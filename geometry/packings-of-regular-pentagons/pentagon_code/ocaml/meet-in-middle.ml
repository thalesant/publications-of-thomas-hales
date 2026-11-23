(* Meet-in-the-middle verification engine.
   Keys deliberately overapproximate compatible shared-edge data. Hash
   collisions add possibilities; they must never remove a feasible gluing.
   Peripheral entries store area LOWER bounds and allowed area UPPER cuts.
   Recut takes a maximum across all possible central matches.
   Success requires exhaustion; width/resource failures are not success.
   Each job runs in its own process; phash is not shared across workers. *)

needs "pent.ml";;
needs "pet.ml";;

module Meet = struct

open Pent;;

let findsome tbl key =
    try
      Some (Hashtbl.find tbl key)
    with Not_found -> None;;

let int_floor x = int_of_float (floor x);;

(* Strict integer ceiling: at an integer n return n+1. This keeps a closed interval's upper endpoint in the same cell as a singleton at that endpoint. *)
let int_ceil x =
  let c = ceil x in
  let i = int_of_float c in
  if (c = x) then succ i else i;;

(* Include every integer cell met by the rescaled closed interval. Shared points therefore yield a common key. Hash collisions in make_keys only enlarge compatibility. *)
let make_a_key width  t =
  let rescale = t/width in
  let im = int_floor (rescale).low in
  let iM = int_ceil (rescale).high in
  (im -- (iM -~ 1));;

let make_keys widths ranges =
  let (r1,r2,r3) = ranges in
  let (w1,w2,w3) = widths in
  let k1 = make_a_key w1 r1 in
  let k2 = make_a_key w2 r2 in
  let k3 = make_a_key w3 r3 in
  map (Hashtbl.hash) (outertriple k1 k2 k3);;

let keys_of_edge width edgedata =
  let (l,t,t') = edgedata in
  let ts = Pet.periodize_pent t in
  let ts' = Pet.periodize_pent t' in
  let triples = outertriple [l] ts ts' in
  let s = two in

  List.flatten (map (make_keys (width,s*width,s*width)) triples);;

(* Adjacent triangles traverse a shared edge in opposite orientations. Negate both signed inclinations; periodic reduction follows in keys_of_edge. *)
let key_invert w (l,t,t') =
  keys_of_edge w (l,-t,-t');;

let key_inverts w eds =
  setify (List.flatten (map (key_invert w) eds));;

let widthlist xs =
  let ws = map (fun x -> x.high -. x.low) xs in
  itlist (fun x y -> max x y) ws 0.0;;

let rec subdivide_subwidth width xs =
  let ns = map (fun t -> int_ceil (width_I t / width).high) xs in
  let one1 (n,x) = let v =  (width_I x /int n) in
		  let z = min_I x + zero2 v in
		  map (fun i -> [z + v * int i]) (0--(n-~ 1)) in
  let prs = map one1 (zip ns xs) in
  end_itlist (fun x y -> outer ( @ ) x y) prs;;

(* Maximum of the allowed upper cuts from all surviving central alternatives. A minimum here would incorrectly remove valid peripheral choices. *)
let maxcut hash keys =
  let cuts = selectsome (map snd (map (Hashtbl.find hash) keys)) in
  if cuts = [] then None
  else
    Some (end_itlist (fun x y -> if x >. y then x else y) cuts);;

(* Minimum lower area bound over compatible keys. Missing entries yield None, never the numerical bound zero. *)
let minarea hash keys =
  let areas = map fst (selectsome (map (findsome hash) keys)) in
  if areas = [] then None
  else
  Some  (min_I(end_itlist (fun x y -> if x.low <. y.low then x else y) areas));;

(* Accumulate the most permissive allowable upper cut across central matches. Existing hash collisions remain conservative. *)
let recut phash cut' key =
    match findsome phash key with
    | None -> ()
    | Some (a,None) -> Hashtbl.add phash key (a,Some cut')
    | Some (a,Some cut) ->
      if cut' >. cut then Hashtbl.replace phash key (a,Some cut');;

(* Subdivide the peripheral box and retain its lower area bound and shared-edge keys. An unresolved chart calculation subdivides again; a certified None or outside-domain result eliminates the box. *)
let mk_one_pericoord initialized width phash fn (pcoord,keys,area) =
  let (extra,fillfn,outdomfn,areafn,keyfn) = fn in
  let maxcut = maxcut phash keys in
  let overweight a = initialized &&

    (match maxcut with | None -> true | Some mx -> (a >>. mx)) in
  let rec makesome pc =
    try
      match (fillfn extra pc) with
      | None -> []
      | Some fill -> (let area' = areafn fill in
		      if (overweight area') || outdomfn fill then []
		      else let keys' = keyfn width fill in
			   [(pc,keys',min_I area')])
    with Unstable -> (let (pc1,pc2) = splitlist (1.0e-4) pc in
		      makesome pc1 @ makesome pc2) in
  if overweight area then []
  else
    let pcs = subdivide_subwidth width pcoord in
     (List.flatten (map makesome pcs));;

let update_one_perihash phash (pcoord,keys,area) =
  let area = min_I area in
  let one_key k = match findsome phash k with
    | None -> Hashtbl.add phash k (area,None)
    | Some (ak,_) -> if area.low <. ak.low then Hashtbl.replace phash k (area,None) in
  let _ = map one_key keys in
  ();;

let mk_peridata initialized width (phash,(pfn,ps)) =
  let ps' = List.flatten (map (mk_one_pericoord initialized width phash pfn) ps) in
  let _ = Hashtbl.clear phash in
  let _ = map (update_one_perihash phash) ps' in
  (phash,(pfn,ps'));;

let periareas width some_phash keyfns fill =
  if isnone(some_phash) then Some([],zero,[])
  else
    let phash = the some_phash in
    let keys' = map (fun f -> f width fill) keyfns in
    let someperiareas = map (fun keys -> minarea phash keys) keys' in
    if exists ((=) None) someperiareas then None
    else
      let periareas = map the someperiareas in
      let total_periarea = min_I (itlist ( + ) periareas zero) in
      Some (periareas,total_periarea,keys');;

(* Add the central area lower bound and minimum compatible peripheral bounds. Reject only when the strict total lower bound exceeds the target. Otherwise propagate conservative upper cuts to all compatible peripheral keys. *)
let  mk_one_cencoord width cluster_areacut some_phash fn (ccoord,cencut) =
  let (extra,fillfn,outdomfn,areafn,keyfns) = fn in
  let _ = ((keyfns = [])=(isnone(some_phash))) ||
    failwith "number of peripherals" in
  let perirecut gap some_phash (keys,periarea0) =
    map (recut (the some_phash) ((periarea0-gap).high)) keys in
  let rec makesome cc =
    try
      match (fillfn extra cc) with
      | None -> []
      | Some fill ->
	(let cenarea = min_I (areafn fill) in
	 if (cenarea >>. cencut) || outdomfn fill then []
	 else
	   match periareas width some_phash keyfns fill with
	   | None -> []
	   | Some (periareas,total_periarea,keys') ->
	     (let clustarea = cenarea + total_periarea in
	      let gap = clustarea - cluster_areacut in
	      if gap >> zero then []
	      else

		let _ = map (perirecut gap some_phash) (zip keys' periareas) in
		let cencut' = (cluster_areacut - total_periarea).high in
		let cencut' = min cencut' cencut in
		[(cc,cencut')]))
    with Unstable ->
      let (cc1,cc2) = splitlist (1.0e-4) cc in
      makesome cc1 @ makesome cc2 in
  let ccs = subdivide_subwidth width ccoord in
  List.flatten (map makesome ccs);;

let mk_cencoord width cluster_areacut some_phash cfn ccs =
  List.flatten (map (mk_one_cencoord width cluster_areacut some_phash cfn) ccs);;

let report_stats(i,width,pdata,ccs) =
  let s1 = Printf.sprintf "i=%d, w=%3.5f, length(ccs)=%d"
    i (width.low) (List.length ccs) in
  let _ = report s1 in
  let ls =  (function |None->0 | Some(_,(_,t)) -> List.length t) pdata in
  let ks,kplus,ph = match pdata with
    |None -> (0,0,0)
    |Some(ph,(_,ps)) ->
      let keyss = map (fun (_,k,_)-> List.length k) ps in
      (itlist (fun x y -> max x y) keyss 0,
       end_itlist ( +~) keyss,
       Hashtbl.length ph) in
  let _ = report (Printf.sprintf " length(ps)=%d maxkey=%d keysum=%d phash=%d" ls ks kplus ph) in
  ();;

(* Refine both sides and rebuild matching data at half the key width. Return true only when a required peripheral or the central list is empty. Width exhaustion raises Failure, never true. *)
let rec mitm_recursion i initialized cluster_areacut width some_pdata cfn ccs =
  let _ = width >> (m (1.0e-6)) || failwith "I'm giving up at small width" in
  let some_pdata',some_phash,empty = match some_pdata with
    | None -> (None,None,false)
    | Some pdata ->
      let pdata' = mk_peridata initialized width pdata in
      let phash = fst pdata in
      (Some pdata',Some phash,(snd (snd pdata')=[])) in
  if empty then true
  else
    let ccs = mk_cencoord width cluster_areacut some_phash cfn ccs in
    if ccs = [] then true
    else
      let _ = report_stats (i,width,some_pdata',ccs) in
      mitm_recursion (succ i) true cluster_areacut (width/two) some_pdata' cfn ccs;;

let mk_hashtbl() =
  let tbl = Hashtbl.create 100000 in
  let _ = Hashtbl.clear tbl in
  tbl;;

let phash = mk_hashtbl();;

end;;
