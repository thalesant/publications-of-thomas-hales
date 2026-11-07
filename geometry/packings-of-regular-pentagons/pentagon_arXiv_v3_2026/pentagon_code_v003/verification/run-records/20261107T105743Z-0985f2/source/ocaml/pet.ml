(* Pair nonoverlap filter, in the paper's inclination-angle convention.
   pet l theta theta' = false certifies that no nonoverlapping pair is
   represented. True permits a pair but need not prove existence. Distances
   and both angles are intervals; modular branches are retained as a union.
   See docs/code_commentary.tex and tests/ocaml/geometry_tests.ml. *)

open Pent;;

module Pet = struct

(* Cover all representatives modulo one by closed subintervals of [0,1]. A full-period input returns the entire period. Duplicate endpoints are conservative. *)
let periodize1 ix =
  if (ix.high  >= 1.0 +. ix.low) then [mk_interval(0.0,1.0)]
  else
    let iy = ix - m (floor ix.low) in
      if iy.high <= 1.0 then [iy] else
	[mk_interval (iy.low,1.0);mk_interval(0.0,iy.high -. 1.0)];;

let periodize ix r =
  let eps = m (1.0e-8) in
  let _ = r >> eps || failwith "underflow periodize" in
    map (( * ) r) (periodize1 (ix / r));;

let periodize_min ix r a =
  let iy = ix -  a in
    map (( + ) ( a)) (periodize iy r);;

let xi2 = m 0.2;;

let xi1 = m 0.1;;

let periodize_pent ix =
  periodize_min ix (pi25) (- pi15);;

let periodize_pent0 ix =
  periodize_min ix pi25 zero;;

let ilawbeta alpha a b =
  asin_I (b * sin_I alpha / a);;

(* A conservative existence test for equal-sign inclinations after reordering absolute angles. True means NOT excluded, rather than a certified nonoverlap witness. *)
let case_pet_pos l (itheta',iabstheta) =
  let abstheta = max_I iabstheta in
  let locx th = iloc l one th in
  let beta th = ilawbeta th (locx th) one in
  let r th = kappa / cos_I (beta th + pi15 - abstheta) in
  let f th = (locx th).high >= (r th).low in

    f (min_I itheta') || f (max_I itheta');;

(* Opposite-sign branch. Restrict the reordered angle range and retain the possible stationary direction as well as endpoints. *)
let case_pet_neg l (itheta',iabstheta) =
  let theta' = max_I itheta' in
  let iabstheta = inter_I iabstheta (mk (theta'.high) (iabstheta.high)) in
  let locx = iloc l one theta' in
  let beta = ilawbeta theta' locx one in
  let target = pi15 - beta in
  let abstheta =
    if iabstheta >> target then min_I iabstheta
    else if iabstheta << target then max_I iabstheta
    else target in
  let r = kappa / cos_I (pi15 - (beta + abstheta)) in
    locx.high >= r.low;;

let pet0 l (itheta', iabstheta,samesign) =
  let locx = iloc one l (max_I itheta') in
    if locx.high >= one.low then true
    else if locx <<  kappa then false
    else if not(samesign) then case_pet_neg l (itheta',iabstheta)
    else case_pet_pos l (itheta',iabstheta);;

let splitat0 itheta =
  if (itheta >>= zero) then [(itheta,true)]
  else if (itheta <<= zero) then [(-itheta,false)]
  else [mk_interval(0.0,itheta.high),true;
	mk_interval(0.0, -. itheta.low),false];;

let resize(t1,t2,samesign) =
  let t = mk (t1.low) (t2.high) in
  let t1 = inter_I t1 t in
  let t2 = inter_I t2 t in
  (t1,t2,samesign);;

let reorder (th1,b1) (th2,b2) =
  let samesign = (b1=b2) in
  if (th1 << th2) then [(th1,th2,samesign)]
  else if (th2 << th1) then [(th2,th1,samesign)]
  else [resize(th1,th2,samesign);resize(th2,th1,samesign)];;

(* Pair feasibility over an interval box. False must exclude every nonoverlapping pair represented by the box. Period/sign/exchange cases are combined by existential OR; uncertain arithmetic propagates. *)
let pet il itheta itheta' =
  let split i = List.flatten (map splitat0  (periodize_pent i)) in
  let ithetas = split itheta in
  let ithetas' = split itheta' in
  let cases = List.flatten (Lib.allpairs reorder ithetas ithetas') in
  exists (pet0 (max_I il)) cases;;

end;;
