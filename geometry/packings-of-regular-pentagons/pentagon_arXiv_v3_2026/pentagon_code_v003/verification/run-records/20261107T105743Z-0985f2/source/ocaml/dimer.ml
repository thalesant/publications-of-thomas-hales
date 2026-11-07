(* COMPUTATION LZMJIZU: mathematical claim and job selection in docs/CALCULATIONS.md. *)
(* Dimer reductions, neighborhood exclusions and squeezing.
   Public geometric documentation: docs/code_commentary.tex. No handwritten
   notes are needed to run or interpret the declared jobs.
   run_group1--run_group4 retain their original calculation bodies and flags.
   squeeze_calc is a proof job. one127/run_group5 retain optional historical
   diagnostics; they are not required by the current manuscript.
   Loading this module does not run any of these searches. *)

reneeds "pent.ml";;
reneeds "pet.ml";;

module Dimer = struct

open Pent;;

open Pet;;

open Banana;;

(* Long-isosceles terminal exclusions. True means the parameter box cannot be a retained subcritical terminal configuration; otherwise the recursive verifier subdivides. *)
let one_iso2C xs =
  let dACrange = merge_I (172//100) (179//100)                    in
  try
    match  mk2C dACrange xs with
    | None -> true
    | Some (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),
	    (dAC,thACB,thCAB,arcB)) ->
      (let th = Pet.periodize_pent thABC in
       (a >> aK ) || disjoint_I dAB dAC ||
	 forall (fun t -> t >> zero) th)
  with Unstable -> false;;

let one_iso2C' xs =
  let dACrange = merge_I (two*kappa) (179//100)              in
  try
    match  mk2C dACrange xs with
    | None -> true
    | Some (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),
	    (dAC,thACB,thCAB,arcB)) ->
       (a >> aK) || disjoint_I dBC dAB || dAC >> dAB
  with Unstable -> false;;

let pint_outdomfn (a,alpha,beta,xa,xb,xc,dBC,dAC,dAB) =
  (dAC << 172 // 100) &&
    (xb >>= 9 // 10) &&
    (beta >>= 12 // 10) &&
    (dBC >> dAB && dBC >> dAC);;

let one_pintx xs =
  try
  let ([alpha;beta;xa],_) = xs in
  if outdomfn_pint alpha beta then true
      else
      let (dBC,dAC,dAB,xc,xb)= pintedge_extended alpha beta xa in
      let a = areamin_acute dBC dAC dAB in
      let inadmissible xc a = xc >> two*sigma || (a >> aK+epsN_I) in
      inadmissible xc a ||
	pint_outdomfn (a,alpha,beta,xa,xb,xc,dBC,dAC,dAB)
  with Unstable -> false;;

let one_pinwheelx xs =
  try
  let ([alpha;beta;xc],_) = xs in
  if alpha+beta >> pi15 then true
      else
      let (d1,d2,d3)= pinwheeledge alpha beta xc in
      let a = areamin_acute d1 d2 d3 in
      let inadmissible = (a >> aK+epsN_I) in
      let one_pinwheelx_constant = 8 // 10 in
      let outdom = (xc << one_pinwheelx_constant) in
      inadmissible || outdom
  with Unstable -> false;;

let one_ljx xs =
  try
    let ([alpha;beta;xa],_) = xs in
    if outdomfn_lj alpha beta then true
    else
      let (d1,d2,d3)= ljedge alpha beta xa in
      let a = areamin_acute d1 d2 d3 in
      let inadmissible = (a >> aK+epsN_I) in
      let one_ljx_constant = 9//10 in
      let outdom = (beta << one_ljx_constant) in
      inadmissible || outdom
  with Unstable -> false;;

let one_tjx xs =
  try
    let ([alpha;beta;xc],_) = xs in
    if outdomfn_tj alpha beta then true
    else
      let (d1,d2,d3)= tjedge alpha beta xc in
      let a = areamin_acute d1 d2 d3 in
      let inadmissible = (a >> aK+epsN_I) in
      let one_tjx_constant = one in
      let outdom = (beta >>  one_tjx_constant) in
      inadmissible || outdom
  with Unstable -> false;;

let domain_iso2C =
  let zpi25 = zero2 (ratpi 2 5) in
  let z2sig = zero2 (two*sigma) in
  let r_slider = [z2sig;zero;z2sig;zpi25] in
  let r_midpointer = [sigma;zpi25;z2sig;zpi25] in
  let b = [(false,true);(false,false)] in
  let f r = map (fun t -> (r,t)) b in
  f r_slider @ f r_midpointer;;

let domain_iso2C' =
  let zpi25 = zero2 (ratpi 2 5) in
  let zpi5 = zero2 (ratpi 1 5) in
  let z2sig = zero2 (two*sigma) in
  let r_slider = [z2sig;zpi25;z2sig;zero] in
  let r_midpointer = [z2sig;zpi25;sigma;zpi5] in
  let b = [(false,true);(true,true)] in
  let f r = map (fun t -> (r,t)) b in
  f r_slider @ f r_midpointer;;

let dummybool = (map (fun t->(t,(true,true))));;

let run_group1() =
  [recursepairtoeps one_iso2C domain_iso2C;
   recursepairtoeps one_iso2C' domain_iso2C';

   recursepairtoeps one_pintx (dummybool pintdomain);
   recursepairtoeps one_pinwheelx (dummybool pinwheeldomain);
   recursepairtoeps one_ljx (dummybool ljdomain);
   recursepairtoeps one_tjx (dummybool tjdomain)
];;

let dimer_outdomfn_null alphaB betaB xbetaB alphaD = false;;

let dimer_outdomfn_eps eps alphaB betaB xbetaB alphaD =
  let nearlyt t x = (x << t + eps) && x >> t - eps in
  nearlyt pi15 betaB &&
    nearlyt sigma xbetaB &&
    nearlyt zero alphaB &&
    nearlyt zero alphaD;;

let ice_ray_nbd = 1 // 100;;

let dimer_outdomfn_01 = dimer_outdomfn_eps ice_ray_nbd;;

(* Glue AC-shared charts by betaD=2*pi/5-betaB and xbetaD=2*sigma-xbetaB. First triangle subcritical, AC longest there. True means an area/domain exclusion or an explicitly supplied alternative. pseudo=true is NOT the same mathematical test as pseudo=false. *)
let one_dimer_eps pseudo eps dimer_outdomfn xs =
  let ([alphaB;betaB;xbetaB;alphaD],
       ((sB,edgeB,disjointB),(sD,edgeD,disjointD))) = xs in
  try

    if disjointB alphaB betaB xbetaB then true
    else
      let (dBC,dAC,dAB) = edgeB alphaB betaB xbetaB in
      let aABC = areamin_acute dBC dAC dAB in
      if aABC >> aK || dAC << dAB || dAC << dBC then true
      else

      let betaD = pi25 - betaB in
      let xbetaD = two*sigma - xbetaB in
      if disjointD alphaD betaD xbetaD then true
      else
	let (dCD,dAC',dAD) = edgeD alphaD betaD xbetaD in
	let aADC = areamin_acute dCD dAC' dAD in
	let pseudodimer = dAD >> dAC' +  3 // 100
	  && dAD >>  18 // 10             in
	aABC + aADC >> two * aK - eps ||
	  (pseudo && pseudodimer) ||
	  dimer_outdomfn alphaB betaB xbetaB alphaD
  with | Unstable -> false;;

let one_dimer = one_dimer_eps false zero;;

(* Stable contact-type order used by every dimer job and its labels: pint,pinw,lj1,lj2,lj3,tj1,tj2,tj3. Do not reorder without regenerating the job registry. *)
let dimer_types = [
  ("pint",shared_pintedge,outdomfn_shared_pint)  ;
  ("pinw",shared_pinwheeledge,outdomfn_shared_pinwheel);
  ("lj1",shared_lj1edge,outdomfn_shared_lj1);
  ("lj2",shared_lj2edge,outdomfn_shared_lj2);
  ("lj3",shared_lj3edge,outdomfn_shared_lj3);
  ("tj1",shared_tj1edge,outdomfn_shared_tj1);
  ("tj2",shared_tj2edge,outdomfn_shared_tj2);
  ("tj3",shared_tj3edge,outdomfn_shared_tj3);];;

let dtype = List.nth dimer_types;;

let dimer_domain (i,j) =
  ((map zero2 [pi25;pi25;two*sigma;pi25]),
  (dtype i,dtype j));;

let dtype_labels xs =
  let (_,((sB,_,_),(sD,_,_))) = xs in
  (sB,sD);;

let recurse_dimer pseudo eps f d =
    try
      let _ = report "..." in
      recurserpair (1.0e-8) 0 (one_dimer_eps pseudo eps f) [d]
    with Failure s ->
      let (sB,sD) = dtype_labels d in
      failwith ("one_dimer("^sB^","^sD^") "^s);;

let recurse0 s = recurse_dimer false zero
  dimer_outdomfn_null (dimer_domain s);;

(* The 48 distinct ordered pairs involving pint,lj3,tj1,tj2, with the 64 original calls (including repeats) retained. No near-ice-ray acceptance branch. *)
let run_group2 () =
  [
    map (fun i -> recurse0 (0,i)) (0--7);
    map (fun i -> recurse0 (i,0)) (0--7);
    map (fun i -> recurse0 (4,i)) (0--7);
    map (fun i -> recurse0 (i,4)) (0--7);
    map (fun i -> recurse0 (5,i)) (0--7);
    map (fun i -> recurse0 (i,5)) (0--7);
    map (fun i -> recurse0 (6,i)) (0--7);
    map (fun i -> recurse0 (i,6)) (0--7)];;

let needsmore = [1;2;3;7];;

let morecases = outer pair needsmore needsmore;;

let recurse_01 pseudo s = recurse_dimer pseudo zero
  dimer_outdomfn_01 (dimer_domain s);;

(* Sixteen remaining ordered pairs. Twelve use pseudo=false; four use pseudo=true. The 0.01-neighborhood alternative is retained exactly. *)
let run_group3() =
  [
    recurse_01 false (1,1);
    recurse_01 false (2,1);
    recurse_01 false (3,1);
    recurse_01 false (7,1);

    recurse_01 false (1,2);
    recurse_01 false (2,2);
    recurse_01 false (3,2);
    recurse_01 false (7,2);

    recurse_01 false (2,3);
    recurse_01 false (7,3);

    recurse_01 false (2,7);
    recurse_01 false (7,7);

    recurse_01 true (1,3);
    recurse_01 true (3,3);
    recurse_01 true (1,7);
    recurse_01 true (3,7)];;

(* The original allowance 0.007 is stronger than the paper's 0.008: the area target is 2*aK minus this allowance. Do not change it merely to make the constants identical. *)
let recurseN s = recurse_dimer false (7//1000)
  dimer_outdomfn_null (dimer_domain s);;

let run_group4() =
  [
    recurseN (1,3);
    recurseN (3,3);
    recurseN (1,7);
    recurseN (3,7);
  ];;

let safetan_I x = if (x.high < 1.57) && (x.low > -. 1.57) then
    tan_I x else raise Unstable;;

(* Contact-line slope after choosing the relevant extended alpha chart. The sign and reciprocal alternatives are geometrically significant; see the outstanding signed-squeeze contract in the audit. *)
let one_sigma arcA thBAC thABC alpha =
  let f0 alpha = safetan_I (-arcA + thBAC + pi310 + (pi25 - alpha)) in
  let f1 alpha = safetan_I (-arcA - thABC + pi310 + alpha) in
  (mergefn f0 f1 merge_I pi25) alpha;;

(* Original three-way squeezing predicate retained. Division/near-vertical tangent instability leads to subdivision. This Boolean is not documented as proving all slopes positive. *)
let squeezable dACrange outofdomfn xs =
  let [xalpha;alpha;xbeta;beta] = xs in
  try
  match mk2Ce dACrange xs with
  | None -> true
  | Some (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),
	  (dAC,thACB,thCAB,arcB)) ->
    (if outofdomfn (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),
	  (dAC,thACB,thCAB,arcB)) then true
     else
	let dAB_sinA =dAB * sin_I (arcA) in
	let sigmaA = one_sigma arcA thBAC thABC alpha in
	let sigmaC = one_sigma arcC thBCA thCBA beta in
	sigmaA << dAB_sinA/dAC ||
	  sigmaC << dAB_sinA/dAC ||
	  (one/sigmaA + one/sigmaC)*dAB_sinA >> dAC)
  with Unstable -> false;;

let domain2Ce =   [map zero2 [two*sigma;pi45;two*sigma;pi45]];;

let squeeze_calc() =
  let top = 232//100 in
  let _ =  kappa*  (sqrt_I(square_I top - square_I(two*kappa))) >>
    (aK+epsN_I) || failwith "232" in
  let dACrange = merge_I (two*kappa) (232//100) in
  let outofdomfn (a,_,_,_) = (a >> aK+epsN_I) in
  recursetoeps (squeezable dACrange outofdomfn) domain2Ce;;

(* Optional historical 1.27 check for the specified isosceles domain. It is retained as a named diagnostic, not asserted to be required by the current paper. *)
let one127 (sgnalpha,sgnbeta) xs  =
  try
    let dACrange = merge_I (172//100) (179//100)                    in
    let v = mk2C dACrange (xs,( sgnalpha, sgnbeta)) in
    if (v = None) then true
    else
      let (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),(dAC,thACB,thCAB,arcB)) = the v in
      (a >> 127 // 100) || disjoint_I dAB dAC ||
	dAC >> dAB
  with Unstable -> false;;

let domain2C =   [map zero2 [two*sigma;ratpi 2 5;two*sigma;ratpi 2 5]];;

let recursesgn f dom =
  map (fun t -> recursetoeps (f t) dom)
    [(true,true);(true,false);(false,true);(false,false)];;

let run_group5() =
  (squeeze_calc(),
  recursesgn one127 domain2C);;

end;;
