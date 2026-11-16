(* Named finite-cluster verification problems.
   Each job retains the paper target and explicitly describes its terminal
   contact domain. True from time_mitm certifies exhaustion of that encoded
   domain, conditional on the geometric enclosure contracts.
   The exceptional-peripheral cap follows the pair-area subtraction. Retain all length-boundary
   alternatives in the two pseudo2 branches. Old runs do not certify these
   enlarged domains. See docs/NEW_TESTS.md and provenance/changes.diff.
   Native function names and seven-letter IDs are retained for navigation. *)

open Meet;;

open Banana;;

let time_mitm cluster_areacut pdata cfn ccs =
  let i = 0 in
  let width = 1//2 in
  let initialized = false in
  time (mitm_recursion i initialized cluster_areacut width pdata cfn) ccs;;

let unit_extra = ();;

let coord5 (dAB,dBC,dAC) =
  let z2pi25 = zero2 pi25 in
  [dAB;z2pi25;z2pi25;dBC;dAC];;

let coord6 (dAB,dBC,dAC) =
  let z2pi25 = zero2 pi25 in
  [dAB;z2pi25;z2pi25;dBC;z2pi25;dAC];;

let coord2Ce =
  let xalpha = zero2 (two*sigma) in
  let alpha = (zero2 pi45) in
    [xalpha;alpha;xalpha;alpha];;

let fillfn5 _ [dAB;thABC;thBAC;dBC;dAC] =
  fillout5D ((dAB,thABC,thBAC),dBC,dAC);;

let fillfn6 _ [dAB;thABC;thBAC;dBC;thCBA;dAC] =
  fillout6D ((dAB,thABC,thBAC),(dBC,thCBA),dAC);;

let areafn5 (a,_) = a;;

let areafn2Ce (a,_,_,_) = a;;

let forall_dom f (a,dds) =
  forall f (map (fun (t1,t2,t3) -> (a,t1,t2,t3)) dds);;

let forall_alpha0 f t =
  let ts = Pet.periodize_pent0 t in
  forall f ts;;

let forall_alpha f t =
  let ts = Pet.periodize_pent t in
  forall f ts;;

let forall_alpha_pair f (t,t') =
    let s = Pet.periodize_pent t in
    let s'= Pet.periodize_pent t' in
    forall f (outer pair s s');;

let forall_alpha_constraint_pseudo_dimer (th,th') =
  forall_alpha0 (fun alpha -> alpha >>pi15) (th+th');;

let d_subcrit_shared =
  let _ = area_I (two*kappa) (two*kappa) (21//10) >> aK || failwith "21" in
  merge_I (172//100) (21//10);;

let d_subcrit_contact =
  merge_I (172//100) two;;

let d_shared_pseudo = merge_I (172//100) (18//10);;

let d_egress =
  let _ = area_I (172//100) (two*kappa) (204//100) >> aK + epsN_I ||
      failwith "204" in
  merge_I (18//10) (204//100);;

let d_third_pseudo = merge_I (two*kappa) (18//10);;

let edge5D_ABs (_,fs) = map (fun ((l,t,t',_),_,_)-> (l,t,t')) fs;;

let edge5D_BCs (_,fs) = map (fun (_,(l,t,t',_),_)-> (l,t,t')) fs;;

let edge5D_ACs (_,fs) = map (fun (_,_,(l,t,t',_))-> (l,t,t')) fs;;

let ckeyfnBC w fs = key_inverts w (edge5D_BCs fs);;

let ckeyfnAC w fs = key_inverts w (edge5D_ACs fs);;

let ckeyfnAB w fs = key_inverts w (edge5D_ABs fs);;

let ckeyfn2Ce w (_,_,_,(dAC,thACB,thCAB,_)) =
  key_invert w (dAC,thACB,thCAB);;

let ckeyfn6AB w (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),(dAC,thACB,thCAB,arcB)) = key_invert w (dAB,thABC,thBAC);;

let ckeyfn6BC w (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),(dAC,thACB,thCAB,arcB)) = key_invert w (dBC,thCBA,thBCA);;

let ckeyfn6AC w (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),(dAC,thACB,thCAB,arcB)) = key_invert w (dAC,thACB,thCAB);;

let init2Cps =
  let fillfn () = mk2Ce d_subcrit_shared in
  let outdomfn (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),(dAC,thACB,thCAB,arcB)) =
    (dAB >> dAC || dBC >> dAC || a >> aK) in
  let keyfn w (_,_,_,(dAC,thACB,thCAB,_)) = keys_of_edge w (dAC,thACB,thCAB) in
  let fn = (unit_extra,fillfn,outdomfn,areafn2Ce,keyfn) in
  let keys = [] in
  let area = amin in
  (fn,[(coord2Ce,keys,area)]);;

let init2Cps_isosceles_AB_AC =
  let (fn,ps) = init2Cps in
  let (extra,fillfn,outdomfn,areafn,keyfn) = fn in
  let outdomfn' (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),
		 (dAC,thACB,thCAB,arcB)) =
    (disjoint_I dAB dAC || dBC >> dAC || a >> aK) in
  let fn = (extra,fillfn,outdomfn',areafn,keyfn) in
  (fn,ps);;

let init2Cps_isosceles_BC_AC =
  let (fn,ps) = init2Cps in
  let (extra,fillfn,outdomfn,areafn,keyfn) = fn in
  let outdomfn' (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),
		 (dAC,thACB,thCAB,arcB)) =
    (disjoint_I dBC dAC || dAB >> dAC || a >> aK) in
  let fn = (extra,fillfn,outdomfn',areafn,keyfn) in
  (fn,ps);;

let init2Cps_isosceles_AC =
  let (fn,ps) = init2Cps in
  let (extra,fillfn,outdomfn,areafn,keyfn) = fn in
  let outdomfn' (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),
		 (dAC,thACB,thCAB,arcB)) =
    (a >> aK || (disjoint_I dBC dAC && disjoint_I dAB dAC)) in
  let fn = (extra,fillfn,outdomfn',areafn,keyfn) in
  (fn,ps);;

let reset_peri ps =
  let _ = Hashtbl.reset phash in
  Some(phash,ps);;

(* diagnostic:central -- Existing central-chart diagnostic (1.2 debug cutoff, not 1.237).
   Execute via run.py; module loading does not run this calculation. *)
let test1_centralpent_1237() =
  let cluster_areacut = (m 1.2            ) in
  let pdata = None in
  let cencut = cluster_areacut.high in
  let outdomfn _ = false in
  let keyfns = [] in
  let k2 = merge_I (two*kappa) in
  let dAB_dBC_dAC = (k2(21//10),k2(21//10),k2(two)) in
  let cfn = (unit_extra,fillfn5,outdomfn,areafn5,keyfns) in
  let ccs = [(coord5(dAB_dBC_dAC),cencut);] in
  time_mitm cluster_areacut pdata cfn ccs;;

(* diagnostic:central -- Existing central-chart diagnostic (1.72 cutoff).
   Execute via run.py; module loading does not run this calculation. *)
let test1_centralpent_172() =
  let cluster_areacut = aK in
  let pdata = None in
  let cencut = cluster_areacut.high in
  let outdomfn _ = false in
  let keyfns = [] in
  let k2 = merge_I (two*kappa) (172//100) in
  let dAB_dBC_dAC = (k2,k2,k2) in
  let cfn = (unit_extra,fillfn5,outdomfn,areafn5,keyfns) in
  let ccs = [(coord5(dAB_dBC_dAC),cencut);] in
  time_mitm cluster_areacut pdata cfn ccs;;

(* Lemma 5.12 [calc:pent4]; source code QPJDYDB.
   Four-triangle bound 4 a_crit: six-dimensional central chart and three subcritical outside-double-contact peripherals.
   Each terminal predicate excludes only a whole box or supplies a lower bound.
   Run with: python3 run.py --job mitm_calc_pent4_6D_postcluster *)
let calc_pent4_6D_postcluster() =
  let cluster_areacut = four*aK in
  let pdata = reset_peri init2Cps in

  let outdomfn (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),(dAC,thACB,thCAB,arcB)) =
    (dAB << dBC || dAB << dAC || dBC << dAC) in
  let keyfns = [ckeyfn6AB;ckeyfn6BC;ckeyfn6AC] in
  let cfn = (unit_extra,fillfn6,outdomfn,areafn2Ce,keyfns) in
  let dAB_dBC_dAC = (d_subcrit_shared,d_subcrit_shared,d_subcrit_shared) in
  let cencut = (aK + int 3*epsN_I).high in
  let ccs = [(coord6 dAB_dBC_dAC,cencut);] in
  let _ = report "pent4_6D_postcluster_experimental" in
  time_mitm cluster_areacut pdata cfn ccs;;

(* Lemma 5.11 [calc:pent3]; source code HUQEJAT.
   Three-triangle bound 3 a_crit + epsilon_M: unrestricted six-dimensional central chart and two long-isosceles peripherals.
   Each terminal predicate excludes only a whole box or supplies a lower bound.
   Run with: python3 run.py --job mitm_calc_pent3_6D_postcluster *)
let calc_pent3_6D_postcluster() =
  let cluster_areacut = int 3*aK + epsM_I in

  let pdata = reset_peri init2Cps_isosceles_AC in

  let outdomfn (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),_) =
    (dAB << dBC) in
  let keyfns = [ckeyfn6AB;ckeyfn6BC] in
  let cfn = (unit_extra,fillfn6,outdomfn,areafn2Ce,keyfns) in
  let d_subcrit_isosc = merge_I (172//100) (179//100) in
  let d_short = merge_I (two*kappa) (202//100) in
  let dAB_dBC_dAC = (d_subcrit_shared,d_subcrit_shared,d_short) in
  let cencut = (aK + two*epsN_I + epsM_I).high in
  let ccs = [(coord6 dAB_dBC_dAC,cencut);] in
  let _ = report "pent3_6D_postcluster" in
  time_mitm cluster_areacut pdata cfn ccs;;

(* Lemma 5.11 [calc:pent3]; source code HUQEJAT.
   Three-triangle bound 3 a_crit + epsilon_M: contact-central chart with peripherals on BC and AC; AB is unshared.
   Each terminal predicate excludes only a whole box or supplies a lower bound.
   Run with: python3 run.py --job mitm_calc_pent3AB_postcluster *)
let calc_pent3AB_postcluster() =
  let cluster_areacut = int 3*aK + epsM_I in
  let pdata = reset_peri init2Cps in
  let outdomfn _ = false in
  let keyfns = [ckeyfnBC; ckeyfnAC] in
  let cfn = (unit_extra,fillfn5,outdomfn,areafn5,keyfns) in
  let _ = area_I (172//100) (172//100) (202//100) >>
    (aK + two * epsN_I + epsM_I) || failwith "202" in
  let d_short = merge_I (two*kappa) (202//100) in

  let dAB_dBC_dAC = (d_short,d_subcrit_shared,d_subcrit_contact) in
  let cencut = (aK + two*epsN_I + epsM_I).high in
  let ccs = [(coord5 dAB_dBC_dAC,cencut);] in
  let _ = report("pent3AB") in
  time_mitm cluster_areacut pdata cfn ccs;;

(* Lemma 5.11 [calc:pent3]; source code HUQEJAT.
   Three-triangle bound 3 a_crit + epsilon_M: contact-central chart with peripherals on AB and AC; BC is unshared.
   Each terminal predicate excludes only a whole box or supplies a lower bound.
   Run with: python3 run.py --job mitm_calc_pent3BC_postcluster *)
let calc_pent3BC_postcluster() =
  let cluster_areacut = int 3*aK + epsM_I in
  let pdata = reset_peri init2Cps in
  let outdomfn _ = false in
  let keyfns = [ckeyfnAB;ckeyfnAC] in
  let cfn = (unit_extra,fillfn5,outdomfn,areafn5,keyfns) in
  let d_short = merge_I (two*kappa) (202//100) in
  let dAB_dBC_dAC=(d_subcrit_shared,d_short,d_subcrit_contact) in
  let cencut = (aK + int 2*epsN_I +epsM_I).high in
  let ccs = [(coord5 dAB_dBC_dAC,cencut);] in
  let _ = report("pent3BC") in
  time_mitm cluster_areacut pdata cfn ccs;;

(* Lemma 5.11 [calc:pent3]; source code HUQEJAT.
   Three-triangle bound 3 a_crit + epsilon_M: contact-central chart with peripherals on AB and BC; AC is unshared.
   Each terminal predicate excludes only a whole box or supplies a lower bound.
   Run with: python3 run.py --job mitm_calc_pent3AC_postcluster *)
let calc_pent3AC_postcluster() =
  let cluster_areacut = int 3*aK +epsM_I in
  let pdata = reset_peri init2Cps in
  let outdomfn _ = false in
  let keyfns = [ckeyfnAB; ckeyfnBC] in
  let cfn = (unit_extra,fillfn5,outdomfn,areafn5,keyfns) in
  let d_short = merge_I (two*kappa) (202//100) in

  let dAB_dBC_dAC=(d_subcrit_shared,d_subcrit_shared,d_short) in
  let cencut = (aK + int 2*epsN_I + epsM_I).high in
  let ccs = [(coord5 dAB_dBC_dAC,cencut);] in
  let _ = report("pent3AC") in
  time_mitm cluster_areacut pdata cfn ccs;;

(* Lemma 5.14 [calc:large]; source code FHBGHHY.
   Non-large-angle pair bound 2 a_crit + epsilon_M: outside-double-contact central triangle.
   Each terminal predicate excludes only a whole box or supplies a lower bound.
   Run with: python3 run.py --job mitm_calc_pent2_postcluster_case0 *)
let calc_pent2_postcluster_case0() =
  let cluster_areacut = two*aK + epsM_I in
  let pdata = reset_peri init2Cps in

  let range = merge_I (172//100) (193//100) in
  let fillfn () = mk2Ce range in
  let outdomfn (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),(dAC,thACB,thCAB,arcB)) =
    (dAB << 18//10 || dBC >> 179//100 || disjoint_I dAC range ||
       forall_alpha_constraint_pseudo_dimer (thABC,thBAC)) in

  let keyfns = [ckeyfn2Ce] in
  let cfn = (unit_extra,fillfn,outdomfn,areafn2Ce,keyfns) in

  let cencut = (aK + epsN_I + epsM_I).high in
  let assertAC = area_I (193//100) (18//10) (two*kappa) >>. cencut ||
    failwith "please reset 1.93 bound and rerun" in
  let assertBC = area_I (18//10) (172//100) (179//100) >>. cencut ||
    failwith "please reset 1.79 bound and rerun" in
  let ccs = [(coord2Ce,cencut);] in
  let _ = report "pent2_case0 covers 2C+2C situation" in
  time_mitm cluster_areacut pdata cfn ccs;;

(* Lemma 5.14 [calc:large]; source code FHBGHHY.
   Non-large-angle pair bound 2 a_crit + epsilon_M: shared edge AB, distinguished nonshared edge AC at length 1.8, with central contact.
   Each terminal predicate excludes only a whole box or supplies a lower bound.
   Run with: python3 run.py --job mitm_calc_pent2_postcluster_case1 *)
let calc_pent2_postcluster_case1() =
  let cluster_areacut = two*aK + epsM_I in
  let pdata = reset_peri init2Cps in
  let outdomfn (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),
		(dAC,thACB,thCAB,arcB)) =
       forall_alpha_constraint_pseudo_dimer (thACB,thCAB) in

  let keyfns = [ckeyfnAB] in
  let cfn = (unit_extra,fillfn5,forall_dom outdomfn,areafn5,keyfns) in
  let d_18 = (18//10) in
  let dAB_dBC_dAC=(d_subcrit_shared,d_third_pseudo,d_18) in
  let cencut = (aK + epsN_I + epsM_I).high in
  let ccs = [(coord5 dAB_dBC_dAC,cencut);] in
  let _ = report("pent2_postcluster_case1:AB shared, AC egressive. ") in
  time_mitm cluster_areacut pdata cfn ccs;;

(* Lemma 5.14 [calc:large]; source code FHBGHHY.
   Non-large-angle pair bound 2 a_crit + epsilon_M: shared edge AB, distinguished nonshared edge BC at length 1.8, with central contact.
   Each terminal predicate excludes only a whole box or supplies a lower bound.
   Run with: python3 run.py --job mitm_calc_pent2_postcluster_case2 *)
let calc_pent2_postcluster_case2() =
  let cluster_areacut = two*aK + epsM_I in
  let pdata = reset_peri init2Cps in
  let outdomfn (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),
	       (dAC,thACB,thCAB,arcB)) =
    forall_alpha_constraint_pseudo_dimer (thBCA,thCBA) in

  let keyfns = [ckeyfnAB] in
  let cfn = (unit_extra,fillfn5,forall_dom outdomfn,areafn5,keyfns) in
  let d_18 = (18//10) in
  let d_contact = merge_I (two*kappa) two in
  let dAB_dBC_dAC=(d_subcrit_shared,d_18,d_contact) in
  let cencut = (aK + epsN_I + epsM_I).high in
  let ccs = [(coord5 dAB_dBC_dAC,cencut);] in
  let _ = report("pent2_postcluster_case2:AB shared, BC egressive. ") in
  time_mitm cluster_areacut pdata cfn ccs;;

(* Lemma 5.14 [calc:large]; source code FHBGHHY.
   Non-large-angle pair bound 2 a_crit + epsilon_M: shared edge BC, distinguished nonshared edge AC at length 1.8, with central contact.
   Each terminal predicate excludes only a whole box or supplies a lower bound.
   Run with: python3 run.py --job mitm_calc_pent2_postcluster_case3 *)
let calc_pent2_postcluster_case3() =
  let cluster_areacut = two*aK + epsM_I in
  let pdata = reset_peri init2Cps in
  let outdomfn (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),
	       (dAC,thACB,thCAB,arcB)) =
    forall_alpha_constraint_pseudo_dimer (thACB,thCAB) in
  let keyfns = [ckeyfnBC] in
  let cfn = (unit_extra,fillfn5,forall_dom outdomfn,areafn5,keyfns) in
  let d_18 = (18//10) in
  let dAB_dBC_dAC = (d_third_pseudo,d_subcrit_shared,d_18) in
  let cencut = (aK + epsN_I + epsM_I).high in
  let ccs = [(coord5 dAB_dBC_dAC,cencut);] in
  let _ = report("pent2_postcluster_case3:BC shared, AC egressive. ") in
  time_mitm cluster_areacut pdata cfn ccs;;

(* Lemma 5.14 [calc:large]; source code FHBGHHY.
   Non-large-angle pair bound 2 a_crit + epsilon_M: shared edge BC, distinguished nonshared edge AB at length 1.8, with central contact.
   Each terminal predicate excludes only a whole box or supplies a lower bound.
   Run with: python3 run.py --job mitm_calc_pent2_postcluster_case4 *)
let calc_pent2_postcluster_case4() =
  let cluster_areacut = two*aK + epsM_I in
  let pdata = reset_peri init2Cps in
  let outdomfn (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),
	       (dAC,thACB,thCAB,arcB)) =
    forall_alpha_constraint_pseudo_dimer (thABC,thBAC) in
  let keyfns = [ckeyfnBC] in
  let cfn = (unit_extra,fillfn5,forall_dom outdomfn,areafn5,keyfns) in
  let d_18 = (18//10) in
  let d_contact = merge_I (two*kappa) two in
  let dAB_dBC_dAC = (d_18,d_subcrit_shared,d_contact) in
  let cencut = (aK + epsN_I + epsM_I).high in
  let ccs = [(coord5 dAB_dBC_dAC,cencut);] in
  let _ = report("pent2_postcluster_case4:BC shared, AB egressive. ") in
  time_mitm cluster_areacut pdata cfn ccs;;

(* Lemma 5.1 [calc:pseudo1]; source code NKQNXUN.
   Shared-edge bound: outside-double-contact central triangle, total cutoff 2 a_crit.
   Each terminal predicate excludes only a whole box or supplies a lower bound.
   Run with: python3 run.py --job mitm_precluster1_case0 *)
let precluster1_case0() =
  let cluster_areacut = two*aK in
  let pdata = reset_peri init2Cps in

  let range = merge_I (18//10) (192//100) in
  let fillfn () = mk2Ce range in
  let outdomfn (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),(dAC,thACB,thCAB,arcB)) =
    (disjoint_I dAC range || disjoint_I dAB range || disjoint_I dBC (merge_I (two*kappa) (17//10))) in
  let keyfns = [ckeyfn2Ce] in
  let cfn = (unit_extra,fillfn,outdomfn,areafn2Ce,keyfns) in

  let cencut = (aK + epsN_I).high in
  let ccs = [(coord2Ce,cencut);] in
  let _ = area_I (18//10) (192//100) (two*kappa) >> aK+epsN_I ||
    failwith "range_check" in
  let _ = area_I (18//10) (18//10) (17//10) >> aK+epsN_I ||
    failwith "range_check" in
  let _ = report "precluster1_case0" in
  time_mitm cluster_areacut pdata cfn ccs;;

(* Lemma 5.1 [calc:pseudo1]; source code NKQNXUN.
   Shared-edge bound: midpoint contact at the nonshared length-1.8 endpoint, total cutoff 2 a_crit.
   Each terminal predicate excludes only a whole box or supplies a lower bound.
   Run with: python3 run.py --job mitm_precluster1_case1 *)
let precluster1_case1() =
  let cluster_areacut = two*aK in
  let pdata = reset_peri init2Cps in

  let theta' = iarc one (18//10) kappa in
  let out_of_theta' t =
    forall_alpha (fun t -> disjoint_I theta' (abs_I t)) t in
  let outdomfn (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),
	       (dAC,thACB,thCAB,arcB)) = out_of_theta' thACB in

  let keyfns = [ckeyfnAB] in
  let cfn = (unit_extra,fillfn5,forall_dom outdomfn,areafn5,keyfns) in

  let d_18 = (18//10) in
  let d_shared = merge_I (18//10) (192//100) in
  let d_short = merge_I (two*kappa) (17//10) in
  let dAB_dBC_dAC = (d_shared,d_short,d_18) in
  let cencut = (aK + epsN_I).high in
  let ccs = [(coord5 dAB_dBC_dAC,cencut);] in
  let _ = report("precluster1 case1 midpointer") in
  time_mitm cluster_areacut pdata cfn ccs;;

(* Lemma 5.1 [calc:pseudo1]; source code NKQNXUN.
   Shared-edge bound: slider contact with either nonshared length 1.8, total cutoff 2 a_crit.
   Each terminal predicate excludes only a whole box or supplies a lower bound.
   Run with: python3 run.py --job mitm_precluster1_case2 *)
let precluster1_case2() =
  let cluster_areacut = two*aK in
  let pdata = reset_peri init2Cps in

  let notslider1 (t, t') = disjoint_I zero (t+t') in
  let notslider (t, t') =
    forall_alpha_pair notslider1 (t,t') in
  let outdomfn (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),
	       (dAC,thACB,thCAB,arcB)) =
    (disjoint_I dAC (18//10) && disjoint_I dBC (18//10) ||
       notslider (thACB,thCAB)) in

  let keyfns = [ckeyfnAB] in
  let cfn = (unit_extra,fillfn5,forall_dom outdomfn,areafn5,keyfns) in

  let d_shared = merge_I (18//10) (192//100) in
  let d_full = merge_I (two*kappa) (192//100) in
  let dAB_dBC_dAC = (d_shared,d_full,d_full) in
  let cencut = (aK + epsN_I).high in
  let ccs = [(coord5 dAB_dBC_dAC,cencut);] in
  let _ = report("precluster1 case2 slider") in
  time_mitm cluster_areacut pdata cfn ccs;;

(* Pseudo-dimer terminal boundary: AB is shared, AC is the contact edge,
   and BC is the other nonshared edge.
   Retain three possible length equalities and either nonshared length 1.8.
   This is deliberately a superset of the paper's stopping events. *)
let pseudo2_boundary_excluded dAB dBC dAC =
  disjoint_I dAC dAB &&
  disjoint_I dAC dBC &&
  disjoint_I dAB dBC &&
  disjoint_I dAC (18//10) &&
  disjoint_I dBC (18//10);;

(* Lemma 5.2 [calc:pseudo2]; source code RWWHLQT.
   Egressive-edge bound: outside-double-contact central triangle with sides at most 1.8, total cutoff 2 a_crit.
   Each terminal predicate excludes only a whole box or supplies a lower bound.
   Run with: python3 run.py --job mitm_precluster2_case0 *)
let precluster2_case0() =
  let cluster_areacut = two*aK in
  let pdata = reset_peri init2Cps in

  let fillfn () = mk2Ce d_shared_pseudo in
  let outdomfn (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),
		(dAC,thACB,thCAB,arcB)) =
    (disjoint_I dAC d_shared_pseudo || disjoint_I dAB d_shared_pseudo ||
       disjoint_I dBC d_third_pseudo ||
    dAB << dAC || dAB << dBC) in
  let keyfns = [ckeyfn2Ce] in
  let cfn = (unit_extra,fillfn,outdomfn,areafn2Ce,keyfns) in

  let cencut = (aK + epsN_I).high in
  let ccs = [(coord2Ce,cencut);] in
  let _ = report "precluster2_case0" in
  time_mitm cluster_areacut pdata cfn ccs;;

(* Lemma 5.2 [calc:pseudo2]; source code RWWHLQT.
   Egressive-edge bound: midpoint contact on a shared-edge tie or nonshared length-1.8 boundary, retaining all three equalities.
   Each terminal predicate excludes only a whole box or supplies a lower bound.
   Run with: python3 run.py --job mitm_precluster2_case1 *)
let precluster2_case1() =
  let cluster_areacut = two*aK in
  let pdata = reset_peri init2Cps in

  let out_of_midpointer dAC thACB =
    forall_alpha (fun t -> disjoint_I kappa (iloc one dAC (abs_I t))) thACB in
  let outdomfn (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),
	       (dAC,thACB,thCAB,arcB)) = out_of_midpointer dAC thACB
    || pseudo2_boundary_excluded dAB dBC dAC
    || (disjoint_I dAB d_shared_pseudo)
    || (disjoint_I dAC d_third_pseudo)
    || (disjoint_I dBC d_third_pseudo) in
  let keyfns = [ckeyfnAB] in
  let cfn = (unit_extra,fillfn5,forall_dom outdomfn,areafn5,keyfns) in

  let dAB_dBC_dAC = (d_shared_pseudo,d_third_pseudo,d_third_pseudo) in
  let cencut = (aK + epsN_I).high in
  let ccs = [(coord5 dAB_dBC_dAC,cencut);] in
  let _ = report("precluster2 case1 midpointer") in
  time_mitm cluster_areacut pdata cfn ccs;;

(* Lemma 5.2 [calc:pseudo2]; source code RWWHLQT.
   Egressive-edge bound: slider contact on a shared-edge tie or nonshared length-1.8 boundary, retaining all three equalities.
   Each terminal predicate excludes only a whole box or supplies a lower bound.
   Run with: python3 run.py --job mitm_precluster2_case2 *)
let precluster2_case2() =
  let cluster_areacut = two*aK in
  let pdata = reset_peri init2Cps in

  let notslider1 (t, t') = disjoint_I zero (t+t') in
  let notslider (t, t') =
    forall_alpha_pair notslider1 (t,t') in
  let outdomfn (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),
	       (dAC,thACB,thCAB,arcB)) =
      pseudo2_boundary_excluded dAB dBC dAC
      ||        notslider (thACB,thCAB) in

  let keyfns = [ckeyfnAB] in
  let cfn = (unit_extra,fillfn5,forall_dom outdomfn,areafn5,keyfns) in

  let dAB_dBC_dAC = (d_shared_pseudo,d_third_pseudo,d_third_pseudo) in
  let cencut = (aK + epsN_I).high in
  let ccs = [(coord5 dAB_dBC_dAC,cencut);] in
  let _ = report("precluster2 case2 slider") in
  time_mitm cluster_areacut pdata cfn ccs;;

(* Lemma 5.10 [calc:dimer-isosc]; source code KUGAKIK.
   Exclude an outside-double-contact long-isosceles subcritical peripheral in a dimer pair with total area at most 2 a_crit.
   Each terminal predicate excludes only a whole box or supplies a lower bound.
   Run with: python3 run.py --job mitm_dimer_isosceles_precluster *)
let dimer_isosceles_precluster() =
  let cluster_areacut = two*aK in
  let pdata = reset_peri init2Cps_isosceles_AB_AC in

  let fillfn () = mk2Ce d_subcrit_shared in
  let outdomfn (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),
		(dAC,thACB,thCAB,arcB)) =
    (dAB >> dAC || dBC >> dAC || disjoint_I dAC d_subcrit_shared) in
  let cfn = (unit_extra,fillfn,outdomfn,areafn2Ce,[ckeyfn2Ce]) in

  let cencut = (aK + epsN_I).high in
  let ccs = [(coord2Ce,cencut);] in
  let _ = report ("dimer with Tin isosceles") in
  time_mitm cluster_areacut pdata cfn ccs;;

(* Lemma 5.4 [calc:pseudo-area]; source code BXZBPJW.
   Pseudo-dimer pair-area bound 2 a_crit - epsilon_M; outside-double-contact peripheral with local AB=AC.
   Each terminal predicate excludes only a whole box or supplies a lower bound.
   Run with: python3 run.py --job mitm_precluster4_case0_experimental *)
let precluster4_case0_experimental() =
  let cluster_areacut = two*aK - epsM_I in
  let pdata = reset_peri init2Cps_isosceles_AB_AC in
  let fillfn () = mk2Ce d_shared_pseudo in
  let outdomfn (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),(dAC,thACB,thCAB,arcB)) =
    (dAB << 18//10 || dBC >> 18//10 || disjoint_I dAC d_shared_pseudo) in
  let keyfns = [ckeyfn2Ce] in
  let cfn = (unit_extra,fillfn,outdomfn,areafn2Ce,keyfns) in
  let cencut = (aK + epsN_I - epsM_I).high in
  let ccs = [(coord2Ce,cencut);] in
  let _ = report "precluster4_case0 isosceles Tin AB=AC --experimental" in
  time_mitm cluster_areacut pdata cfn ccs;;

(* Lemma 5.4 [calc:pseudo-area]; source code BXZBPJW.
   Pseudo-dimer pair-area bound 2 a_crit - epsilon_M; outside-double-contact peripheral with local BC=AC.
   Each terminal predicate excludes only a whole box or supplies a lower bound.
   Run with: python3 run.py --job mitm_precluster4_case1_experimental *)
let precluster4_case1_experimental() =
  let cluster_areacut = two*aK - epsM_I in
  let pdata = reset_peri init2Cps_isosceles_BC_AC in
  let fillfn () = mk2Ce d_shared_pseudo in
  let outdomfn (a,(dAB,thABC,thBAC,arcC),(dBC,thCBA,thBCA,arcA),(dAC,thACB,thCAB,arcB)) =
    (dAB << 18//10 || dBC >> 18//10 || disjoint_I dAC d_shared_pseudo) in
  let keyfns = [ckeyfn2Ce] in
  let cfn = (unit_extra,fillfn,outdomfn,areafn2Ce,keyfns) in
  let cencut = (aK + epsN_I - epsM_I).high in
  let ccs = [(coord2Ce,cencut);] in
  let _ = report "precluster4_case1 isosceles Tin BC=AC experimental" in
  time_mitm cluster_areacut pdata cfn ccs;;

(* The exceptional outgoing peripheral is bounded by aK+2*epsM_I,
   not aK+epsM_I. The total cluster target remains 3*aK+epsM_I. *)
let init2Cps_precluster6 =
  let (fn,ps) = init2Cps in
  let (extra,fillfn,outdomfn,areafn,keyfn) = fn in
  let outdomfn' (a,ddAB,ddBC,(dAC,thACB,thCAB,arcB)) =
    ((dAC << 18//10) && outdomfn (a,ddAB,ddBC,(dAC,thACB,thCAB,arcB))) ||
      (a >> aK + two * epsM_I) in
  let fn = (extra,fillfn,outdomfn',areafn,keyfn) in
  (fn,ps);;

(* Lemma 5.5 [calc:pseudo-area3]; source code JQMRXTH.
   Three-triangle pseudo-dimer bound 3 a_crit + epsilon_M: incoming edge AB, outgoing edge BC; exceptional peripheral cap a_crit + 2 epsilon_M.
   Each terminal predicate excludes only a whole box or supplies a lower bound.
   Run with: python3 run.py --job mitm_precluster6_case1 *)
let precluster6_case1() =
  let cluster_areacut = (int 3)*aK + epsM_I in
  let pdata = reset_peri init2Cps_precluster6 in
  let outdomfn _ = false in
  let keyfnT = ckeyfnAB in
  let keyfnS = ckeyfnBC in
  let cfn =
    (unit_extra,fillfn5,forall_dom outdomfn,areafn5,[keyfnT;keyfnS]) in
  let dAB_dBC_dAC = (d_shared_pseudo,d_egress,d_third_pseudo) in
  let cencut = (aK + epsN_I).high in
  let ccs = [(coord5 dAB_dBC_dAC,cencut);] in
  let _ = report("precluster6 case1 AB shared Tin, egress BC") in
  time_mitm cluster_areacut pdata cfn ccs;;

(* Lemma 5.5 [calc:pseudo-area3]; source code JQMRXTH.
   Three-triangle pseudo-dimer bound 3 a_crit + epsilon_M: incoming edge AB, outgoing edge AC; exceptional peripheral cap a_crit + 2 epsilon_M.
   Each terminal predicate excludes only a whole box or supplies a lower bound.
   Run with: python3 run.py --job mitm_precluster6_case2 *)
let precluster6_case2() =
  let cluster_areacut = (int 3)*aK + epsM_I in
  let pdata = reset_peri init2Cps_precluster6 in
  let outdomfn _ = false in
  let keyfnT = ckeyfnAB in
  let keyfnS = ckeyfnAC in
  let cfn =
    (unit_extra,fillfn5,forall_dom outdomfn,areafn5,[keyfnT;keyfnS]) in
  let dAB_dBC_dAC = (d_shared_pseudo,d_third_pseudo,d_egress) in
  let cencut = (aK + epsN_I).high in
  let ccs = [(coord5 dAB_dBC_dAC,cencut);] in
  let _ = report("precluster6 case2 AB shared Tin, egress AC") in
  time_mitm cluster_areacut pdata cfn ccs;;

(* Lemma 5.5 [calc:pseudo-area3]; source code JQMRXTH.
   Three-triangle pseudo-dimer bound 3 a_crit + epsilon_M: incoming edge BC, outgoing edge AB; exceptional peripheral cap a_crit + 2 epsilon_M.
   Each terminal predicate excludes only a whole box or supplies a lower bound.
   Run with: python3 run.py --job mitm_precluster6_case3 *)
let precluster6_case3() =
  let cluster_areacut = (int 3)*aK + epsM_I in
  let pdata = reset_peri init2Cps_precluster6 in
  let outdomfn _ = false in
  let keyfnT = ckeyfnBC in
  let keyfnS = ckeyfnAB in
  let cfn =
    (unit_extra,fillfn5,forall_dom outdomfn,areafn5,[keyfnT;keyfnS]) in
  let dAB_dBC_dAC = (d_egress,d_shared_pseudo,d_third_pseudo) in
  let cencut = (aK + epsN_I).high in
  let ccs = [(coord5 dAB_dBC_dAC,cencut);] in
  let _ = report("precluster6 case3 BC shared Tin, egress AB") in
  time_mitm cluster_areacut pdata cfn ccs;;

(* Lemma 5.5 [calc:pseudo-area3]; source code JQMRXTH.
   Three-triangle pseudo-dimer bound 3 a_crit + epsilon_M: incoming edge BC, outgoing edge AC; exceptional peripheral cap a_crit + 2 epsilon_M.
   Each terminal predicate excludes only a whole box or supplies a lower bound.
   Run with: python3 run.py --job mitm_precluster6_case4 *)
let precluster6_case4() =
  let cluster_areacut = (int 3)*aK + epsM_I in
  let pdata = reset_peri init2Cps_precluster6 in
  let outdomfn _ = false in
  let keyfnT = ckeyfnBC in
  let keyfnS = ckeyfnAC in
  let cfn =
    (unit_extra,fillfn5,forall_dom outdomfn,areafn5,[keyfnT;keyfnS]) in
  let dAB_dBC_dAC = (d_third_pseudo,d_shared_pseudo,d_egress) in
  let cencut = (aK + epsN_I).high in
  let ccs = [(coord5 dAB_dBC_dAC,cencut);] in
  let _ = report("precluster6 case4: BC shared Tin, egress AC") in
  time_mitm cluster_areacut pdata cfn ccs;;

(* Lemma 5.5 [calc:pseudo-area3]; source code JQMRXTH.
   Three-triangle pseudo-dimer bound 3 a_crit + epsilon_M: incoming edge AC, outgoing edge AB; exceptional peripheral cap a_crit + 2 epsilon_M.
   Each terminal predicate excludes only a whole box or supplies a lower bound.
   Run with: python3 run.py --job mitm_precluster6_case5 *)
let precluster6_case5() =
  let cluster_areacut = (int 3)*aK + epsM_I in
  let pdata = reset_peri init2Cps_precluster6 in
  let outdomfn _ = false in
  let keyfnT = ckeyfnAC in
  let keyfnS = ckeyfnAB in
  let cfn =
    (unit_extra,fillfn5,forall_dom outdomfn,areafn5,[keyfnT;keyfnS]) in
  let dAB_dBC_dAC = (d_egress,d_third_pseudo,d_shared_pseudo) in
  let cencut = (aK + epsN_I).high in
  let ccs = [(coord5 dAB_dBC_dAC,cencut);] in
  let _ = report("precluster6 case5: AC shared Tin, egress AB") in
  time_mitm cluster_areacut pdata cfn ccs;;

(* Lemma 5.5 [calc:pseudo-area3]; source code JQMRXTH.
   Three-triangle pseudo-dimer bound 3 a_crit + epsilon_M: incoming edge AC, outgoing edge BC; exceptional peripheral cap a_crit + 2 epsilon_M.
   Each terminal predicate excludes only a whole box or supplies a lower bound.
   Run with: python3 run.py --job mitm_precluster6_case6 *)
let precluster6_case6() =
  let cluster_areacut = (int 3)*aK + epsM_I in
  let pdata = reset_peri init2Cps_precluster6 in
  let outdomfn _ = false in
  let keyfnT = ckeyfnAC in
  let keyfnS = ckeyfnBC in
  let cfn =
    (unit_extra,fillfn5,forall_dom outdomfn,areafn5,[keyfnT;keyfnS]) in
  let dAB_dBC_dAC = (d_third_pseudo,d_egress,d_shared_pseudo) in
  let cencut = (aK + epsN_I).high in
  let ccs = [(coord5 dAB_dBC_dAC,cencut);] in
  let _ = report("precluster6 case6: AC shared Tin, egress BC") in
  time_mitm cluster_areacut pdata cfn ccs;;
