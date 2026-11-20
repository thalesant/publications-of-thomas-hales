(* Additional contact-domain bounds used by manuscript v007.
   Loaded after the geometric modules; loading starts no calculations.

   QKZVPNA / pintab_area: in a pin-T triangle, d_AB >= 1.72 implies
   area > 1.315.  VLMRTQH / small3C_area: every non-Delta triple-contact
   triangle with sides <= 1.8 has area > 1.262.  Together these exclude
   the AB-shared central pin-T placement in Lemma 5.4 / Appendix B.4.3.
   The Delta area estimate is the separate job onedeltajmin.

   ZHCFWUP / face_lj1: on beta_bar = pi/5, the LJ1 area strictly decreases
   when alpha_bar decreases at unit speed (Theorem 6.1, stage 6, Appendix A.7).
   Area bounds use area_I, not a conditional nonobtuse lower bound.
   See docs/CALCULATIONS.md and docs/code_commentary.pdf for the geometry. *)
open Pent;;

let pintab_dAB_min  = 172 // 100;;
let pintab_area_min = 1315 // 1000;;
let small3C_edge_max = 18 // 10;;
let small3C_area_min = 1262 // 1000;;

(* True: outside the pin-T domain, contact point beyond B's edge (x_gamma > 2 sigma),
   d_AB certainly < 1.72, or area > 1.315.  Same chart and exclusions as Dimer.one_pintx. *)
let one_pintab xs =
  try
    let ([alpha;beta;xa],_) = xs in
    if outdomfn_pint alpha beta then true
    else
      let (dBC,dAC,dAB,xc,_) = pintedge_extended alpha beta xa in
      xc >> two*sigma ||
      dAB << pintab_dAB_min ||
      area_I dBC dAC dAB >> pintab_area_min
  with Unstable -> false;;

let pintab_area () = recursepairtoeps one_pintab (Dimer.dummybool pintdomain);;

(* Same form as one172, with 1.8 for 1.7215 and 1.262 for aK. *)
let one_small3C outdomfn_domain edges abx =
  try
    let (alpha,beta,xgamma) = abx in
    outdomfn_domain alpha beta ||
      let (l1,l2,l3) = edges alpha beta xgamma in
      longest_exceeds l1 l2 l3 small3C_edge_max || area_I l1 l2 l3 >> small3C_area_min
  with Unstable -> false;;

let small3C_area () =
  map (fun (_,outdom,edges,domain) -> recursetofinish (one_small3C outdom edges) domain) types3C;;

(* Same form as Autodiff.one_twist_claim_lj2, with the LJ_1 shared-edge chart. *)
let one_face_lj1 xs =
  try
    let ([alpha';xbeta],_) = xs in
    if outdomfn_shared_lj1 alpha' pi15 xbeta then true
    else
      let (l1,l2,l3) = Autodiff.shared_lj1edgeD (alpha',- one) (pi15,zero) (xbeta,zero) in
      let (_,a') = Autodiff.area_D l1 l2 l3 in
      a' << zero
  with Unstable -> false;;

let face_lj1 () =
  let ee = merge_I (- Dimer.ice_ray_nbd) (Dimer.ice_ray_nbd) in
  recursepairtoeps one_face_lj1 (Dimer.dummybool [[zero2 Dimer.ice_ray_nbd; sigma+ee]]);;

(* Explicit invocation belongs to the launcher. Loading these definitions runs no searches. *)
