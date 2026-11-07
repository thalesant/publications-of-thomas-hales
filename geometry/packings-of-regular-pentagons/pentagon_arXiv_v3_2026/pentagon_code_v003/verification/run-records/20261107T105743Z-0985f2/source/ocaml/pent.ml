(* COMPUTATION QGPVOYX: mathematical claim and job selection in docs/CALCULATIONS.md. *)
(* Original notice: This code is in the public domain.
   Thomas Hales April 12, 2015--September 2016. *)
(* Core interval geometry and one-triangle exclusions.
   All lengths use pentagon circumradius 1; angles are radians.
   A true exclusion predicate eliminates its whole input box. False means
   unresolved, not a counterexample. Division/square-root uncertainty raises
   Unstable and is subdivided by the calling verifier.
   Original mathematical functions: Thomas Hales, 2015--2016 (public domain).
   This release separates examples from definitions; see provenance/changes.diff. *)

module Pent = struct

let rec selectsome = function
  | [] -> []
  | None::xs -> selectsome xs
  | Some x::xs -> x:: selectsome xs;;

let the x = match x with
  | None -> failwith "the"
  | Some t -> t;;

let issome x = match x with
  | None -> false
  | _ -> true;;

let isnone x = not(issome x);;

let outer = Lib.allpairs;;

let pair x y = x,y;;

let outertriple k1 k2 k3 =
  let k123 = outer pair k1 (outer pair k2 k3) in
    map (fun (i,(j,k)) -> (i,j,k)) k123;;

let ( +~ ) = Stdlib.( + );;

let ( *~) = Stdlib.( * );;

let ( -~ ) = Stdlib.( - );;

let ( >. ) (x:float) (y:float) = x > y;;

let ( <. ) (x:float) (y:float) = x < y;;

let sqrt = Stdlib.sqrt;;

let sin = Stdlib.sin;;

let cos = Stdlib.cos;;

let ( + ) = ( +$ );;

let ( - ) = ( -$ );;

let ( * ) = ( *$ );;

let ( ~- ) = ( ~-$ );;

let mk_interval(a,b) = {low=a;high=b};;

let m r = mk_interval(r,r);;

let mk x y = mk_interval(x,y);;

let zero = m 0.0;;

let one = m 1.0;;

let two = m 2.0;;

let four = m 4.0;;

let i16 = m 16.0;;

let merge_I x y = {low = min x.low y.low;high = max x.high y.high};;

(* Closed intersection. Disjoint inputs raise Failure; endpoint contact remains a singleton. No empty interval is substituted for an unresolved evaluation. *)
let inter_I x y =
  let t = {low = max x.low y.low; high = min x.high y.high} in
  let _ = t.low <= t.high || failwith "inter_I void" in
  t;;

let min_I y = {low = y.low;high = y.low};;

let max_I y = {low = y.high;high = y.high};;

let min2_I x y = min_I (merge_I x y);;

let max2_I x y = max_I (merge_I x y);;

let max3_I x y z = max2_I (max2_I x y) z;;

let mem_I r i = (i.low <= r && r <= i.high);;

let width_I x = max_I x - min_I x;;

(* Strict interval separation: x >> y means every point of x exceeds every point of y. Equality or overlapping intervals do not justify exclusion. *)
let ( >> ) x y = x.low >. y.high;;

let ( >>= ) x y = x.low >= y.high;;

let ( << ) x y = x.high <. y.low;;

let ( <<= ) x y = x.high <= y.low;;

let ( >>. ) x y = x.low >. y;;

let ( <<. ) x y = x.high <. y;;

let disjoint_I x y = (x >> y) || (y >> x);;

let meet_I x y = not (disjoint_I x y);;

let abs_I = Interval.abs_I;;

(* Division is deliberately unresolved near a zero denominator. The fixed 1e-8 guard is historical and is not a proof tolerance. *)
let (/) =
  let eps_I = mk (- 1.0e-8) (1.0e-8) in
  fun x y ->
    if disjoint_I eps_I y then x /$ y else raise Unstable;;

let int = Interval.float_i;;

let rat i j =   (int i) / (int j);;

let ( // ) = rat;;

let hasint x =
  let t = x - m (floor x.low) in
  mem_I 0.0 t || mem_I 1.0 t;;

let getint x =
  let k = m (floor x.low) in
  let k' = if disjoint_I k x then k+one else k in
  let _ = disjoint_I (k'+one) x || raise Unstable in
  if meet_I k' x then Some k' else None;;

let ratpi i j =
  (pi_I *$. float_of_int i) /$. float_of_int j;;

let pi =  pi_I;;

let pi2 = ratpi 1 2;;

let twopi = ratpi 2 1;;

let pi15 = ratpi 1 5;;

let pi25 = ratpi 2 5;;

let pi35 = ratpi 3 5;;

let pi45 = ratpi 4 5;;

let pi65 = ratpi 6 5;;

let pi110 = ratpi 1 10;;

let pi310 = ratpi 3 10;;

let pi710 = ratpi 7 10;;

let kappa = cos_I (pi /$. 5.0);;

let sigma = sin_I (pi /$. 5.0);;

let aK = (1.0 +.$ kappa)*$ (3.0 *.$ (kappa *$ sigma)) /$. 2.0;;

let acrit = aK;;

let amin =  1237 // 1000;;

let epsN_I = aK - amin;;

let epsM_I = 8 // 1000;;

(* Translate the legacy Failure contract into the project exception Unstable. The CRlibm adapter restores this contract only for the observed wholly negative square-root case. *)
let sqrt_I x =
  try
    Interval.sqrt_I x
  with Failure _ -> raise Unstable;;

let square_I x = x*x;;

let acos_I x =
  try
    Interval.acos_I x
  with Failure _ -> raise Unstable;;

let ups_I x1 x2 x3 =
  two * (x1 * x2 + x2 * x3 + x3 * x1) - x1*x1 - x2*x2 - x3*x3;;

let area_I y1 y2 y3 =
  let x1 = y1 * y1 in
  let x2 = y2 * y2 in
  let x3 = y3 * y3 in
    sqrt_I (ups_I x1 x2 x3 ) / four;;

(* Conditional lower bound on the NONOBTUSE triangles represented by the three side intervals. The independent lower endpoints need not form a nonobtuse triangle; the Heron polynomial argument is in docs/code_commentary.tex. A negative radicand is Unstable, not a proof of emptiness. *)
let areamin_acute y1 y2 y3 =
  area_I (min_I y1) (min_I y2) (min_I y3);;

(* Angle opposite the third side. Endpoint optimizations are conditional on certified acute/obtuse derivative signs; otherwise retain the general interval cosine-law evaluation. *)
let iarc =
  let mn = min_I in
  let mx = max_I in
  let iarc1 a b cop =
    acos_I (((a * a) + (b*b) - (cop*cop)) / (two * a * b)) in
  let iarc2 a b cop a' b' cop' =
    merge_I (iarc1 a b cop) (iarc1 a' b' cop') in
  fun a b cop ->
    let (a,b) = if a << b then (a,b) else (b,a) in
    let b_obtuse =  b*b >> a*a+cop*cop in
    if b_obtuse
    then iarc2 (mn a) (mx b) (mn cop) (mx a) (mn b) (mx cop)
    else
      let ab_acute = b*b << a*a+cop*cop && a*a << b*b+cop*cop in
      if ab_acute
      then iarc2 (mx a) (mx b) (mn cop) (mn a) (mn b) (mx cop)
      else iarc1 a b cop;;

let lawsines a alpha beta gamma =
  let aa = a / sin_I alpha in
    (aa * sin_I beta, aa * sin_I gamma);;

let iloc =
  let mx = max_I in
  let mn = min_I in
  let ilocc a b costh =
    sqrt_I(a * a + b * b - two * a * b * costh) in
  let ilocc2 a b cth a' b' cth' = merge_I (ilocc a b cth) (ilocc a' b' cth') in
    fun a b theta ->
        let costh = cos_I theta in
	let (a,b) = if a << b then (a,b) else (b,a) in
	let b_obtuse = b*costh >> a in
	if b_obtuse
	then ilocc2 (mn a) (mx b)  (mn costh) (mx a) (mn b)  (mx costh)
	else
	  let ab_acute = b*costh << a && a*costh << b in
	  if ab_acute
	  then ilocc2 (mx a) (mx b) (mn costh) (mn a) (mn b) (mx costh)
	  else ilocc a b costh;;

(* Contact geometry: h is the signed displacement from the receptor-edge midpoint, kappa its distance to the receptor center, and psi the relative edge direction. The cosine law gives the center distance. *)
let ell_aux h psi =
  let r = sqrt_I (h * h + kappa* kappa) in
  let theta = acos_I (h / r) in
    iloc one r (psi+theta);;

let ellx  =
  fun x alpha ->
    ell_aux (sigma - x) (alpha + pi310);;

(* Pointer/receptor contact coordinates. Return (center distance, first inclination, second inclination); xalpha measures from the edge endpoint, not from its midpoint. *)
let thetax =
  fun xalpha alpha ->
    let h = xalpha - sigma in
    let r = sqrt_I (h*h + kappa*kappa) in
    let phi' = asin_I (h / r) in
    let delta = pi65 - (alpha + phi') in
    let elx = iloc r one delta in
    let ely = iloc r (two * sigma) (delta  - pi310) in
    let theta' = pi25 - (iarc one elx ely) in
    let theta = alpha - theta' in
    (elx,theta,theta');;

(* The second directed-contact chart exchanges pointer/receptor roles. It extends alpha past 2*pi/5; do not identify its angle convention with an unoriented center angle. *)
let shifted_thetax xalpha alpha =
  let (elx,theta,theta') = thetax (two*sigma - xalpha) (alpha - pi25) in
  elx,(theta'+ pi25),theta;;

let mergefn f0 f1 m cutax  =
  fun x ->
    if x << cutax then f0 x
    else if x >> cutax then f1 x
    else
      let x0 = merge_I (min_I x) cutax in
      let x1 = merge_I (max_I x) cutax in
      m (f0 x0) (f1 x1);;

let ethetax xalpha alpha =
  if alpha << pi25 then thetax xalpha alpha
  else if alpha >> pi25 then shifted_thetax xalpha alpha
  else
    mergefn (thetax xalpha) (shifted_thetax xalpha)
    (fun (x1,y1,z1) (x2,y2,z2) -> merge_I x1 x2,merge_I y1 y2, merge_I z1 z2)
      (pi25) alpha;;

let theta'mono xa alpha =
    let (_,_,th1) = ethetax (min_I xa) (min_I alpha) in
    let (_,_,th2) = ethetax (max_I xa) (max_I alpha) in
    merge_I th1 th2;;

let thetamono xa alpha =
    let (_,th1,_) = ethetax (min_I xa) (max_I alpha) in
    let (_,th2,_) = ethetax (max_I xa) (min_I alpha) in
    merge_I th1 th2;;

(* Bounds the contact length over a box using endpoint and stationary candidates. The stationary x and alpha values are retained whenever their interval meets the box. *)
let ellxmono_r xa alpha =
    let ellmax x =
      let h = x - sigma in
      let r = sqrt_I (kappa*kappa+ h* h) in
      let alpham = pi15 - asin_I (h / r) in
      if (meet_I alpham alpha)
      then ellx x alpham
      else max2_I (ellx x (min_I alpha)) (ellx x (max_I alpha)) in
    let ellM = max2_I (ellmax (min_I xa)) (ellmax (max_I xa)) in
    let ellmin alp =
      let xm = sigma + sin_I (alp - pi15) in
      if (meet_I xm xa)
      then ellx xm alp
      else min2_I (ellx (min_I xa) alp) (ellx (max_I xa) alp) in
    let ellm = min2_I (ellmin (min_I alpha)) (ellmin (max_I alpha)) in
    merge_I ellm ellM;;

let ellxmono xa alpha =
    let alpha2 =
      if alpha << pi25 then alpha
      else if alpha >> pi25 then (pi45-alpha)
      else (merge_I (min2_I alpha (pi45-alpha)) pi25) in
    ellxmono_r xa alpha2;;

let ellthetax xa alpha =
    (ellxmono xa alpha,thetamono xa alpha,theta'mono xa alpha);;

let ellthetax_sgn xalpha alpha sgn =
  let (el,th,th') = ellthetax xalpha alpha in
  if sgn then (el,th,th') else (el,th',th);;

(* Triple contact, pinwheel chart: alpha+beta+gamma=pi/5. First apply the sine rule to the small contact triangle, then convert each contact pair into a center distance. *)
let pinwheeledge =
  fun alpha beta xgamma ->
    let gamma = pi15 - (alpha + beta) in

    let (xalpha,xbeta) =
      lawsines xgamma (pi25 - alpha) (pi25 - beta) (pi25 - gamma) in
    ((ellxmono xalpha alpha),
     (ellxmono xbeta beta),
     (ellxmono xgamma gamma));;

let pintedge_extended =
  fun alpha beta xalpha ->
    let gamma = pi - (alpha+beta) in
    let alpha' = pi25 - alpha in
    let beta' = pi25 - beta in
    let gamma' = pi25 - gamma in
    let eps' = pi35 - alpha' in
    let eps = pi - eps' in
    let delta = pi - (beta' + eps) in
    let delta' = pi - delta in
    let (w1,w2) = lawsines xalpha eps' pi25 alpha' in
    let (w3,w4) = lawsines (two * sigma + w2) delta beta' eps in
    let (w5,w6) = lawsines (two * sigma) delta' pi25 gamma' in
    let xbeta = w4-w6 in
    let xgamma = w1+w3+w5 in
    ((ellxmono xalpha alpha),
     (ellxmono xbeta beta),
     (ellxmono xgamma gamma),xgamma,xbeta);;

let pintedge alpha beta xalpha =
  let (d1,d2,d3,_,_) = pintedge_extended alpha beta xalpha in
  (d1,d2,d3);;

let deltajedge =
  fun alpha beta xalpha' ->
    let gamma = pi15 - (alpha + beta) in
    let alpha' = pi25 - alpha in
    let beta' = pi25 - beta in
    let gamma' = pi25 - gamma in
    let (yalpha,ygamma) = lawsines (two * sigma) (beta') (alpha') (gamma') in
    let xbeta' = two * sigma - (ygamma + xalpha') in
    let xgamma' = two * sigma - yalpha in
    ((ellxmono xalpha' alpha'),
     (ellxmono xbeta' beta'),
     (ellxmono xgamma' gamma'));;

let ljedge_extended =
  fun alpha beta xalpha ->
  let gamma = pi35 - (alpha+beta) in
  let alpha' = pi25 - alpha in
  let beta' = pi25 - beta in
  let gamma' = pi25 - gamma in
  let delta' = pi - (alpha' + beta') in
  let (s1,b1) = lawsines xalpha delta' beta' alpha' in
  let s2 = two*sigma - s1 in
  let (b2,xgamma) = lawsines s2 pi25 gamma' delta' in
  let xbeta = b1 - b2 in
    ((xbeta,xgamma),
    ((ellxmono xalpha alpha),
     (ellxmono xbeta beta),
     (ellxmono xgamma gamma)));;

let ljedge alpha beta xalpha =
  let (_,ll) = ljedge_extended alpha beta xalpha in
  ll;;

let tjedge_extended =
  fun alpha beta xgamma ->
    let gamma = pi - (alpha + beta) in
    let alpha' = pi25 - alpha in
    let beta' = pi25 - beta in
    let gamma' = pi25 - gamma in
    let delta' = pi - (pi25 + gamma') in
    let eps' = pi - (pi25 + beta') in
    let (t1,s1) = lawsines xgamma delta' gamma' pi25 in
    let s2 = two*sigma - s1 in
    let (a2,t2) = lawsines s2 eps' delta' alpha' in
    let t3 = two*sigma + t1 - t2 in
    let (a3,xbeta) = lawsines t3 pi25 beta' eps' in
    let xalpha = a2-a3 in
    let t = (xbeta,t1,s1,s2,a2,t2,t3,a3,xalpha) in
    ((ellxmono xalpha alpha),
     (ellxmono xbeta beta),
     (ellxmono xgamma gamma),
     (xalpha,xbeta));;

let tjedge alpha beta xgamma =
  let (l1,l2,l3,_) = tjedge_extended alpha beta xgamma in
  (l1,l2,l3);;

(* Shared-edge charts return (dBC,dAC,dAB), with AC the shared edge. The input is (bar alpha,bar beta,bar x_beta). These permutations are essential for assembling two triangles. *)
let shared_pinwheeledge alpha beta xbeta =
  let gamma = pi15 - (alpha+beta) in
  let dAB,dBC,dAC = pinwheeledge gamma alpha xbeta in
  dBC,dAC,dAB;;

let shared_pintedge alpha beta xbeta =
  let dAC,dBC,dAB = pintedge beta alpha xbeta in
  dBC,dAC,dAB;;

let shared_lj1edge_extended =
  fun alpha' beta xbeta ->
    let alpha = pi25 - alpha' in
    let gamma = pi35 - (alpha + beta) in
    let beta' = pi25 - beta in
    let gamma' = pi25 - gamma in
    let delta' = pi - (alpha'+gamma') in
    let (c1,xaa) = lawsines (two*sigma) delta' alpha' gamma' in
    let (a,c2) = lawsines xbeta delta' beta' pi25 in
    let xa = xaa - a in
    let xc = c1 + c2 in
    (ellx xa alpha,ellx xbeta beta,ellx xc gamma,xa,xc);;

let shared_lj1edge alpha' beta xbeta =
  let dBC,dAC,dAB,_,_ = shared_lj1edge_extended alpha' beta xbeta in
  dBC,dAC,dAB;;

let shared_lj2edge alpha beta xbeta =
  let (dAC,dBC,dAB) = ljedge beta alpha xbeta in
  dBC,dAC,dAB;;

let shared_lj2edge_extended alpha beta xbeta =
  let t,(dAC,dBC,dAB) = ljedge_extended beta alpha xbeta in
  dBC,dAC,dAB,t;;

let shared_lj3edge_extended =
  fun alpha beta xbeta ->
    let gamma = pi35 - (alpha + beta) in
    let alpha' = pi25 - alpha in
    let beta' = pi25 - beta in
    let gamma' = pi25 - gamma in
    let delta' = pi - (alpha'+gamma') in
    let (s1,a1) = lawsines xbeta delta' pi25 beta' in
    let s2 = two*sigma - s1 in
    let (xgamma,aa) = lawsines s2 alpha' delta' gamma' in
    let xalpha = aa - a1 in
    (ellx xalpha alpha,
     ellx xbeta beta,
     ellx xgamma gamma,
     (s2,xalpha,xgamma));;

let shared_lj3edge alpha beta xbeta =
  let (dBC,dAC,dAB,_) = shared_lj3edge_extended alpha beta xbeta in
  (dBC,dAC,dAB);;

let shared_tj1edge =
    fun alpha beta xbeta ->
    let gamma = pi - (alpha + beta) in
    let alpha' = pi25 - alpha in
    let beta' = pi25 - beta in
    let gamma' = pi25 - gamma in
    let delta' = pi - (alpha'+gamma') in
    let eps' = pi - (pi25  + beta') in
    let (s1,a2) = lawsines xbeta eps' pi25 beta' in
    let (a1,cc) = lawsines (two*sigma) delta' gamma' alpha' in
    let s2 = two*sigma - s1 in
    let (c2,a3) = lawsines s2 delta' eps' pi25 in
    (ellx ((a1+a3)-a2) alpha,ellx xbeta beta,ellx (cc-c2) gamma);;

let shared_tj2edge alpha beta xbeta =
  let gamma = pi - (alpha + beta) in
  let (dAB,dBC,dAC) = tjedge gamma alpha xbeta in
  dBC,dAC,dAB;;

let shared_tj2edge_extended alpha beta xbeta =
  let gamma = pi - (alpha + beta) in
  let (dAB,dBC,dAC,t) = tjedge_extended gamma alpha xbeta in
  dBC,dAC,dAB,t;;

let shared_tj3edge_extended alpha' beta xbeta =
    let alpha = pi25 - alpha' in
    let gamma = pi - (alpha + beta) in
    let beta' = pi25 - beta in
    let gamma' = pi25 - gamma in
    let eps' = pi - (alpha' + pi25) in
    let delta' = pi - (beta'+ pi25) in
    let (c2,a2) = lawsines (two*sigma) eps' alpha' pi25 in
    let (a1,s1) = lawsines xbeta delta' beta' pi25 in
    let s2 = two*sigma - s1 in
    let (a3,cc) = lawsines s2 eps' gamma' delta' in
    let xalpha = (a2+a3)-a1 in
    let xgamma = cc - c2 in
    (ellx xalpha alpha,ellx xbeta beta,ellx xgamma gamma,xalpha,xgamma);;

let shared_tj3edge alpha' beta xbeta =
  let (dBC,dAC,dAB,_,_) = shared_tj3edge_extended alpha' beta xbeta in
  (dBC,dAC,dAB);;

let pint_constant = 605 // 10000;;

let outdomfn_shared_pint alpha beta xbeta =
  let ab = alpha+beta in
  if pi35 >> ab || xbeta >> pint_constant then true
  else
    let (_,_,_,xgamma,_) = pintedge_extended beta alpha xbeta in
    xgamma >> two*sigma;;

let outdomfn_shared_pinwheel alpha beta xbeta =
  let one_pinwheelx_constant = 8 // 10 in
   alpha+beta  >> pi15 || xbeta >> one_pinwheelx_constant;;

let outdomfn_15_35 alpha beta =
  let ab = alpha+beta in
  pi15 >> ab || ab >> pi35;;

let outdomfn_sigma xsig =
  xsig << zero || xsig >> two*sigma;;

let outdomfn_shared_lj1 alpha' beta xbeta =
  let alpha = pi25 - alpha' in
  if outdomfn_15_35 alpha beta then true
  else
    let (_,_,_,xa,xc) = shared_lj1edge_extended alpha' beta xbeta in
    outdomfn_sigma xa || outdomfn_sigma xc;;

let outdomfn_shared_lj2 alpha beta xbeta =
  outdomfn_15_35 alpha beta;;

let outdomfn_shared_lj3 alpha beta xbeta  =
  let one_ljx_constant = 9//10 in
  if outdomfn_15_35 alpha beta || alpha >> one_ljx_constant  then true
  else
    let (_,_,_,(_,xa,xc)) = shared_lj3edge_extended alpha beta xbeta in
    outdomfn_sigma xa || outdomfn_sigma xc;;

let outdomfn_35_45 alpha beta =
  let ab = alpha+beta in
  pi35 >> ab || ab >> pi45;;

let outdomfn_shared_tj1 alpha beta xbeta =
  let one_tjx_constant = one in
  outdomfn_35_45 alpha beta || (beta << one_tjx_constant);;

let outdomfn_shared_tj2 alpha beta xbeta =
  if outdomfn_35_45 alpha beta then true
  else
    let (_,_,_,(x1,x2)) = shared_tj2edge_extended alpha beta xbeta in
    outdomfn_sigma x1 || outdomfn_sigma x2;;

let outdomfn_shared_tj3 alpha' beta xbeta =
  let alpha = pi25 - alpha' in
  outdomfn_35_45 alpha beta;;

let rec maxwidth c (i,w) = function
  | [] -> (i,w)
  | x::xs ->
      let t = x.high -. x.low in
      let c' = Stdlib.(+) c 1 in
      if t >= w then maxwidth c' (c,t) xs else maxwidth c' (i,w) xs;;

let testi =
  [mk_interval (1.0,2.0);mk_interval(2.0,3.5);mk_interval(2.3,3.2)];;

let string_of_interval x =
  "("^string_of_float x.low ^","^string_of_float x.high^")";;

let join_semi = String.concat ";";;

let string_of_list f xs = "["^join_semi (map f xs)^"]";;

(* Bisect a widest component, covering the closed parent box. Exhaustion of the minimum width raises Failure and cannot count as verification. *)
let splitlist eps xs =
  let _ = not(xs=[]) || failwith "empty list" in
  let (i,w) = maxwidth 0 (0,0.0) xs in
  let _ = w > eps ||
    failwith ("splitlist width:" ^ string_of_float w ^ " " ^
		 string_of_int i ^",\n"^string_of_list string_of_interval xs) in
  let (us,v::vs) = chop_list i xs in
  let t = (v.low +. v.high) /. 2.0 in
  let v1 = mk_interval(v.low,t) in
  let v2 = mk_interval(t,v.high) in
    (us @ (v1 :: vs)),(us @ (v2 :: vs));;

let prepost pre post f x =
  let ys = pre x in
  let (x1,x2) = f ys in
    (post x1,post x2);;

let split eps pre post = prepost pre post (splitlist eps);;

let rec recurser eps n onef = function
  | [] -> (n,true)
  | abx :: xs ->
      if onef abx then recurser eps (succ n) onef xs
	  else
	    let (a1,a2) =
	      splitlist eps abx in
	      recurser eps (succ n) onef (a1::a2::xs);;

let print_stats n xs =
  if (n mod 100000 = 0) then
    let ws = map (map width_I) (map fst xs) in
    let vol = end_itlist ( + ) (map (end_itlist ( * )) ws) in
    report (Printf.sprintf "count=%d, length=%d, vol=%4.4f" n (List.length ws) vol.high)
  else ();;

(* As above, carrying immutable contact-type data with each box. Counts include subdivision nodes, not just terminal boxes. *)
let rec recurserpair eps n onef = function
  | [] -> (n,true)
  | abx :: xs as xss ->
    let _ = print_stats n xss in
    if onef abx then recurserpair eps (succ n) onef xs
    else
      let (a1,a2) = splitlist eps (fst abx) in
      recurserpair eps (succ n) onef
	((a1,snd abx)::(a2,snd abx)::xs);;

let recursetoeps = recurser (1.0e-8) 0;;

let recursepairtoeps = recurserpair (1.0e-8) 0;;

let recurserpair_x eps n onef xs  =
  recurserpair eps n (fun (t,_) -> onef t) (map (fun x -> x,()) xs);;

let recurs_xeps = recurserpair_x (1.0e-8) 0;;

let recursetofinish onef =
  let wrap3 onef abx =
    let [a;b;x] = abx in
      onef (a,b,x) in
    recursetoeps (wrap3 onef);;

let area_exceeds l1 l2 l3 a = (area_I l1 l2 l3 >> a);;

let longest_exceeds l1 l2 l3 r = max l1.low (max l2.low l3.low) > r.high;;

let longgt172 =
  let i172 =  17215 // 10000 in
  fun l1 l2 l3 -> longest_exceeds l1 l2 l3 i172;;

(* Subcritical longest-edge check: out-of-domain OR a side exceeds 1.7215 OR area exceeds aK. The 1.7215 threshold is stronger than the paper's 1.72. *)
let one172 outdomfn_domain edges abx =
  try
    let (alpha,beta,xgamma) = abx in
    outdomfn_domain alpha beta ||
      let (l1,l2,l3) = edges alpha beta xgamma in
      (longgt172 l1 l2 l3) || area_exceeds l1 l2 l3 aK
  with | Unstable -> false;;

let outdomfn_pinwheel alpha beta =
  (beta >> alpha) ||
    pi15 >> alpha + two * beta ||
    alpha+beta  >> pi15;;

let outdomfn_lj alpha beta =
  let ab = alpha+beta in
  pi15 >> ab || ab >> pi35;;

let outdomfn_tj alpha beta =
  let ab = alpha+beta in
  pi35 >> ab || ab >> pi45;;

let outdomfn_pint alpha beta =
  let ab = alpha+beta in
  pi35 >> ab;;

let calculate suffix oner (name, outdomfn, edges, domain) =
  mkcalc ((name^suffix),fun() ->
    let once = oner outdomfn edges in
    time (recursetofinish once) domain);;

let zero2 = merge_I zero;;

let pinwheeldomain = [[zero2 pi15;zero2 pi15;zero2 (two*sigma)]];;

let ljdomain =  [[zero2 pi25;zero2 pi25;zero2 (two*sigma)]];;

let tjdomain = [[merge_I pi15 pi25;merge_I pi15 pi25;zero2 (two*sigma)]];;

let pintdomain = [[merge_I pi15 pi25;merge_I pi15 pi25;
		   zero2 pint_constant]];;

let types3C =
  [("pinwheel",outdomfn_pinwheel,pinwheeledge,pinwheeldomain);
   ("lj",outdomfn_lj,ljedge,ljdomain);
   ("tj",outdomfn_tj,tjedge,tjdomain);
   ("pint",outdomfn_pint,pintedge,pintdomain)];;

let () = ignore (map (calculate "17215" one172) types3C);;

(* Nonobtuse area check on the classified triple-contact charts; amin=1.237. This is the proof calculation, unlike the optional MITM diagnostic with its historical 1.2 cutoff. *)
let one1237 outdomfn_domain edges abx =
  try
    let (alpha,beta,xgamma) = abx in
    outdomfn_domain alpha beta ||
    let (l1,l2,l3) = edges alpha beta xgamma in
      areamin_acute l1 l2 l3 >> amin
    with | Unstable -> false;;

let () = ignore (map (calculate "1237" one1237) types3C);;

let outdomfn_delta alpha beta =
  (beta >> alpha) || alpha+beta >> pi15;;

let onedeltajamin abx =
  try
    let (alpha,beta,xalpha) = abx in
    outdomfn_delta alpha beta ||
      let (l1,l2,l3) = deltajedge alpha beta xalpha in
      areamin_acute l1 l2 l3 >>  15 // 10
  with | Unstable -> false;;

let () = ignore (mkcalc ("onedeltajmin",fun() ->
  let ff = sigma / (two * kappa) in
	  (recursetofinish onedeltajamin)
	    [[zero2 pi15;zero2 pi15;zero2 (two * (sigma-ff))]]));;

end;;
