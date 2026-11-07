(* COMPUTATION YQRQXVD: see docs/CALCULATIONS.md and docs/TESTING.md. *)
(* Tests of the release functions, not rewritten copies of their predicates.
   EXACT: dyadic/algebraic fixtures with exact expectations.
   CONTRACT: interval/order/finite-model invariants.
   DIAGNOSTIC: numerical reference or round-trip evidence, not a proof.
   Generated tests have an explicit seed and report their witness count. *)
module PentagonTests = struct
open Stdlib
module I = Interval_crlibm.I
let m = Pent.m
let mk = Pent.mk
let rows = ref []
let add id kind f = rows := (id,kind,f)::!rows
let demand why b = if not b then failwith why
let contains x v = x.low <= v && v <= x.high
let overlaps = Pent.meet_I
let valid x = x.low <= x.high &&
  classify_float x.low <> FP_nan && classify_float x.high <> FP_nan
let both x lo hi = valid x && contains x lo && contains x hi
let same x y = x.low = y.low && x.high = y.high
let check id kind b = add id kind (fun () -> demand id (b ()))
let raises_unstable f = try ignore(f()); false with Unstable -> true
let raises_failure f = try ignore(f()); false with Failure _ -> true
let scalar x = (x.low +. x.high) /. 2.
let member v xs = List.exists (fun x -> contains x v) xs
let eps = 1.e-9
let near x y = abs_float (x-.y) < eps

let core () =
  check "interval.strict-equality-retained" "CONTRACT" (fun () -> not Pent.(m 2. >> m 2.));
  check "interval.touching-not-disjoint" "CONTRACT" (fun () -> not(Pent.disjoint_I (mk 0. 1.) (mk 1. 2.)));
  check "interval.separated-disjoint" "CONTRACT" (fun () -> Pent.disjoint_I (mk 0. 1.) (mk 1.25 2.));
  check "interval.intersection-singleton" "EXACT" (fun () -> same (Pent.inter_I (mk 0. 1.) (mk 1. 2.)) (m 1.));
  check "interval.intersection-empty" "CONTRACT" (fun () -> raises_failure(fun()->Pent.inter_I (mk 0. 1.) (mk 2. 3.)));
  check "interval.empty-option" "CONTRACT" (fun () -> Banana.someinter_I (mk 0. 1.) (mk 2. 3.) = None);
  check "interval.touching-option" "CONTRACT" (fun () -> match Banana.someinter_I (mk 0. 1.) (mk 1. 2.) with Some x -> same x (m 1.) | None -> false);
  check "interval.add-exact" "EXACT" (fun () -> same I.(mk 1. 2. + mk 3. 4.) (mk 4. 6.));
  check "interval.multiply-signs" "EXACT" (fun () -> both I.(mk (-2.) 3. * mk (-4.) 5.) (-12.) 15.);
  check "interval.divide-dyadic" "EXACT" (fun () -> both I.(mk 1. 2. / mk 4. 8.) 0.125 0.5);
  check "interval.denominator-guard" "CONTRACT" (fun () -> raises_unstable(fun()->Pent.(one / mk (-1.e-9) 1.e-9)));
  check "interval.sqrt-positive" "EXACT" (fun () -> same (Pent.sqrt_I (mk 4. 9.)) (mk 2. 3.));
  check "interval.sqrt-partial-domain" "EXACT" (fun () -> same (Pent.sqrt_I (mk (-1.) 4.)) (mk 0. 2.));
  check "interval.sqrt-recorded-failure" "CONTRACT" (fun () -> raises_unstable(fun()->Pent.sqrt_I (mk (-2.854101966249686) (-2.854101966249678))));
  check "interval.sin-zero" "EXACT" (fun () -> contains (I.sin (m 0.)) 0.);
  check "interval.cos-zero" "EXACT" (fun () -> contains (I.cos (m 0.)) 1.);
  check "interval.sin-critical-point" "CONTRACT" (fun () -> contains (I.sin Pent.pi2) 1.);
  check "interval.cos-critical-point" "CONTRACT" (fun () -> contains (I.cos Pent.pi) (-1.));
  check "interval.sin-full-period" "CONTRACT" (fun () -> both (I.sin (Pent.merge_I Pent.zero Pent.twopi)) (-1.) 1.);
  check "constants.pythagorean" "CONTRACT" (fun () -> contains Pent.(kappa*kappa+sigma*sigma) 1.);
  check "constants.phi-identity" "CONTRACT" (fun () -> contains Pent.(int 4*kappa*kappa-two*kappa-one) 0.);
  check "constants.eps-order" "CONTRACT" (fun () -> Pent.(epsN_I >> epsM_I && epsM_I >> zero));
  check "constants.two-epsM-less-epsN" "CONTRACT" (fun () -> Pent.(two*epsM_I << epsN_I));
  check "constants.density-two-formulas" "CONTRACT" (fun () -> overlaps Pent.(int 5*kappa*sigma/(two*aK)) Pent.((int 5-sqrt_I(int 5))/int 3));
  List.iter (fun (a,b,c,area) ->
    check (Printf.sprintf "area.pythagorean.%g-%g-%g" a b c) "EXACT"
      (fun () -> contains (Pent.area_I (m a) (m b) (m c)) area))
    [(3.,4.,5.,6.);(5.,12.,13.,30.);(8.,15.,17.,60.);(7.,24.,25.,84.)];
  check "area.permutation" "CONTRACT" (fun () -> overlaps (Pent.area_I (m 2.) (m 3.) (m 4.)) (Pent.area_I (m 4.) (m 2.) (m 3.)));
  check "area.scale-by-two" "CONTRACT" (fun () -> overlaps (Pent.area_I (m 4.) (m 6.) (m 8.)) Pent.(four * area_I (m 2.) (m 3.) (m 4.)));
  check "angle.right" "CONTRACT" (fun () -> overlaps (Pent.iarc (m 3.) (m 4.) (m 5.)) Pent.pi2);
  check "cosine-law.right" "CONTRACT" (fun () -> contains (Pent.iloc (m 3.) (m 4.) Pent.pi2) 5.);
  check "split.parent-covered" "CONTRACT" (fun () ->
    let a,b=Pent.splitlist 1.e-8 [mk (-1.) 1.;mk 2. 2.5] in
    List.for_all (fun x -> List.exists (fun box -> contains (List.hd box) x) [a;b]) [-1.;-0.5;0.;0.5;1.] &&
    List.for_all (fun box -> both (List.nth box 1) 2. 2.5) [a;b]);
  check "split.minimum-width-fails" "CONTRACT" (fun () -> raises_failure(fun()->Pent.splitlist 1.e-8 [m 0.]));
  check "recursion-unresolved-never-passes" "CONTRACT" (fun () -> raises_failure(fun()->Pent.recursetoeps (fun _->false) [[m 0.]]));
  check "recursion-counts-work" "CONTRACT" (fun () -> Pent.recursetoeps (fun _->true) [[m 1.];[m 2.]] = (2,true));
  List.iter (fun (a,b) ->
    check (Printf.sprintf "periodize.%g.%g" a b) "CONTRACT" (fun () ->
      let out=Pet.periodize1 (mk a b) in
      List.for_all (fun t -> member (t-.floor t) out) [a; (a+.b)/.2.;b]))
    [(3.25,3.5);(3.75,4.25);(-3.75,-3.25);(-1.,0.);(0.,0.);(0.,2.)];
  check "periodize.full-cover" "EXACT" (fun () -> match Pet.periodize1(mk (-2.) 2.) with [x]->same x(mk 0. 1.)|_->false);
  check "periodize.endpoint" "EXACT" (fun () -> member 0. (Pet.periodize1(m 1.)));
  check "getint.unique" "EXACT" (fun () -> match Pent.getint(mk 1.9 2.1) with Some x->same x(m 2.)|_->false);
  check "getint.ambiguous" "CONTRACT" (fun () -> raises_unstable(fun()->Pent.getint(mk 1. 2.)))

let boundaries () =
  (* Calls the helper used in BOTH real precluster2 case predicates. *)
  List.iter (fun (id,ab,bc,ac) ->
    check ("C014."^id) "CONTRACT" (fun () -> not(pseudo2_boundary_excluded (m ab) (m bc) (m ac))))
    [("contact-shared",1.75,1.7,1.75);("contact-other",1.74,1.7,1.7);
     ("short-contact-missing-tie",1.75,1.75,1.7);("contact-1.8",1.74,1.7,1.8);
     ("other-1.8",1.74,1.8,1.7);("all-equal",1.75,1.75,1.75)];
  check "C014.strictly-off-boundaries" "CONTRACT" (fun () -> pseudo2_boundary_excluded (m 1.74) (m 1.77) (m 1.7));
  check "C014.straddling-1.8" "CONTRACT" (fun () -> not(pseudo2_boundary_excluded(m 1.74)(m 1.77)(mk 1.79 1.81)));
  check "C014.touching-length-intervals" "CONTRACT" (fun () -> not(pseudo2_boundary_excluded(mk 1.72 1.75)(m 1.77)(mk 1.75 1.76)));
  let (fn,_) = init2Cps_precluster6 in
  let (_,_,out,_,_) = fn in
  let edge l = (l,Pent.zero,Pent.zero,Pent.zero) in
  let fixture a = (a,edge(m 1.7),edge(m 1.7),edge(m 1.9)) in
  let cap=Pent.(aK+two*epsM_I) in
  check "C013.old-new-cap-band" "CONTRACT" (fun () -> not(out(fixture Pent.(aK+rat 3 2*epsM_I))));
  check "C013.new-cap-equality" "CONTRACT" (fun () -> not(out(fixture cap)));
  check "C013.straddling-cap" "CONTRACT" (fun () -> not(out(fixture(mk (cap.low-.0.001) (cap.high+.0.001)))));
  check "C013.strictly-above-cap" "CONTRACT" (fun () -> out(fixture(m (cap.high+.0.001))));
  check "C013.expanded-still-below-epsN" "CONTRACT" (fun () -> Pent.(cap << aK+epsN_I));
  (* Mutation witnesses: the old clause rejects the newly admitted band and tie.
     No production source mutation is performed by these assertion tests. *)
  check "mutation.C013-old-cap-detected" "CONTRACT" (fun () -> Pent.(aK+rat 3 2*epsM_I >> aK+epsM_I));
  check "mutation.C014-old-filter-detected" "CONTRACT" (fun () -> Pent.disjoint_I(m 1.75)(m 1.7) && Pent.disjoint_I(m 1.75)(m 1.7))

let derivatives () =
  let open Autodiff in
  let x=(m 2.,m 1.,m 0.) in
  let y=Autodiff.(x *^^ x *^^ x) in
  let a,b,c=y in
  check "AD.cube-value" "EXACT" (fun () -> contains a 8.);
  check "AD.cube-first" "EXACT" (fun () -> contains b 12.);
  check "AD.cube-second" "EXACT" (fun () -> contains c 12.);
  let a,b,c=Autodiff.(oneD2 /^^ x) in
  check "AD.reciprocal-value" "EXACT" (fun () -> contains a 0.5);
  check "AD.reciprocal-first" "EXACT" (fun () -> contains b (-0.25));
  check "AD.reciprocal-second" "EXACT" (fun () -> contains c 0.25);
  let a,b,c=sqrtD2(m 4.,m 1.,m 0.) in
  check "AD.sqrt-value" "EXACT" (fun () -> contains a 2.);
  check "AD.sqrt-first" "EXACT" (fun () -> contains b 0.25);
  check "AD.sqrt-second" "EXACT" (fun () -> contains c (-1./.32.));
  let a,b,c=sinD2(m 0.,m 1.,m 0.) in
  check "AD.sin-at-zero" "EXACT" (fun () -> contains a 0. && contains b 1. && contains c 0.);
  let a,b,c=cosD2(m 0.,m 1.,m 0.) in
  check "AD.cos-at-zero" "EXACT" (fun () -> contains a 1. && contains b 0. && contains c (-1.));
  List.iter (fun (name,f) -> check ("AD.original."^name) "DIAGNOSTIC" f) diagnostic_tests;
  List.iter (fun t ->
    add (Printf.sprintf "Gamma.identity.t=%g" t) "CONTRACT" (fun () ->
      let xx=Pent.(sigma+m t) in
      let xxD=(xx,Pent.one,Pent.zero) in
      let yyD=Autodiff.(twoD2 *^^ sigmaD2 -^^ xxD) in
      let f z=let a,b,c=shared_pinwheeledgeD2 zeroD2 pi15D2 z in area_D2 a b c in
      let value,d1,d2=Autodiff.(f xxD +^^ f yyD) in
      let expected=Pent.(two*aK+sigma*m t*m t) in
      demand "Gamma value mismatch" (overlaps value expected);
      demand "Gamma first derivative mismatch" (overlaps d1 Pent.(two*sigma*m t));
      demand "Gamma second derivative mismatch" (overlaps d2 Pent.(two*sigma));
      demand "Gamma second derivative not positive" Pent.(d2 >> zero)))
    [-0.01;-0.005;0.;0.005;0.01]

let geometry () =
  check "pair.well-separated" "CONTRACT" (fun () -> Pet.pet (m 3.) (m 0.2) (m (-0.3)));
  check "pair.inscribed-disks-overlap" "CONTRACT" (fun () -> not(Pet.pet(m 1.)(m 0.)(m 0.)));
  check "pair.exchange-symmetry" "CONTRACT" (fun () -> Pet.pet(m 1.9)(m 0.2)(m (-0.3)) = Pet.pet(m 1.9)(m (-0.3))(m 0.2));
  check "pair.reflection-symmetry" "CONTRACT" (fun () -> Pet.pet(m 1.9)(m 0.2)(m (-0.3)) = Pet.pet(m 1.9)(m (-0.2))(m 0.3));
  check "banana.curve-II-roundtrip" "CONTRACT" (fun () -> contains (Banana.curveIIt (Banana.curveIIth(m 0.1))) 0.1);
  check "banana.critical-both-extrema" "CONTRACT" (fun () ->
    let pts=Banana.critical_points_banana(mk (-0.2) 0.7,mk 1.6 2.1) in
    let has (x,y)=List.exists(fun(a,b)->overlaps a x && overlaps b y)pts in
    has (Pent.(pi15-Banana.theta'ks),Banana.ks) && has(Pent.zero,Pent.two));
  check "danana.critical-both-extrema" "CONTRACT" (fun () ->
    let pts=Banana.critical_points_danana(mk 0. 1.4,mk 1.6 2.1) in
    let has (x,y)=List.exists(fun(a,b)->overlaps a x && overlaps b y)pts in
    has(Pent.pi15,Pent.(two*kappa)) && has(Pent.pi310,Pent.(sqrt_I(two*(one+kappa)))));
  List.iter (fun (x,alpha) ->
    add (Printf.sprintf "contact.independent-length.%g.%g" x alpha) "DIAGNOSTIC" (fun () ->
      let d=Pent.ellx (m x) (m alpha) in
      let k=cos(Float.pi/.5.) and s=sin(Float.pi/.5.) in
      let h=s-.x and psi=alpha+.3.*.Float.pi/.10. in
      let reference=sqrt(1.+.h*.h+.k*.k-.2.*.h*.cos psi+.2.*.k*.sin psi) in
      demand "Direct vertex displacement disagrees" (abs_float(scalar d-.reference)<1.e-10)))
    [(0.1,0.2);(0.5,0.6);(0.8,1.);(0.2,0.);(0.6,Float.pi/.5.)];
  (* Symmetry uses the actual standard contact coordinates and common constants. *)
  List.iter (fun (x,a) -> check (Printf.sprintf "contact.reflection.%g.%g" x a) "CONTRACT" (fun () ->
    overlaps (Pent.ellx(m x)(m a)) Pent.(ellx(two*sigma-m x)(pi25-m a)))) [(0.2,0.3);(0.5,0.7);(0.9,1.)];
  check "fillout6D.separated-equilateral" "DIAGNOSTIC" (fun () ->
    match Banana.fillout6D ((m 3.,m 0.1,m 0.2),(m 3.,m 0.3),m 3.) with
    | None -> false
    | Some(a,_,_,_) -> abs_float(scalar a -. 9.*.sqrt 3./.4.)<1.e-10);
  (* A lower bound is not an enclosure of each represented triangle's area.
     This exact fixture uses lower sides (3,4,5), but the represented nonobtuse
     triangle (3.5,4.5,5.5) has strictly greater area. No tolerance is used. *)
  check "area.lower-bound-need-not-overlap-point-area" "CONTRACT" (fun () ->
    let lower = Pent.areamin_acute (mk 3. 3.5) (mk 4. 4.5) (mk 5. 5.5) in
    let point_area = Pent.area_I (m 3.5) (m 4.5) (m 5.5) in
    same lower (m 6.) && valid point_area && lower.high < point_area.low);
  (* The ice-ray witness tests fillout2C's actual
     lower-area contract. Its returned area uses the three LOWER side endpoints;
     it is not required to overlap the exact ice-ray area. Check the independently
     simplified side lengths and the full-side area enclosure separately. *)
  add "fillout2C.ice-ray-witness" "CONTRACT" (fun () ->
    let show name x =
      Printf.printf "ICE-RAY WITNESS %s = %s\n%!" name
        (I.to_string ~fmt:"%.17g" x)
    in
    let finite x = valid x && Float.is_finite x.low && Float.is_finite x.high in
    let encloses x y = finite x && finite y && x.low <= y.low && y.high <= x.high in
    let e1 = Pent.ellthetax Pent.sigma Pent.zero in
    let e2 = Pent.ellthetax_sgn Pent.(sigma/(two*kappa)) Pent.zero false in
    match Banana.fillout2C (mk 1.8 1.82) e1 e2 with
    | None -> failwith "fillout2C discarded the ice-ray witness (returned None)"
    | Some (lower,(ab,_,_,_), (bc,_,_,_), (ac,_,_,_)) ->
      let expected_ab = Pent.(sqrt_I (four*kappa*kappa + sigma*sigma)) in
      let expected_bc = Pent.(sqrt_I (int 11) / two) in
      let expected_ac = Pent.(one+kappa) in
      List.iter (fun (name,x) -> show name x)
        [("AB",ab); ("AB reference",expected_ab);
         ("BC",bc); ("BC reference",expected_bc);
         ("AC",ac); ("AC reference",expected_ac);
         ("returned area lower bound",lower); ("exact-area enclosure aK",Pent.aK)];
      demand "AB interval did not contain the independent ice-ray length enclosure"
        (encloses ab expected_ab);
      demand "BC interval did not contain sqrt(11)/2's enclosure"
        (encloses bc expected_bc);
      demand "AC interval did not contain (1+kappa)'s enclosure"
        (encloses ac expected_ac);
      let full_area = Pent.area_I ab bc ac in
      show "area evaluated on full side intervals" full_area;
      demand "Full-side area interval did not contain the exact-area enclosure aK"
        (encloses full_area Pent.aK);
      demand "Returned lower-area interval is unordered or nonfinite" (finite lower);
      (* aK.low <= exact area. This sufficient comparison certifies the returned
         LOWER endpoint without enlarging either interval or adding a tolerance.
         If rounding prevents it, fail explicitly rather than asserting a pass. *)
      demand "Could not certify returned lower endpoint <= aK.low; inspect printed intervals"
        (lower.low <= Pent.aK.low))

let mitm () =
  List.iter (fun x -> check (Printf.sprintf "keys.singleton.%g" x) "CONTRACT" (fun () ->
    let ks=Meet.make_a_key(m 0.25)(m x) in ks<>[] && List.mem (int_of_float(floor(x/. 0.25))) ks)) [-1.;-0.25;0.;0.25;1.];
  List.iter (fun x -> check (Printf.sprintf "keys.touching.%g" x) "CONTRACT" (fun () ->
    let a=Meet.make_a_key(m 0.25)(mk (x-. 0.25) x) and b=Meet.make_a_key(m 0.25)(mk x (x+. 0.25)) in
    List.exists (fun k->List.mem k b) a)) [-1.;-0.25;0.;0.25;1.];
  check "keys.edge-inversion" "CONTRACT" (fun () ->
    let l=mk 1.7 1.8 and a=mk 0.1 0.2 and b=mk (-0.3) (-0.2) in
    let k=Meet.key_invert(m 0.1)(l,a,b) and h=Meet.keys_of_edge(m 0.1)(l,Pent.(-a),Pent.(-b)) in
    List.sort_uniq compare k = List.sort_uniq compare h);
  check "keys.periodic-edge" "CONTRACT" (fun () ->
    let l=m 1.75 and t=m 0.2 and u=m (-0.3) in
    let a=Meet.keys_of_edge(m 0.1)(l,t,u) and b=Meet.keys_of_edge(m 0.1)(l,Pent.(t+pi25),u) in
    List.exists(fun k->List.mem k b)a);
  check "subdivision.cover" "CONTRACT" (fun () ->
    let boxes=Meet.subdivide_subwidth(m 0.25)[mk 0. 1.;mk (-0.5) 0.5] in
    List.for_all(fun x->List.for_all(fun y->List.exists(fun b->contains(List.nth b 0)x && contains(List.nth b 1)y)boxes)[-0.5;-0.25;0.;0.25;0.5])[0.;0.25;0.5;0.75;1.]);
  check "subdivision.singleton" "CONTRACT" (fun () -> Meet.subdivide_subwidth(m 0.25)[m 1.] <> []);
  check "hash.minimum-and-collision" "CONTRACT" (fun () ->
    let h=Hashtbl.create 5 in
    Meet.update_one_perihash h ([],[1],m 3.);
    Meet.update_one_perihash h ([],[1;2],m 2.);
    match Meet.minarea h [1;2] with Some a->same a(m 2.)|_->false);
  check "hash.recut-takes-maximum" "CONTRACT" (fun () ->
    let h=Hashtbl.create 5 in Hashtbl.add h 1 (m 1.,None);
    Meet.recut h 2. 1; Meet.recut h 3. 1; Meet.recut h 1. 1;
    Meet.maxcut h [1]=Some 3.);
  check "hash.absent-key-not-zero" "CONTRACT" (fun () -> let h=Hashtbl.create 2 in Meet.minarea h [42]=None);
  (* Exhaustive finite fixtures exercise actual central pruning and recut. *)
  List.iter (fun (a,b,c,target) ->
    let id=Printf.sprintf "MITM.finite.%g.%g.%g.%g" a b c target in
    check id "EXACT" (fun () ->
      let h=Hashtbl.create 5 in
      Hashtbl.add h 11 (m b,None);Hashtbl.add h 12 (m c,None);
      let fn=((),(fun () _->Some(m a)),(fun _->false),(fun x->x),[(fun _ _->[11]);(fun _ _->[12])]) in
      let survivors=Meet.mk_one_cencoord(m 0.5)(m target)(Some h)fn([m 0.],10.) in
      let feasible=a+.b+.c <= target in
      demand "Finite exhaustive oracle differs" ((survivors<>[])=feasible);
      if feasible then (
        demand "Feasible peripheral b was overcut" (match Meet.maxcut h [11] with Some cut->cut>=b|_->false);
        demand "Feasible peripheral c was overcut" (match Meet.maxcut h [12] with Some cut->cut>=c|_->false));true))
    [(0.5,0.5,0.5,1.5);(0.5,0.5,0.5,2.);(1.,0.5,0.5,1.5);(0.25,0.5,0.75,1.5);(0.25,0.75,0.75,1.5);(1.,1.,1.,3.)];
  check "MITM.unstable-is-not-empty" "CONTRACT" (fun () ->
    let fn=((),(fun () _->raise Unstable),(fun _->false),(fun x->x),[]) in
    raises_failure(fun()->Meet.mk_one_cencoord(m 0.5)(m 2.)None fn([m 0.],3.)));
  check "MITM.feasible-does-not-exhaust" "CONTRACT" (fun () ->
    let fn=((),(fun () _->Some(m 1.)),(fun _->false),(fun x->x),[]) in
    raises_failure(fun()->Meet.mitm_recursion 0 false (m 2.) (m 0.5) None fn [([m 0.],2.)]));
  check "MITM.impossible-exhausts" "CONTRACT" (fun () ->
    let fn=((),(fun () _->Some(m 3.)),(fun _->false),(fun x->x),[]) in
    Meet.mitm_recursion 0 false (m 2.) (m 0.5) None fn [([m 0.],4.)])

(* A reference polygon construction and separating-axis test. This uses ordinary
   floating arithmetic and a margin, so it is DIAGNOSTIC, never a certificate. *)
let vertices cx cy angle = Array.init 5 (fun j -> let a=angle+.float j*.2.*.Float.pi/.5. in cx+.cos a,cy+.sin a)
let dot (x,y) (u,v) = x*.u+.y*.v
let separation a b =
  let best=ref neg_infinity in
  Array.iter (fun p -> for i=0 to 4 do
    let x,y=p.(i) and u,v=p.((i+1) mod 5) in
    let axis=(y-.v,u-.x) in
    let project poly=let xs=Array.map(fun pt->dot pt axis)poly in
      Array.fold_left min infinity xs,Array.fold_left max neg_infinity xs in
    let al,ah=project a and bl,bh=project b in
    best:=max !best (max (bl-.ah)(al-.bh))
  done) [|a;b|];!best
let extended () =
  add "generated.pair-SAT-no-false-exclusion" "DIAGNOSTIC" (fun () ->
    let rng=Random.State.make[|2016;2026;13|] in let accepted=ref 0 in
    for i=1 to 3000 do
      let d=1.62+.Random.State.float rng 0.55 in
      let t=Random.State.float rng (2.*.Float.pi/.5.)-.Float.pi/.5. in
      let u=Random.State.float rng (2.*.Float.pi/.5.)-.Float.pi/.5. in
      let a=vertices 0. 0. t and b=vertices d 0. (Float.pi-.u) in
      if separation a b > 1.e-7 then (
        incr accepted;
        demand (Printf.sprintf "SAT witness %d d=%.17g t=%.17g u=%.17g" i d t u)
          (Pet.pet(mk (d-.1.e-12)(d+.1.e-12))(mk(t-.1.e-12)(t+.1.e-12))(mk(u-.1.e-12)(u+.1.e-12))))
    done;
    Printf.printf "SAT separated witnesses checked: %d; seed=2016,2026,13\n%!" !accepted;
    demand "Too few generated witnesses" (!accepted >= 100));
  add "generated.closed-key-cover" "CONTRACT" (fun () ->
    let rng=Random.State.make[|2026;14|] in
    for i=1 to 2000 do
      let p=float(Random.State.int rng 65-32)/.16. in
      let l=float(Random.State.int rng 16)/.16. and r=float(Random.State.int rng 16)/.16. in
      let ks1=Meet.make_a_key(m 0.125)(mk(p-.l)p) and ks2=Meet.make_a_key(m 0.125)(mk p(p+.r)) in
      demand (Printf.sprintf "Common point lost at fixture %d" i) (List.exists(fun k->List.mem k ks2)ks1)
    done);
  add "generated.nonobtuse-area-lower-bound" "DIAGNOSTIC" (fun () ->
    let rng=Random.State.make[|2026;15|] in let n=ref 0 in
    for _i=1 to 2000 do
      let a=1.62+.Random.State.float rng 0.4 and b=1.62+.Random.State.float rng 0.4 and c=1.62+.Random.State.float rng 0.4 in
      if a*.a+.b*.b>=c*.c && a*.a+.c*.c>=b*.b && b*.b+.c*.c>=a*.a then (
        let x=mk(a-.0.01)(a+.0.01) and y=mk(b-.0.01)(b+.0.01) and z=mk(c-.0.01)(c+.0.01) in
        let s=(a+.b+.c)/.2. in let reference=sqrt(s*.(s-.a)*.(s-.b)*.(s-.c)) in
        let lower=Pent.areamin_acute x y z in
        demand "Area lower bound exceeds independent Heron diagnostic" (lower.low <= reference+.1.e-12);incr n)
    done;
    demand "No acute fixtures" (!n>100))

let run with_generated =
  rows := []; core();boundaries();derivatives();geometry();mitm();
  if with_generated then extended();
  let cases=List.rev !rows in
  let ids=List.map(fun(id,_,_)->id)cases in
  demand "Duplicate test ID" (List.length ids=List.length(List.sort_uniq compare ids));
  demand "Empty test suite" (List.length cases>100);
  let failures=ref [] in
  List.iter(fun(id,kind,f)->
    let start=Sys.time() in
    try f();Printf.printf "TEST PASS [%s] %s (%.6fs)\n%!" kind id (Sys.time()-.start)
    with exn -> failures:=(id,Printexc.to_string exn)::!failures;
      Printf.printf "TEST FAIL [%s] %s: %s\n%!" kind id (Printexc.to_string exn))cases;
  Printf.printf "TEST SUMMARY: total=%d; passed=%d; failed=%d; generated=%b\n%!"
    (List.length cases)(List.length cases-List.length !failures)(List.length !failures)with_generated;
  if !failures<>[] then failwith "Function-contract suite failed; inspect individual TEST FAIL lines"
end;;
