(* COMPUTATION GJULAOH: see docs/CALCULATIONS.md and docs/TESTING.md. *)
(* Function-contract tests for contact-sign geometry. These are not the four range proofs.
   Exact interval-boundary checks are distinguished from consistency checks
   against the older contact-distance formula. No tolerance padding is used. *)
module SqueezeTests = struct
  module S = SqueezeSign
  module I = Interval_crlibm.I
  let run () =
    let passed=ref 0 in
    let check name condition =
      if not condition then failwith ("Squeeze test failed: " ^ name);
      incr passed; Printf.printf "TEST PASS: %s\n%!" name in
    let failure_with_prefix prefix f =
      try f (); false with Failure message ->
        String.length message >= String.length prefix &&
        String.sub message 0 (String.length prefix) = prefix in
    let z=S.zero and o=S.one in
    check "strict positive excludes zero" (not (S.positive z));
    check "strict negative excludes zero" (not (S.negative z));
    check "strict positive excludes straddling interval" (not (S.positive (S.box (-1.) 1.)));
    check "closed endpoint contact is not disjoint"
      (not (S.below (S.box 0. 1.) (S.box 1. 2.)));
    check "square crosses zero without negative lower bound"
      (let q=S.square (S.box (-2.) 3.) in q.low=0. && q.high>=9.);
    check "square of negative interval covers both endpoints"
      (let q=S.square (S.box (-3.) (-2.)) in S.contains q 4. && S.contains q 9.);
    check "area cap is stronger-domain acrit+epsN, not amin+epsN"
      (S.above S.area_cap Pent.aK);
    check "five discrete relative rotations" (Array.length S.rotations=5);
    check "four pointer-direction jobs" (List.length S.case_names=4);
    check "determinant orientation" (S.positive (S.det (o,z) (z,o)));
    check "opposite determinant orientation" (S.negative (S.det (z,o) (o,z)));
    check "quarter-turn" (let x,y=S.quarter_turn (o,z) in S.contains x 0. && S.contains y 1.);
    let horizontal = {S.center=(z,z); from_b_normal=(z,o); orientation=z} in
    let other = {S.center=(o,z); from_b_normal=(o,o); orientation=z} in
    check "zero slope/normal component does not pass strict sign test"
      (not (S.correct_contact_signs horizontal other));
    check "identical pentagons have strict interior overlap" (S.strict_overlap horizontal horizontal);
    let displaced = {horizontal with S.center=(S.point 3.,z)} in
    check "separated pentagons not certified overlapping" (not (S.strict_overlap horizontal displaced));
    let shifted = {horizontal with S.center=(S.point 0.25,z)} in
    check "nearby equal-oriented pentagons overlap" (S.strict_overlap horizontal shifted);
    (* A direct contact is a boundary, not strict overlap. This exercises both
       role charts and their endpoint conventions against actual vertex axes. *)
    List.iter (fun b_points ->
      List.iter (fun u -> List.iter (fun v ->
        let q=S.contact b_points (S.point u) (S.point v) in
        let key=Printf.sprintf "%b/%.3f/%.3f" b_points u v in
        check ("manufactured B-neighbor contact not rejected as overlap " ^ key)
          (not (S.strict_overlap horizontal q));
        (* Qualify only the multiplication operator, not its arguments:
           a local I.(...) would shadow the float v with the constructor I.v. *)
        let x = I.( * ) (I.( * ) Pent.two Pent.sigma) (I.singleton u) in
        let alpha = I.( * ) Pent.pi25 (I.singleton v) in
        let old_distance=Pent.ellx x alpha in
        let new_distance=I.sqrt (S.norm2 q.S.center) in
        check ("distance consistency with Section A.1 ellx " ^ key)
          (S.meets old_distance new_distance)
      ) [0.25;0.5;0.75]) [0.125;0.5;0.875]
    ) [true;false];
    (* Slider and vertex endpoints are intentionally INCLUDED, not discarded
       by an open initial box. These tests do not invoke old inverse trig. *)
    List.iter (fun b_points -> List.iter (fun u -> List.iter (fun v ->
      let q=S.contact b_points (S.point u) (S.point v) in
      check (Printf.sprintf "closed contact-chart endpoint %b %.0f %.0f" b_points u v)
        (not (S.strict_overlap horizontal q))
    ) [0.;1.]) [0.;1.]) [true;false];
    let witnesses = [
      ("BA_BC",1,[|0.;0.5;0.;0.|]);
      ("BA_CB",0,[|0.;0.5;0.;0.|]);
      ("AB_BC",2,[|0.;0.;0.;0.|]);
      ("AB_CB",1,[|0.;0.;0.;0.5|])
    ] in
    List.iter (fun (name,m,values) ->
      let ba,bc=S.case_flags name in
      let xs=Array.map S.point values in
      let a=S.contact ba xs.(0) xs.(1) in
      let c=S.rotate_contact m (S.contact bc xs.(2) xs.(3)) in
      check ("signed contact witness " ^ name) (S.correct_contact_signs a c);
      check ("witness reaches conclusion branch " ^ name)
        (S.classify ba bc m xs=Some S.Contact_signs)
    ) witnesses;
    let parent=Array.make 4 (S.box 0. 1.) in
    let l,r=S.split parent in
    check "closed bisection covers parent and shared midpoint"
      (l.(0).low=0. && l.(0).high=r.(0).low && r.(0).high=1. &&
       l.(1)=parent.(1) && r.(1)=parent.(1) && parent.(0).high=1.);
    check "width exhaustion is a failure, not exclusion"
      (failure_with_prefix "Unresolved at subdivision limit"
        (fun () -> ignore(S.split (Array.make 4 (S.point 0.5)))));
    check "node limit is incomplete, not success"
      (failure_with_prefix "Unresolved: requested node limit"
        (fun () -> ignore(S.verify_case ~max_nodes:1 "BA_BC")));
    if !passed <> 71 then failwith "Expected all 71 supplement checks to execute";
    Printf.printf "SQUEEZE TEST SUMMARY: %d passed; 0 failed\n%!" !passed
end;;
