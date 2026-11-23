(* A geometric positive control for the released MITM machinery.
   It represents two actual Gamma triangles on opposite sides of AC.
   The two triangles are encoded separately in the two-contact chart with
   parameters sigma+t and sigma-t. Their centers and side lengths are
   constructed independently below as a geometric check of that encoding.
   The test target is 3, deliberately above the known pair area. This is
   a retention test, NOT a counterexample to the packing inequality.

   No production source or key function is redefined. No unbounded search
   is run on a feasible input: two actual matching/pruning rounds suffice.
*)
module Review_positive_control = struct
  open Pent

  let run () =
    let assertions = ref 0 in
    let check name condition =
      Stdlib.incr assertions;
      if condition then Printf.printf "CONTROL PASS: %s\n%!" name
      else failwith ("Geometric positive control failed: " ^ name)
    in
    let nonempty xs = match xs with [] -> false | _ -> true in
    let common xs ys = List.exists (fun x -> List.mem x ys) xs in
    (* Fixed pentagon orientations: A,C have a vertex in the positive
       x direction; B,D have the opposite orientation. The rational shear
       is nonzero so the reflected edge angles are distinguishable. *)
    let t = 1 // 200 in
    let ell0 = one + kappa in
    let height0 = int 3 * kappa * sigma in
    let ab0sq = four*kappa*kappa + sigma*sigma in
    let bc0sq = four*kappa*kappa + (sigma/(two*kappa))*(sigma/(two*kappa)) in
    let x0 = (ab0sq - bc0sq + ell0*ell0)/(two*ell0) in
    let bx = x0 - sigma*t and by = height0 + kappa*t in
    let cx = ell0 and cy = t in
    let dx = x0 + sigma*t and dy = -height0 + kappa*t in
    let dab = sqrt_I (bx*bx + by*by) in
    let dbc = sqrt_I ((cx-bx)*(cx-bx) + (by-cy)*(by-cy)) in
    let dac = sqrt_I (cx*cx + cy*cy) in
    let xc = sigma + t in
    let cc = [xc; zero; xc/(two*kappa); zero] in
    let xp = sigma - t in
    let pc = [xp; zero; xp/(two*kappa); zero] in
    let central_area = (by*cx-bx*cy)/two in
    let peripheral_area = (dx*cy-dy*cx)/two in
    let target = int 3 in
    check "the constructed pair is below the test target 3"
      (central_area+peripheral_area << target);
    check "the peripheral is subcritical"
      (peripheral_area << aK);
    check "the shear is strictly nonzero" (t >> zero);
    let pfill () xs = Banana.mk2C d_subcrit_shared (xs,(true,false)) in
    let unwrap name = function Some x -> x | None -> failwith (name ^ " lost the known configuration") in
    let pf = unwrap "two-contact reconstruction" (pfill () pc) in
    let cf = unwrap "central two-contact reconstruction" (pfill () cc) in
    let (_,_,_,(psh,_,_,_)) = pf in
    let (_,(cab,_,_,_),(cbc,_,_,_),(csh,_,_,_)) = cf in
    check "central side data agree with the independently constructed centers"
      (meet_I cab dab && meet_I cbc dbc && meet_I csh dac);
    check "both independently reconstructed shared lengths enclose the geometric length"
      (meet_I psh dac && meet_I csh dac);
    let (extra,_,pout,parea,pkeys),_ = init2Cps in
    check "the production peripheral predicate retains the witness" (not (pout pf));
    let pfn = (extra,pfill,pout,parea,pkeys) in
    let cfn = (unit_extra,pfill,(fun _ -> false),areafn2Ce,[ckeyfn2Ce]) in
    let h = Hashtbl.create 127 in
    let pdata = ref (h,(pfn,[(pc,[],amin)])) in
    let ccs = ref [(cc,target.high)] in
    List.iteri (fun round width ->
      let k_p = pkeys width pf in
      let k_c = ckeyfn2Ce width cf in
      let (_,_,_,(l,ta,tb,_)) = cf in
      let wrong = Meet.keys_of_edge width (l,ta,tb) in
      check "geometric peripheral and inverted central keys collide" (common k_p k_c);
      check "omitting the orientation inversion is detected by this asymmetric fixture"
        (not (common k_p wrong));
      let initialized = Stdlib.(round > 0) in
      let nextp = Meet.mk_peridata initialized width !pdata in
      let hash,(_,surviving_p) = nextp in
      check "actual peripheral construction retains a box" (nonempty surviving_p);
      check "actual central lookup finds peripheral area data"
        (match Meet.periareas width (Some hash) [ckeyfn2Ce] cf with
         | Some ([a],total,[keys]) ->
             nonempty keys && not (a >> peripheral_area) &&
             not (total >> peripheral_area)
         | _ -> false);
      let nextc = Meet.mk_cencoord width target (Some hash) cfn !ccs in
      check "actual central pruning retains the known feasible box" (nonempty nextc);
      (* mk_cencoord updates key cuts through Meet.recut. Peripheral triples
         still store LOWER area bounds; their allowed upper cut is maxcut
         over the compatible keys, not a fabricated field in that triple. *)
      check "propagated peripheral upper cuts retain the actual area"
        (List.for_all (fun (_,keys,_) ->
           match Meet.maxcut hash keys with
           | Some cut -> Stdlib.(cut >= peripheral_area.high)
           | None -> false) surviving_p);
      pdata := nextp;
      ccs := nextc
    ) [1 // 4096; 1 // 8192];
    Printf.printf "GEOMETRIC MITM CONTROL: %d assertions passed; two production pruning rounds.\n%!" !assertions;
    !assertions
end;;
