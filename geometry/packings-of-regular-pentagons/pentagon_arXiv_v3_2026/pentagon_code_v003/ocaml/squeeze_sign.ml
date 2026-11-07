(* COMPUTATION GJULAOH: see docs/CALCULATIONS.md and docs/TESTING.md. *)
(* Contact-line signs for Lemma 6.5 (lemma:squeeze-area).
   Manuscript: pentagon_v005.tex, Section 6.3; contact parameters: Section A.1.

   This module proves a four-dimensional interval exclusion. It does
   not replace squeeze_calc: that calculation supplies the area-derivative
   inequality once the present calculation supplies its positive-slope branch.

   Fix B at the origin with a vertex at (1,0). Each incident contact has two
   real parameters x in [0,2*sigma], alpha in [0,2*pi/5], and one pointer flag.
   The four jobs are the four combinations of flags. In each job all five
   relative pentagonal rotations of C are retained. They are discrete chart
   alternatives, NOT an extra continuous dimension.

   Numerical boxes use u=x/(2*sigma), v=alpha/(2*pi/5) in [0,1]. Bisection
   therefore covers the exact endpoints without rounding an initial rational
   bound inward. Parameter values are converted by interval arithmetic.

   See docs/SQUEEZING.md for the coordinates, the signed-normal criterion,
   and the strict separating-axis overlap test. No tangent, inverse-trig,
   banana enclosure, or meet-in-the-middle pruning is used here.
*)
module SqueezeSign = struct
  module I = Interval_crlibm.I
  type interval = I.t
  type vector = interval * interval
  let ( +$ ) = I.( + )
  let ( -$ ) = I.( - )
  let ( *$ ) = I.( * )
  let neg = I.( ~- )
  let point = I.singleton
  let integer = I.of_int
  let box lo hi : interval =
    if classify_float lo = FP_nan || classify_float hi = FP_nan || lo > hi
    then invalid_arg "unordered or NaN interval";
    Pent.mk lo hi
  let zero = point 0.
  let one = point 1.
  let two = point 2.
  let half = point 0.5
  let pi = Pent.pi
  let delta = Pent.pi15
  let period = Pent.pi25
  let kappa = Pent.kappa
  let sigma = Pent.sigma
  (* IMPORTANT: acrit + epsN, not amin + epsN. *)
  let area_cap = Pent.aK +$ Pent.epsN_I
  let below (x:interval) (y:interval) = x.high < y.low
  let above x y = below y x
  let positive (x:interval) = x.low > 0.
  let negative (x:interval) = x.high < 0.
  let meets (x:interval) (y:interval) = x.low <= y.high && y.low <= x.high
  let contains (x:interval) v = x.low <= v && v <= x.high

  let add (x,y) (u,v) = (x +$ u, y +$ v)
  let sub (x,y) (u,v) = (x -$ u, y -$ v)
  let scale a (x,y) = (a *$ x, a *$ y)
  let quarter_turn (x,y) = (neg y,x)
  let dot (x,y) (u,v) = (x *$ u) +$ (y *$ v)
  let det (x,y) (u,v) = (x *$ v) -$ (y *$ u)
  let unit a = (I.cos a, I.sin a)
  let rotate (x,y) (c,s) = ((c *$ x) -$ (s *$ y), (s *$ x) +$ (c *$ y))
  let square (x:interval) =
    if x.low >= 0. || x.high <= 0. then x *$ x
    else let a = point x.low and b = point x.high in
      box 0. (max (a *$ a).high (b *$ b).high)
  let norm2 (x,y) = square x +$ square y
  let min_center_distance2 = (point 4.) *$ square kappa

  type contact = {
    center : vector;
    from_b_normal : vector; (* outward from B, toward the neighbor *)
    orientation : interval; (* direction of a vertex of that neighbor *)
  }

  (* The parameter convention is EXACTLY Section A.1, not its reflected
     alpha -> 2*pi/5-alpha variant. For B -> X, phi=alpha-pi/5,
     X=(1,0)+kappa*n+(x-sigma)*Jn, orient(X)=alpha+3*pi/5.
     For X -> B, rotate this construction to make the RECEPTOR B have
     orientation zero: n=unit(pi/5), replace (1,0) by unit(2*pi/5-alpha).
     These formulas preserve both the contact segment and the pointer side. *)
  let contact b_points u v =
    let alpha = period *$ v in
    let h = sigma *$ ((two *$ u) -$ one) in
    let n = if b_points then unit (alpha -$ delta) else (kappa,sigma) in
    let first = if b_points then (one,zero) else unit (period -$ alpha) in
    let center = add (add first (scale kappa n)) (scale h (quarter_turn n)) in
    let orientation =
      if b_points then alpha +$ (integer 3 *$ delta)
      else (pi +$ period) -$ alpha in
    {center; from_b_normal=n; orientation}

  let rotations = Array.init 5 (fun m -> unit (integer m *$ period))
  let rotate_contact m c =
    if m < 0 || m >= 5 then invalid_arg "rotation index";
    {center=rotate c.center rotations.(m);
     from_b_normal=rotate c.from_b_normal rotations.(m);
     orientation=c.orientation +$ (integer m *$ period)}

  (* With g=C-A, e=g/|g|, f=Je, B is above AC iff det(A,C)>0.
     The contact-line slopes are (n.g)/det(n,g). Its B-facing normal
     is -n, with f-component det(n,g)/|g|. Thus the four strict
     inequalities below prove BOTH signed slopes and BOTH upper-side claims.
     No division is performed: zero and vertical boundaries cannot pass. *)
  let signed_components a c =
    let g = sub c.center a.center in
    (neg (dot a.from_b_normal g), det a.from_b_normal g,
     dot c.from_b_normal g, det c.from_b_normal g)
  let correct_contact_signs a c =
    let p,q,r,s = signed_components a c in
    positive p && positive q && positive r && positive s

  (* Bounds for min/max of the five vertex projections along an axis.
     The angle is (polygon orientation - axis direction). The minimum's
     upper bound and maximum's lower bound are needed to CERTIFY overlap. *)
  let vertex_support angle =
    let values = Array.init 5 (fun j -> I.cos (angle +$ (integer j *$ period))) in
    let lo_min = ref infinity and hi_min = ref infinity in
    let lo_max = ref neg_infinity and hi_max = ref neg_infinity in
    Array.iter (fun (x:interval) ->
      lo_min := min !lo_min x.low; hi_min := min !hi_min x.high;
      lo_max := max !lo_max x.low; hi_max := max !hi_max x.high) values;
    (box !lo_min !hi_min, box !lo_max !hi_max)

  (* Along each outward edge normal a regular pentagon's own projection
     interval, relative to its center, is [-1,kappa]. For the other pentagon,
     add the center separation to its projected vertex min/max. Strict
     overlap on ALL ten edge axes certifies intersection of the interiors.
     Failure to certify overlap means unresolved, never separation. *)
  let strict_overlap a c =
    let axes_overlap owner other =
      let displacement = sub other.center owner.center in
      let rec loop j =
        if j = 5 then true else
        let angle = (owner.orientation +$ delta) +$ (integer j *$ period) in
        let projected = dot displacement (unit angle) in
        let lo,hi = vertex_support (other.orientation -$ angle) in
        if below (projected +$ lo) kappa && above (projected +$ hi) (neg one)
        then loop (j+1) else false in
      loop 0 in
    axes_overlap a c && axes_overlap c a

  type reason = Orientation | Short_AC | Obtuse | Area | Contact_signs | Overlap
  let reason_index = function
    | Orientation -> 0 | Short_AC -> 1 | Obtuse -> 2
    | Area -> 3 | Contact_signs -> 4 | Overlap -> 5
  let reason_names = [|"orientation";"AC shorter than 2*kappa";"obtuse triangle";
                       "area above acrit+epsN";"both contact signs proved";
                       "A and C interiors overlap"|]

  (* Apart from choosing the positive orientation, the classifier uses an
     inexpensive-to-expensive rejection order. Equality is retained by the geometric
     exclusions. The Contact_signs branch establishes the desired conclusion;
     all other branches exclude the input from the lemma's hypotheses. *)
  let classify b_to_a b_to_c m xs =
    if Array.length xs <> 4 then invalid_arg "four parameters required";
    let a = contact b_to_a xs.(0) xs.(1) in
    let c = rotate_contact m (contact b_to_c xs.(2) xs.(3)) in
    let g = sub c.center a.center in
    let twice_area = det a.center c.center in
    if twice_area.high <= 0. then Some Orientation
    else if below (norm2 g) min_center_distance2 then Some Short_AC
    else if negative (dot a.center c.center) ||
            negative (dot a.center (sub a.center c.center)) ||
            negative (dot c.center g) then Some Obtuse
    else if above (half *$ twice_area) area_cap then Some Area
    else if correct_contact_signs a c then Some Contact_signs
    else if strict_overlap a c then Some Overlap
    else None

  let case_flags = function
    | "BA_BC" -> (true,true)
    | "BA_CB" -> (true,false)
    | "AB_BC" -> (false,true)
    | "AB_CB" -> (false,false)
    | s -> invalid_arg ("unknown pointer case: " ^ s)
  let case_names = ["BA_BC";"BA_CB";"AB_BC";"AB_CB"]
  let show_interval (x:interval) = Printf.sprintf "[%.17g,%.17g]" x.low x.high
  let show_box xs = String.concat "; " (Array.to_list (Array.map show_interval xs))

  (* Split a closed box into two closed children with the SAME stored
     midpoint. Their union is the parent, including their common boundary. *)
  let split (xs:interval array) =
    let j = ref 0 in
    for k=1 to 3 do
      if xs.(k).high -. xs.(k).low > xs.(!j).high -. xs.(!j).low then j:=k
    done;
    let x=xs.(!j) in
    let mid=x.low +. (x.high -. x.low) *. 0.5 in
    if x.high -. x.low <= 1.0e-8 || mid <= x.low || mid >= x.high then
      failwith ("Unresolved at subdivision limit; normalized box " ^ show_box xs);
    let left=Array.copy xs and right=Array.copy xs in
    left.(!j)<-box x.low mid; right.(!j)<-box mid x.high;
    (left,right)

  type result = { processed:int; splits:int; max_depth:int;
                  reasons:int array; rotation_nodes:int array }
  let verify_case ?(max_nodes=0) name =
    let ba,bc = case_flags name in
    let reasons=Array.make 6 0 and rotation_nodes=Array.make 5 0 in
    let processed=ref 0 and splits=ref 0 and max_depth=ref 0 in
    let started=Sys.time () in
    let rec visit = function
      | [] -> ()
      | (m,depth,xs)::rest ->
        if max_nodes > 0 && !processed >= max_nodes then
          failwith ("Unresolved: requested node limit reached in " ^ name);
        incr processed;
        rotation_nodes.(m)<-rotation_nodes.(m)+1;
        max_depth:=max !max_depth depth;
        if !processed mod 100000 = 0 then
          Printf.printf "PROGRESS %s nodes=%d depth=%d cpu=%.3f\n%!"
            name !processed depth (Sys.time () -. started);
        match classify ba bc m xs with
        | Some reason ->
          let k=reason_index reason in reasons.(k)<-reasons.(k)+1; visit rest
        | None ->
          let left,right =
            try split xs with Failure message ->
              failwith (Printf.sprintf "%s; case=%s rotation=%d" message name m) in
          incr splits;
          visit ((m,depth+1,left)::(m,depth+1,right)::rest) in
    Printf.printf "CASE %s: x_alpha,alpha,x_gamma,gamma; five discrete rotations\n%!" name;
    visit (List.init 5 (fun m -> (m,0,Array.make 4 (box 0. 1.))));
    let leaves=Array.fold_left ( + ) 0 reasons in
    if !processed <> 2 * !splits + 5 || leaves <> !splits + 5 ||
       not (Array.for_all (fun n -> n>0) rotation_nodes) then
      failwith "Subdivision accounting failed";
    Array.iteri (fun i n -> Printf.printf "LEAVES %s: %d\n" reason_names.(i) n) reasons;
    Array.iteri (fun m n -> Printf.printf "ROTATION %d: nodes=%d\n" m n) rotation_nodes;
    Printf.printf "CASE COMPLETED %s: nodes=%d splits=%d depth=%d cpu=%.6f\n%!"
      name !processed !splits !max_depth (Sys.time () -. started);
    {processed= !processed; splits= !splits; max_depth= !max_depth;
     reasons; rotation_nodes}
end;;
