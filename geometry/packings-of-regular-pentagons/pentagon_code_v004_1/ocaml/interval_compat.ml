(* Legacy API adapter: CRlibm backend only. The square-root domain-error translation preserves the
   exception contract expected by Pent.sqrt_I (unresolved input -> subdivision).
   All other exceptions propagate. No Intel trigonometric fallback. *)
module Interval = struct
  include Interval_crlibm

  (* Legacy interval/interval operators. *)
  let ( +$ ) = I.( + )
  let ( -$ ) = I.( - )
  let ( *$ ) = I.( * )
  let ( /$ ) = I.( / )
  let ( ~-$ ) = I.( ~- )

  (* Keep the operand order used in the original source. *)
  let ( *$. ) = I.( *: )   (* interval times float *)
  let ( *.$ ) = I.( *. )   (* float times interval *)
  let ( /$. ) = I.( /. )   (* interval divided by float *)
  let ( +.$ ) = I.( +: )   (* float plus interval *)

  let float_i = I.of_int
  let pi_I = I.pi
  let abs_I = I.abs
  (* A wholly negative radicand has no real square root. Report it using
     the legacy Failure constructor so Pent.sqrt_I requests subdivision.
     Unexpected backend exceptions remain errors; no box is accepted here. *)
  let sqrt_domain_error_count = ref 0
  let sqrt_I x =
    try I.sqrt x with
    | Interval_base.Domain_error "sqrt"
        when x.low <= x.high && x.high < 0. ->
        incr sqrt_domain_error_count;
        raise (Failure "sqrt_I")
  let acos_I = I.acos
  let asin_I = I.asin
  let cos_I = I.cos
  let sin_I = I.sin
end;;
open Interval;;
let tan_I = Interval_crlibm.I.tan;;
