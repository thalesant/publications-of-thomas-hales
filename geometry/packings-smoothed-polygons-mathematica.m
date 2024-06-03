
(*
This file contains Mathematica calculations related to the book
"Packings of Smoothed Polygons"
by Hales and Vajjha

At some point, we will clean up the code,
but that will be a future project.


Conventions:

* tag="MCA:id" in a module gives the cross-reference to LaTeX.
doc="docstring" gives module documentation.

* To keep global namespace clutter to a minimum, substitution rules
are preferred to global variables, etc.

* compute... name for end-computations for paper.  Not needed
  elsewhere in code.

* test name for test code.

* By default, the file loads without running much code. To run
  specific calculations, it is often needed to change ":=" to "=".

* Many of the equations and lemmas in the book appear as "Claims" in
  the code.

* The file contains some obsolete code that was used in experiments
  before completion of the project.  This code is generally marked as
  obsolete and is sometimes commented out.

* The file also contains code for chapters that have been removed from
  the public version of the book.

*)

(* global definitions *)
Echoing= False;
EchoOff[x_] := If[Echoing,Echo[x],x];

MCAID := Module[{doc = "create random identifier"}, 
  StringJoin["MCA:", ToString[RandomInteger[{10^6, 10^7}]]]];

Claim::usage="Claim[bool], Claim[bool,falsemsg]";

Claim[x_] := If[Not[TrueQ[x]], Echo[{"Failed Claim", x}], x];
Claim[x_, msg__] := 
  If[Not[TrueQ[x]], Echo[{"Failed Claim", msg, x}], x];
Claim0[x_, msg__] := 
  If[Not[TrueQ[x == 0]], Echo[{"Failed Claim", msg, x}], x];

Only[x_] := (Claim[Length[x] == 1, "Only"]; First[x]);

complexNorm[zs_] := 
	Sqrt[Total[Abs[zs]^2]];

test := (complexNorm[{3 + 4 I, 1 + I}]^2 - (25 + 2))

RR[z1_, z2_] := Re[Conjugate[z1]*z2];

errorAbs[vv_] := Apply[Plus, Map[Abs, Flatten[vv]]];
error2[vv_]:= Apply[Plus,Map[Abs[#]^2&,Flatten[vv]]];

EqTable[x_,y_]:= Table[x[[i]]==y[[i]],{i,1,Length[x]}];
NormalSeries[x__] := Normal[Series[x]];

rescale[zs_, f_] := 
  Module[{doc = "weighted homogeneous rescaling"}, 
   Table[zs[[k]]*f^k, {k, 1, Length[zs]}]];

test = rescale[{1, 1, 1, 1}, 2];

(* end repeated global *)

id[x_] := x;
X = {{a, b}, {c, -a}};
Xp = {{ap, bp}, {cp, -ap}};
e0 = {1, 0};
e1 = {1/2, Sqrt[3]/2};
e2 = {-1/2, Sqrt[3]/2};
e3 = -e0;
e4 = -e1;
e5 = -e2;
J = {{0, -1}, {1, 0}};
R = {{1/2, -Sqrt[3]/2}, {Sqrt[3]/2, 1/2}};
Claim[(R==MatrixExp[J Pi/3])//Simplify,"check R"];

I2 = {{1, 0}, {0, 1}};

wd[x_, y_] := Det[{x, y}];
Phiz = {{x/y, -(x^2 + y^2)/y}, {1/y, -x/y}};
br[x_, y_] := x.y - y.x;
frac[{{a_, b_}, {c_, d_}}, z_] := (a z + b)/(c z + d);
Ad[g_,X_]:= g.X.Inverse[g];

Cayley[X_]:= Module[{c = {{1,I},{I,1}}/Sqrt[2]},
		    Inverse[c].X.c];
ICayley[X_] := Module[{c = {{1, I}, {I, 1}}/Sqrt[2]}, c.X.Inverse[c]];

u100sub = {u0 -> 1, u1 -> 0, u2 -> 0};
u010sub = {u0 -> 0, u1 -> 1, u2 -> 0};
u001sub = {u0 -> 0, u1 -> 0, u2 -> 1};
abcsub = {a -> (u1 - u2)/Sqrt[3], b -> (u0 - 2 u1 - 2 u2)/3, 
   c -> u0};

{fvector, f010, f001, f100} = 
  Module[{fden, f1, f2, fu, fvector, f010, f001, f100}, 
   fden = 2 a x + b - c x^2 - c y^2;
   f1 = y (2 a x + b - c x^2 + c y^2)/fden;
   f2 = 2 y^2 (a - c x)/fden;
   fvector = {f1, f2};
   fu = fvector /. abcsub;
   f010 = (fu /. u010sub);
   f001 = (fu /. u001sub);
   f100 = (fu /. u100sub);
   {fvector, f010, f001, f100}];

Zu = X /. abcsub;

Phi[x_,y_]:= {{x/y, (-x^2 - y^2)/y}, 
 {y^(-1), -(x/y)}};

linFrac[R_,{x_,y_}]:= IPhi[R.Phi[x,y].Inverse[R]];

      
IPhi[Phiz_] := Module[{a = Phiz[[1, 1]], c = Phiz[[2, 1]]},
   {a/c, 1/c}];
P001[X_] := Zu/Tr[X.Zu] /. u001sub // Simplify;
P010[X_] := Zu/Tr[X.Zu] /. u010sub // Simplify;
P100[X_] := Zu/Tr[X.Zu] /. u100sub // Simplify;
Z001 = Zu /. u001sub;
Z010 = Zu /. u010sub;
Z100 = Zu /. u100sub;

(* end of global definitions *)

smoothedOctPlot:=
	Module[{tag = "smoothed-oct plot", y0, t1, X0, P0, gA, ee, sigs, gB, 
   gC, gD, cost}, y0 = Sqrt[(Sqrt[8] - 1)/3];
  t1 = Log[4/(3 y0^2 + 1)]/(Sqrt[3] y0);
  X0 = (Phiz/.{x->0,y->y0});
  P0 = P001[X0];
  gA = MatrixExp[t (X0 + P0)].MatrixExp[-t P0] // N // Simplify // 
    Chop;
  (*STALLS:cost=-6*Integrate[Simplify[Trace[J.MatrixExp[
  t P0].X0.MatrixExp[-t P0]]],{t,0,t1}];
  EchoOff[cost];*)ee = {e0, e1, e2, e3, e4, e5};
  sigs[g_] := Table[g.ee[[i]], {i, 1, 6}];
  gB = (gA /. t -> t1).MatrixPower[R, 2].gA.Inverse[MatrixPower[R, 2]];
  gC = (gB /. t -> t1).R.gA.Inverse[R];
  gD = (gC /. t -> t1).gA;
  ParametricPlot[
	  Join[sigs[gA], sigs[gB], sigs[gC], sigs[gD]], {t, 0, t1}]];

smoothedOctCost:=
	Module[{doc = "smoothed-oct cost", y0, t1, X0, P0, cost, eP}, 
  y0 = Sqrt[(Sqrt[8] - 1)/3];
  t1 = Log[4/(3 y0^2 + 1)]/(Sqrt[3] y0);
       X0 = (Phiz/.{x->0,y->y0})//Simplify;
  P0 = P001[X0] // FullSimplify;
  eP = MatrixExp[t P0] // FullSimplify;
  cost = -6 Integrate[
	  Simplify[Tr[J.eP.X0.Inverse[eP]]], {t, 0, t1}]] // Simplify;

MCA7481306 := 
 Module[{doc = "0.902414,eq:density-formula", t}, t = smoothedOctCost/Sqrt[12];
 {N[t], t - (8 - Sqrt[32] - Log[2])/(Sqrt[8] - 1) // Simplify}];

moduleTangentSpace:=Module[{tag = "MCA:-", 
   doc = "This computes the action of a rotation via linear" <>
      "fractional transformations on the tangent space at I of the" <>
      "upper-half-plane"}, 
  D[frac[MatrixExp[J theta], I + dt], dt] /. dt -> 0 // FullSimplify];

modulePhiEquivariant:=Module[{tag = "MCA:Phi-equivariant", 
   doc = "This shows that Phi is SL2-equivariant", 
   g = {{a, b}, {c, d}}, f1, f}, 
  f1 = IPhi[g.Phiz.Inverse[g] // Simplify].{1, I};
  f = frac[{{a, b}, {c, d}}, x + I y] // FullSimplify;
  f1 - f // FullSimplify];

	    (* rho-related calculations *)

rhosub = Module[{tag = "MCA:rho-star-inequalities", sol00, sol11, 
   sol22, sols, det, vertices, stsub}, 
  sol00 = Only[Solve[X.e0 == rho0 e1 + trho1 e2, {rho0, trho1}]];
  sol11 = Only[Solve[X.e1 == rho1 e2 + trho2 e3, {rho1, trho2}]];
  sol22 = Only[Solve[X.e2 == rho2 e3 + trho3 e4, {rho2, trho3}]];
  sols = {sol00, sol11, sol22, rho3 -> rho0, rho4 -> rho1, 
      rho5 -> rho2} // Flatten // Simplify;
  Claim[({rho0 - trho3, rho1 - trho1, rho2 - trho2} /. sols // 
      Simplify) == {0, 0, 0}];
  det = (rho0 rho1 + rho0 rho2 + rho1 rho2) - Det[X] /. sols // 
    Simplify;
  Claim[det == 0, "critical hexagon det"];
  vertices = {(e0 + rho2 X.e0/Det[X]) - (e1 - rho0 X.e1/Det[X]), (e1 +
          rho3 X.e1/Det[X]) - (e2 - rho1 X.e2/Det[X]), (e2 + 
         rho4 X.e2/Det[X]) - (e3 - rho2 X.e3/Det[X])} //. sols // 
    FullSimplify;
  Claim[(vertices // Flatten // Union) == {0}, 
   "critical hexagon check"];
  stsub = {Solve[
      e0 + s0 (rho0 e1 + rho1 e2) == e1 - t1 (rho1 e2 + rho2 e3), {s0,
        t1}][[1]], 
    Solve[e1 + s1 (rho1 e2 + rho2 e3) == 
       e2 - t2 (rho2 e3 + rho3 e4), {s1, t2}][[1]], 
    Solve[e2 + s2 (rho2 e3 + rho3 e4) == 
       e3 - t2 (a3 e4 + rho4 e5), {s2, t2}][[1]]};
  Join[sols, stsub]];

Module[{doc = "MCA:7511280, q1 calculation", q1, q1bis, sols, p1, 
  p2},
 sols = Take[rhosub, 8];
 p1 = e1 + (rho0) X.e1/Det[X];
 p2 = e2 + rho1 X.e2/Det[X];
 q1 = p1 + 2 rho1 X.e1/Det[X];
 q1bis = p2 - 2 rho1 X.e3/Det[X];
 Claim[{0, 0} == q1 - q1bis /. sols // Simplify];
 ];

(* Dihedral symmetries of star inequalities *)

moduleRhoRotate:=Module[{tag = "MCA:rho-rotate", 
   doc = "Look what happens to the star ineqs rho_i > 0, when X is \
replaced with AdR.X", XR, ar, br, cr, sols, subr}, 
  XR = R.X.Inverse[R] // Simplify;
  ar = XR[[1, 1]];
  br = XR[[1, 2]];
  cr = XR[[2, 1]];
  subr = {a -> ar, b -> br, c -> cr, rho0 -> rho0R, rho1 -> rho1R, 
    rho2 -> rho2R};
  sols = Take[rhosub, 8]; sols /. subr // Simplify];

moduleKappa2Pos:=Module[{tag = "MCA:kappa2-pos", 
   doc = "Proof that kappa2>0 if kappa0=kappa1=0.", Y, solw, sols, 
   out}, Y = X - X.Xp;
  sols = Take[rhosub, 8];
  solw = Solve[{wd[e0, Y.e0] == 0, wd[e2, Y.e2] == 0}, {ap, 
      bp}][[1]];
  wd[e4, Y.e4] /. solw // Simplify;
  out = Det[X] Sqrt[3]/rho0;
  Claim[({wd[e0, Y.e0], wd[e2, Y.e2], wd[e4, Y.e4] - out} /. solw /. 
       sols // Simplify) == {0, 0, 0}];
  out];

{rho0z, rho1z, rho2z} = 
  Module[{doc = 
     "MCA:2104115, compute rho_j o Phiz, compare to obsolete alpha,beta,gamma", 
    sols, rho0z, rho1z, rho2z, alpha, beta, gamma}, 
   sols = Take[rhosub, 8];
   {rho0z, rho1z, 
     rho2z} = {rho0, rho1, rho2} /. sols /. {a -> Phiz[[1, 1]], 
       b -> Phiz[[1, 2]], c -> Phiz[[2, 1]]} // Simplify;
   alpha = (1 + Sqrt[3] x)/y;
   beta = (1 - Sqrt[3] x)/y;
   gamma = (3 x^2 + 3 y^2 - 1)/(2 y);
   Claim[({alpha - Sqrt[3]*rho0z, beta - Sqrt[3]*rho1z, 
        gamma - Sqrt[3]*rho2z} // Simplify) == {0, 0, 0}];
   {rho0z, rho1z, rho2z}];

moduleODEDenom:=Module[{doc = "Formula for denominator of ODE", sols, den1, den2}, 
  sols = Take[rhosub, 8]; den1 = Tr[Zu.X];
  den2 = -(2/Sqrt[3]) (rho2 u0 + rho1 u1 + rho0 u2) /. sols;
  Claim0[den1 - den2 // Simplify,"Tr[Zu.X]"]];

sl2Lemmas := Module[{Y},
  Claim0[Tr[X.X] + 2 Det[X] // Simplify, "MCA:sl2-lemmas-1"];
  Claim[({a, b, c} /. 
        Solve[{wd[e1, X.e1] == 0, wd[e2, X.e2] == 0, 
          wd[e3, X.e3] == 0}, {a, b, c}] // Flatten // Union) == {0}, 
   "sl2-lemmas-2"];
  Y = {{d, e}, {f, -d}};
  Claim[X.Y + Y.X == Tr[X.Y] I2, "sl2-lemmas-3"];
  ];

(*Filippov lemma*)

moduleFilippovDiff := 
  Module[{doc = "MCA:4087162", sols}, sols = Take[rhosub, 8];
   Claim[(f001 - f010) == {0, 2/(Sqrt[3] rho0z rho1z)} /. sols // 
     Simplify, "MCA:4087162"]];

moduleFilippovLemma := 
  Module[{doc = "Filippov lemma,MCA:8165998", r1, r2, r3, Lf, Lf1, 
    affline, tt}, 
   affline = 
    Only[Solve[{{r1, r2}.f100 + r3 == 0, {r1, r2}.f010 + r3 == 
        0, {r1, r2}.f001 + r3 == 1}, {r1, r2, r3}]];
   Lf = ({r1, r2}.(fvector /. abcsub) + r3) /. affline // Simplify;
   Lf1 = u2 rho0z/(u0 rho2z + u1 rho1z + u2 rho0z) // Simplify;
   Claim0[Lf - Lf1 // FullSimplify, "MCA:8165998"]];

test:=Module[{doc = "obscure", rsub}, 
  rsub = Solve[{Tr[{{u, v}, {w, -u}}.{{1, 0}, {0, -1}}] == 
       2 (v1 x + v2 y), Tr[{{u, v}, {w, -u}}.{{0, 1}, {0, 0}}] == v1, 
      Tr[{{u, v}, {w, -u}}.{{0, 0}, {1, 0}}] == -(v1 (x^2 - y^2) + 
          2 v2 x y)}, {u, v, w}][[1]];
  Tr[{{u, v}, {w, -u}}.Phiz] /. rsub // Simplify];

lemTangentMaps := Module[{doc = "MCA:6479593", Y},
  Y = {{a, b}, {0, -a}};
  Y /. Only[
    Solve[r1 D[Phiz, x] + r2 D[Phiz, y] == br[Y, Phiz] + t  Phiz, {a, 
      b, t}]]
		  ];

lemma := Module[{doc = "MCA:6654903"},
  Claim[Tr[J.Phiz] == -(x^2 + y^2 + 1)/y // Simplify, "6654903"]
	 ];

fvectorDerivation := 
 Module[{doc = "MCA:4861125", dPhi, Z, dPhiZ, sub, fvec}, 
  dPhi = D[Phiz, x] dx + D[Phiz, y] dy;
  Z = {{a, b}, {c, -a}};
  dPhiZ = br[Z, Phiz]/Tr[Z.Phiz];
  sub = Only[
    Solve[{dPhi[[1, 1]] == dPhiZ[[1, 1]], 
      dPhi[[2, 1]] == dPhiZ[[2, 1]]}, {dx, dy}]];
  fvec = {dx, dy} /. sub;
  Claim[fvec == fvector // Simplify, "MCA:4861125"];
  Claim[dPhiZ == dPhi /. sub // Simplify,"MCA:4861125"];
	fvec];	

lemma:= Module[{doc = "MCA:9433693, Dihedral action", S},
 S = {{-1, 0}, {0, 1}};
 Claim[R.Z001.Inverse[R] == Z010, "9433693-001"];
 Claim[R.Z010.Inverse[R] == Z100, "9433693-002"];
 Claim[R.Z100.Inverse[R] == Z001, "9433693-003"];
 Claim[-S.Z100.Inverse[S] == Z100, "9433693-004"];
 Claim[-S.Z010.Inverse[S] == Z001, "9433693-005"];
 ]

(* explicit compactification \h^** *)

moduleHstarCompactification:=
	Module[{doc = "compactification", circle, r, z, h = 4.5}, 
  r = r /. Only[Solve[15 (1/Sqrt[3] - r) == h, r]];
  z = frac[R, r + I h];
  circle = (x^2 + (y - c)^2) + b;
  NSolve[{(circle /. {x -> 1/Sqrt[3], y -> 0}) == 
	  0, (circle /. {x -> Re[z], y -> Im[z]}) == 0}, {b, c}]];

moduleHstarCompactificationBis := 
 Module[{doc = "compactification, MCA:6316399, explicit horocycle", d2, z, cy},
  z = frac[{{a, b}, {c, d}}, x + I h];
  d2 = Abs[z - (a/c + I cy) ]^2 // ComplexExpand // Simplify;
  cy = cy /. 
    Only[FullSimplify[
      Solve[{(d2 /. x -> 0) == d2}, {cy}], {a*d - b*c > 0, h > 0}]];
  Claim[cy == (a d - b c)/(2 c^2 h), "MCA:6316399"];
  {a/c, cy} /. {a -> R[[1, 1]], b -> R[[1, 2]], c -> R[[2, 1]], 
    d -> R[[2, 2]], h -> 45/10}
  ];

explicitSolution:=Module[{doc = "MCA:9041208", X0, sol, sol0}, 
 Claim[J == 3 X /. abcsub /. {u0 -> 1/3, u1 -> 1/3, u2 -> 1/3}, 
  "MCA:9041208"];
 X0 = X /. abcsub /. {u0 -> 1 - u1 - u2};
 sol0 = Only[Solve[{X0[[1, 1]] == 0, X0[[1, 2]] == 0}, {u1, , u2}]] //
    Echo;
       X0 /. sol0];

  explicitSolutionAtVertex := Module[{doc = "MCA:8735396", fvec, f, xt, yt},
   Echo[{"001", Eigensystem[-Z001]}];
  fvec = fvector /. abcsub;
  f = fvec /. u001sub;
  {xt, yt} = {-1/Sqrt[3] + C0 E^(r t), C0 r E^(r t)};
  Claim[D[{xt, yt}, t] == (f /. {x -> xt, y -> yt}) // Simplify, 
   "ODE001 MCA:8735396"];
  Echo[{"010", Eigensystem[-Z010]}];
  f = fvec /. u010sub;
  {xt, yt} = {1/Sqrt[3] + C0 E^(r t), C0 r E^(r t)};
  Claim[D[{xt, yt}, t] == (f /. {x -> xt, y -> yt}) // Simplify, 
   "ODE010 MCA:8735396"];
  Claim[0 == X[[2, 1]] /. abcsub /. u0 -> 0, "MCA:8735396"];
  ]	

       
(* Wall analysis. Book section on Walls. *)

moduleWallAnalysisObsolete:=
	Module[{doc="replaced with moduleWallAnalysis",uwallsub, fwall, h, odes, Xt, h0, ham, phi, A, v, b, tilsub, 
  odecompute}, 
 uwallsub = {u0 -> 0, u1 -> 1/2 + uwall, u2 -> 1/2 - uwall};
 fwall = fvector /. abcsub /. uwallsub // Simplify;
 EchoOff[{"fwall", fwall}];
 h = {{s[t], 1 - s[t]*x[t]}, {-1, x[t]}};
 odes = {s'[t] -> 1/y[t], x'[t] -> y[t]};
 Xt = Inverse[h].(D[h, t] /. odes) // Simplify;
 (*eq:xy-wall*)
 Claim[Phiz == (Xt /. {x[t] -> x, y[t] -> y}) // Simplify];
 (*independent of s0*)
 h0 = {{s[t] + s0, 1 - (s[t] + s0) x[t]}, {-1, x[t]}};
 Claim[{{1, -s0}, {0, 1}} == (h0.Inverse[h] // Simplify)];
 (*costate eqns*)phi = x^2/y;
 ham = l1 y + l2 fwall[[2]] + l3/y + lcost phi;
 EchoOff[{"costate ", -{D[ham, x], D[ham, y], D[ham, s]} // 
    FullSimplify}];
 (*Monotonoicity,negatative*)
 EchoOff[{"negative: ", D[fwall[[2]], uwall] // Simplify}];
 (*eq:wall-zero*)
 EchoOff[Solve[({ham, D[ham, y]} /. l2 -> 0) == {0, 0}, {l3, l1}]];
 ];

moduleWallODEErrorObsolete:=
	Module[{doc = "redone in moduleWallAnalysis, wall ODE v-error term switching lambda2", ham, b, A, odeA, odeB},
 ham = lambda1* y + lambda2*ef2[x, y] + lambda3/y + 
    lcost*x^2/y /. {lcost -> -1, lambda3 -> x0^2};
 odeA = ({l1p, l2p} - {til1p, til2p}) /. {til1p -> 2 x/y, 
      til2p -> -(x^2 - x0^2)/y^2 - til1, l1p -> -D[ham, x], 
      l2p -> -D[ham, y]} /. {lambda1 -> v1 + til1, 
     lambda2 -> v2 + til2} // Simplify;
 b = {D[ef2[x, y], x], D[ef2[x, y], y]};
 A = {{0, b[[1]]}, {1, b[[2]]}};
 odeB = -A.{v1, v2} - til2 b;
 Claim[(odeA - odeB // Simplify) == {0, 0}]
	];

moduleWallAnalysis := 
 Module[{doc = "MCA:7297989", uwallsub, fwall, h, odes, odeA, Xt, 
   htilde, ham, phi, A, v, b, odeB, tilsub}, 
  uwallsub = {u0 -> 0, u1 -> 1/2 + uwall, u2 -> 1/2 - uwall};
  fwall = fvector /. abcsub /. uwallsub // Simplify;
  Echo[{"fwall", fwall // InputForm}];
  Claim[fwall == {y, 
     2 3^Rational[1, 
        2] uwall (-1 + 2 3^Rational[1, 2] uwall x)^(-1) y^2}, 
   "MCA:7297989:fwall"];
  h = {{s[t], 1 - s[t]*x[t]}, {-1, x[t]}};
  "better h";
  h = {{1, -x[t]}, {s[t], 1 - s[t]*x[t]}};
  odes = {s'[t] -> 1/y[t], x'[t] -> y[t]};
  Xt = Inverse[h].(D[h, t] /. odes) // Simplify;
  Claim[Phiz == (Xt /. {x[t] -> x, y[t] -> y}) // Simplify, 
   "MCA:7297989:ODE-h"];
  htilde = h /. {s[t] -> (s0 + s[t])};
  htilde.Inverse[h] // Simplify // Echo;
  Claim[{{1, 0}, {s0, 1}}.h == htilde // Simplify, 
   "MCA:7297989:independent of s0"];
  "doc=costate eqns";
  phi = x^2/y;
  ham = l1 y + l2 fwall[[2]] + l3/y + lcost phi;
  Echo[{"costate ", -{D[ham, x], D[ham, y], D[ham, s]} // 
     FullSimplify}];
  doc = "Monotonoicity,negative";
  {"negative", D[fwall[[2]], uwall] // Simplify} // Echo;
  "eq:wall-zero";
  Echo[Solve[({ham, D[ham, y]} /. l2 -> 0) == {0, 0}, {l3, l1}]];
  "wall ODE v-error term switching lambda2";
  ham = ham /. {lcost -> -1, l3 -> x0^2};
  odeA = ({l1p, l2p} - {til1p, til2p}) /. {til1p -> 2 x/y, 
        til2p -> -(x^2 - x0^2)/y^2 - til1, l1p -> -D[ham, x], 
        l2p -> -D[ham, y]} /. {l1 -> v1 + til1, l2 -> v2 + til2} // 
     Simplify // Echo;
  b = {D[fwall[[2]], x], D[fwall[[2]], y]} // Echo;
  A = {{0, b[[1]]}, {1, b[[2]]}};
  odeB = -A.{v1, v2} - til2 b;
  Claim[(odeA == odeB // Simplify), "MCA:7297989,ODE-v"];];

test:=Module[{doc = "I think this is all junk", uwallsub, f1u, f2u, Hu, PX, 
   PX0, PX010, PX100, PX001, Pdiff, Ep, LRsub, LLR, ODEterm1, Y, hR, 
   aR, bR, cR, a1, b1, c1, Lambda10, L1, LR, L1c, musol, compat, 
   compat2, Der},
  (*ODE along (0,1,0)(0,0,1) wall*)
  uwallsub = {u0 -> 0, u1 -> 1/2 + uwall, u2 -> 1/2 - uwall};
  f1u = First[fvector] /. abcsub /. uwallsub // Simplify;
  f2u = Last[fvector] /. abcsub /. uwallsub // Simplify;
  Hu = nu1 First[fvector] + nu2 Last[fvector] /. abcsub;
  (Hu /. u010sub) - (Hu /. u001sub) // Simplify;
  PX = Zu/Tr[Zu.Phiz] // Simplify;
  PX0 = PX /. uwallsub // Simplify; 
  PX001 = PX /. u001sub // Simplify;
  PX010 = PX /. u010sub // Simplify;
  PX100 = PX /. u100sub // Simplify;
  Pdiff = PX001 - PX010 // Simplify;
  Ep = {{0, 1}, {0, 0}};
  (*LambdaR=cr*LLR*)
  LR = {{aR, bR}, {cR, -aR}};
  LRsub = 
  Solve[{Tr[LR.Phiz] == 0, Tr[LR.Pdiff] == 0}, {aR, bR}]//Only // 
    Simplify;
  LLR = (LR /. LRsub)/cR // Simplify;
  {"ham", Tr[LLR.PX0]} // Simplify Tr[LLR.PX010 - PX100] // Simplify;
  (*ODE for LLR*)
  ODEterm1 = (br[PX0, LLR] - Tr[LLR.PX0]*br[PX0, Phiz]) // Simplify;
  y (Last[fvector] /. abcsub /. uwallsub) Ep // Simplify;
  ODEterm1 - 2 y (Last[fvector] /. abcsub /. uwallsub) Ep // Simplify;
  (First[fvector] /. abcsub /. uwallsub) // Simplify;
  Y = {{y, -2 x y}, {0, -y}};
  {Tr[LLR.Y], Tr[LLR.Phiz], Tr[Y.Phiz]} // Simplify;
  {Tr[LLR.LLR], Tr[Y.Y]} // Simplify;
  hR = {{tau, 1 - tau x}, {-1, x}};
  Lambda10 = {{a1, b1}, {c1, -a1}};
  L1 = Inverse[hR].Lambda10.hR - (3/2) lcost J // Simplify;
  L1c = L1 /. {lcost -> (2/3) c1} // Simplify;
  (**)
  br[Phiz, Y] - 2 LLR // Simplify; {"X0y+LLR", Phiz y + LLR} //
    Simplify;
  Tr[(Lambda10 - (3/2) lcost J).(Phiz y + LLR)] // Simplify;
  (*compat*)
  musol = {mu -> -Tr[br[L1c, Phiz].Y]/(2 y^2)} // Simplify; 
  Der[f_] := 
   Module[{f1, f2, f3}, 
    f1 = f /. {x -> x[t], y -> y[t], tau -> tau[t]};
    f2 = D[f1, t];
    f3 = f2 /. {x[t] -> x, x'[t] -> y, y[t] -> y, y'[t] -> f2u, 
        tau[t] -> tau, tau'[t] -> 1/y} // Simplify;
    f3];
  (*'*)
  compat = Der[mu /. musol] f2u; 
  compat2 = compat - br[L1c, Phiz][[2, 1]] // Simplify // Factor;
  compat2 /. c1 -> 0 // Simplify; 
  Solve[compat2 == 0, tau];
  {"L1cPhiz", (1/b1)*br[L1c, Phiz] /. {a1 -> 0, c1 -> 0} // 
	      Simplify} // Factor];

(* ... *)
test:=Module[{} , 
 fvector /. abcsub /. {u0 -> 0, u1 -> 1/2 + uu, u2 -> 1/2 - uu} // 
  Simplify;
 fvector /. abcsub /. u001sub // Simplify D[Phiz, y] // Simplify;
 D[Phiz, x]/2 Phiz Zu /. abcsub /. u0 -> 0];

abnormalWall = 
 Module[{doc = "Abnormal Wall calc, MCA:4647835", LR, L1, x1p, y1p, xysub, Z, P, 
   Ham},
  LR = {{x[t], y[t]^2 - x[t]^2}, {1, -x[t]}};
  L1 = {{-x[t], x[t]^2}, {-1, x[t]}};
  {x1p, y1p} = fvector /. abcsub /. {u0 -> 0};
  xysub = {x[t] -> x, y[t] -> y, x'[t] -> x1p, y'[t] -> y1p};
  Z = Zu /. {u0 -> 0};
  P = Z/Tr[Z.Phiz];
  Claim[D[L1, t] == br[L1, Phiz] /. xysub // Simplify, 
   "abnormal wall"];
  Claim[D[LR, t] == 
      br[P, LR] - Tr[LR.P]*br[P, Phiz] + br[-L1, Phiz] /. xysub // 
    Simplify, "abnormal wall LR"];
  Ham = Tr[L1.Phiz] - Tr[LR.P] /. xysub // Simplify;
  Claim0[Ham, "abnormal wall ham"];
 ];

test:=Module[{doc="Maximum principle is strict on abnormal wall",Z011, LR, ham},
  Z011 = Zu /. abcsub;
  LR = {{x, y^2 - x^2}, {1, -x}};
  ham = Tr[LR.Z011]/Tr[Phiz.Z011] // Simplify;
  {"always strictly positive:",
   (h /. {u0 -> 0}) - (h /. {u1 -> 0, u2 -> 0})}] // Simplify

(* end of Wall-Section *)

cost2ndOrder = Module[{doc="MCA:1049350 cost calculation of circle deformation",
		       Psi, Psi0},
  Psi0 = {{psi1[t], psi2[t]}, {psi2[t], -psi1[t]}};
  Psi = I2 + s Psi0 + s^2/2 Psi0.Psi0 + s^3/3! MatrixPower[Psi0, 3];
  Series[-(3/2) Tr[J.Inverse[Psi].D[Psi, t]], {s, 0, 2}]];

modulePlotDeformedCircle:=
	Module[{doc="Produce graphic from book: Images/deformed-circle.pdf. "<>
  "Take a second order deformation of the circle"<>
  "to find that it looks approximately like a smoothed octagon, "<>
  "deformed-circle.pdf, MCA:9575710",
  c12,c11,YY,J,eee=0.12,s0=-1/8,f},
       c12[t_] := Which[t <= Pi/9, t,
			t <= 2 Pi/9, 2 Pi/9 - t, True, 0];
       c11[t_] := Which[t <= Pi/9, 0, t <= 2 Pi/9, t - Pi/9, True, 
			Pi/3 - t];
       YY[e_, t_] := MatrixExp[e {{c11[t], c12[t]}, {c12[t], -c11[t]}}];
       J = {{0, -1}, {1, 0}};
       f[e_, t_, s_] := MatrixExp[J s0].YY[e, t].MatrixExp[J (t + s)].{1, 0};
       ParametricPlot[{f[eee, t, 0], f[eee, t, Pi/3], f[eee, t, 2 Pi/3], 
	     f[eee, t, Pi], f[eee, t, 4 Pi/3], f[eee, t, 5 Pi/3]},
	 {t, 0, Pi/3}]];

(* no finite switch at the singular set *)
test:=Module[{adJ,Zk},
       adJ[X_]:= br[J,X];
       Zk = Zu/.u001sub
];

(* main transversality result for the smoothed 6k+2-gon *)

tswgon = Module[{doc = 
    "Formula for tswgon (switching time) in 6k+2-gon." <> 
     "The module verifies the strong boundary conditions, " <> 
     "using constant control ODE solution for X", tag = "MCA:t1", zy, 
   Phizy, P3y, e3X, X3t, X3tt, tswgon, transversality}, 
  tswgon = Log[4/(1 + 3 y0^2)]/(Sqrt[3] y0);
  zy := I y0;
  Phizy = Phiz /. {x -> 0, y -> y0};
  P3y = P001[Phizy];
  e3X = MatrixExp[t P3y] // Simplify;
  X3t = e3X.Phizy.Inverse[e3X] // Simplify;
  X3tt = X3t /. t -> tswgon // FullSimplify;
  transversality = X3tt == Inverse[R].Phizy.R // Simplify;
  Check[transversality, "MCA:t1 boundary condition"];
  tswgon];

(*
Ad3Deprecated[g_,X_,gInv_]:= g.X.gInv;
 *)

constantControlSolution[Zu_,X0_,Lambda10_,LambdaR0_,lambdacost_]:=
 Module[{P0,expmX0P0,expmP0,expX0P0,expP0,Psi,psi,LambdaRtil,g,X,Lambda1,LambdaR},
  P0 = Zu/Tr[Zu.X0];
  expmX0P0 = MatrixExp[-t (X0+P0)];
  expX0P0 = (expmX0P0/.{t-> -t});
  expmP0 = MatrixExp[-t P0];
  expP0 = expmP0/.{t-> -t};
  Psi = Integrate[expmX0P0.Lambda10.expX0P0-(3/2)lambdacost*expmP0.J.expP0    ,{t,0,t}];
  psi = Integrate[Tr[P0.(LambdaR0 - br[Psi,X0])]    ,{t,0,t}];
  LambdaRtil = LambdaR0 - br[Psi + psi P0,X0];
  LambdaR = expP0.LambdaRtil.expmP0;
  g = expX0P0.expmP0;
  X = expP0.X0.expmP0;
  Lambda1 = expP0.expmX0P0.Lambda10.g;
  {X,Lambda1,LambdaR}];



CoshE[t_] := (E^t + E^(-t))/2; 
SinhE[t_] := (E^t - E^(-t))/2;

MatrixExpSL[t_, X_] := Module[{doc="assume detX<0",d, d1},
   d = Det[X];
   d1 = Sqrt[-d];
   CoshE[t *d1] IdentityMatrix[2] + (SinhE[t *d1]/d1) X
   ];

MatrixExpSymbolic[t_, X_, detmsqrt_] := 
  CoshE[t*detmsqrt] IdentityMatrix[2] + (SinhE[t*detmsqrt]/detmsqrt) X;

constantControlSolutionNegDet[Zu_, X0_, Lambda10_, LambdaR0_, 
   lambdacost_] := 
  Module[{doc = "precondition sl2, Det[P0]<0, Det[X0+P0]<0", P0, expmX0P0, 
    expmP0, expX0P0, expP0, Psi, psi, LambdaRtil, g, X, Lambda1, 
    LambdaR}, P0 = Zu/Tr[Zu.X0];
   expmX0P0 = MatrixExpSL[-t, (X0 + P0)];
   expX0P0 = (expmX0P0 /. {t -> -t});
   expX0P0 = MatrixExpSL[t, (X0 + P0)];
   EchoOff[{expX0P0, expmX0P0}];
   Claim[Det[X0 + P0] < 0, "X0+P0"];
   Claim[Det[P0] < 0, "P0"];
   expmP0 = MatrixExpSL[-t, P0];
   expP0 = expmP0 /. {t -> -t};
   EchoOff[expP0.expmP0 /. t -> 0.1];
   EchoOff[{"id", expX0P0.expmX0P0} /. t -> 0.1];
   (*Echo[{"constant control dets",Det[P0],Det[X0+P0]}];*)
   Psi = Integrate[
     expmX0P0.Lambda10.expX0P0 - (3/2) lambdacost*expmP0.J.expP0, {t, 
      0, t}];
   psi = Integrate[Tr[P0.(LambdaR0 - br[Psi, X0])], {t, 0, t}];
   LambdaRtil = LambdaR0 - br[Psi + psi P0, X0];
   LambdaR = expP0.LambdaRtil.expmP0;
   g = expX0P0.expmP0;
   X = expP0.X0.expmP0;
   Lambda1 = expP0.expmX0P0.Lambda10.g;
   {X, Lambda1, LambdaR}];

constantControlSolutionData[P0_, X0P0_, 
  Lambda10_, detP0msqrt_,lambdacost_] := 
	Module[{doc = "precondition sl2, Det[P0]<0, Det[X0+P0]<0, LambdaR0, detP0=det(X0+P0)", 
   expmX0P0, expmP0, expX0P0, expP0, Psi, psi, LambdaRtil, g, gm, X0, 
   X, Lambda1, LambdaR, igrand},
  X0 = X0P0 - P0 // Simplify;
  expX0P0 = MatrixExpSymbolic[t, X0P0, detP0msqrt];
  expmX0P0 = MatrixExpSymbolic[-t, X0P0, detP0msqrt];
  expP0 = MatrixExpSymbolic[t, P0, detP0msqrt];
  expmP0 = MatrixExpSymbolic[-t, P0, detP0msqrt];
  EchoOff[{expX0P0, expP0}];
  igrand = 
   expmX0P0.Lambda10.expX0P0 - (3/2) lambdacost*expmP0.J.expP0 // 
    Simplify;
  Psi = Integrate[igrand, {t, 0, t}] // Simplify;
  EchoOff[Psi];
  igrand = -Tr[P0.br[Psi, X0]] // Simplify;
  psi = Integrate[igrand, {t, 0, t}] // Simplify;
  EchoOff[psi];
  (*
  LambdaRtil=-br[Psi+psi P0,X0];
  LambdaR=expP0.LambdaRtil.expmP0;
  g=expX0P0.expmP0;
  gm=expP0.expmX0P0;
  X=expP0.X0.expmP0;
  Lambda1=gm.Lambda10.g;
  *)
  EchoOff["simplify"];
  {expP0, expmP0, expX0P0, expmX0P0, Psi, psi} // Simplify];

Clear[p11, p12, p21, xp11, xp12, xp21, l11, l12, l21, dP0msqrt];

expforms := expforms = Module[{P0, X0P0, L10, LR0, lambdacost = -1},
    P0 = {{p11, p12}, {p21, -p11}};
    X0P0 = {{xp11, xp12}, {xp21, -xp11}};
    L10 = {{l11, l12}, {l21, -l11}};
    constantControlSolutionData[P0,  X0P0, L10, 
     dP0msqrt,lambdacost]
		       ];

Echo["R500"];

constantControlSolutionPreComputeDet[Zu_,X0_,Lambda10_,LambdaR0_,detP0msqrt_]:=
  Module[{P0, X0P0, p011, p012, p021, xp011, xp012, xp021, l011, l012,
     l021, expP0, expmP0, expX0P0, Psi, psi,
     LambdaR, expmX0P0, exmLambdaR, g, gm, X, Lambda1, LambdaRtil, 
    dummy},
   P0 = Zu/Tr[Zu.X0];
   {{p011, p012}, {p021, dummy}} = P0;
   X0P0 = X0 + P0;
   {{xp011, xp012}, {xp021, dummy}} = X0P0;
   {{l011, l012}, {l021, dummy}} = Lambda10;
   {expP0, expmP0, expX0P0, expmX0P0, Psi, psi} = 
    expforms /. {dP0msqrt -> detP0msqrt, 
      p11 -> p011, p12 -> p012, p21 -> p021, xp11 -> xp011, 
      xp12 -> xp012, xp21 -> xp021, l11 -> l011, l12 -> l012, 
      l21 -> l021};
   LambdaRtil = (* -br[Psi + psi P0, X0] + *)
   -br[Psi,X0] - psi*br[P0,X0] +
		LambdaR0 - 
     t*Tr[P0.LambdaR0]*br[P0, X0];
   LambdaR = expP0.LambdaRtil.expmP0;
   g = expX0P0.expmP0;
   gm = expP0.expmX0P0;
   X = expP0.X0.expmP0;
   Lambda1 = gm.Lambda10.g;
   {X, Lambda1, LambdaR}
  ];

constantControlSolutionPreCompute[Zu_, X0_, Lambda10_, LambdaR0_] :=
	Module[{P0,X0P0,detP0msqrt},
	          P0 = Zu/Tr[Zu.X0];
   X0P0 = X0 + P0;
   detP0msqrt = Sqrt[-Det[P0]];
   constantControlSolutionPreComputeDet[Zu,X0,Lambda10,LambdaR0,detP0msqrt]];

constantControl[Zu_, X0_, Lambda10_, LambdaR0_,mode_] := 
  Module[{lambdacost = -1},
   Switch[mode,
    "pre", 
    constantControlSolutionPreCompute[Zu, X0, Lambda10, LambdaR0],
    "neg", 
    constantControlSolutionNegDet[Zu, X0, Lambda10, LambdaR0, 
     lambdacost],
    "gen", 
    constantControlSolution[Zu, X0, Lambda10, LambdaR0, lambdacost]]];

test:=constantControlSolutionPreCompute[Z010, J, -(3/2) J, {{0, 0}, {0, 0}}];


test := MatrixExp[{{0, 1}, {2, 0}}]  - 
    MatrixExpSL[1, {{0, 1}, {2, 0}}] // Simplify;

moduleTestConstantControl:=
	Module[{doc = "test-constant-control-solutions", X0, P0, Lambda10, 
  LambdaR0, Xout, Lambda1out, LambdaRout, lambdacost = -1},
 X0 = {{0, -1}, {3/2, 0}};
 Lambda10 = {{0, -2}, {2, 0}};
 LambdaR0 = {{1, 1}, {2, 3}};
 P0 = Z001/Tr[Z001.X0];
 {Xout, Lambda1out, LambdaRout} = 
  constantControlSolution[Z001, X0, Lambda10, LambdaR0, lambdacost];
 Claim[(({Xout, Lambda1out, LambdaRout} - {X0, Lambda10, 
           LambdaR0}) /. {t -> 0} // Simplify // Flatten // 
     Union) == {0}, "init-sol"];
 Claim[(D[Xout, t] - br[P0, Xout] // Simplify // Flatten // 
     Union) == {0}, "X-ode"];
 Claim[(D[Lambda1out, t] - br[Lambda1out, Xout] // Simplify // 
      Flatten // Union) == {0}, "Lambda1-ode"];
 Claim[(D[LambdaRout, 
         t] - ((br[P0, LambdaRout] - 
            Tr[P0.LambdaRout]*br[P0, Xout]) + 
          br[-Lambda1out + (3/2) lambdacost J, Xout]) // Simplify // 
      Flatten // Union) == {0}, "LambdaR-ode"];
 ];


HamC[Zu_,X_,LambdaR_]:= Module[{doc="Control part of Hamiltonian"},-Tr[LambdaR.Zu]/Tr[X.Zu]];


switch[ZA_,ZB_,X_,LambdaR_]:= HamC[ZA,X,LambdaR]-HamC[ZB,X,LambdaR];

(* clear denominator *)
normalizedSwitch[ZA_,ZB_,X_,LambdaR_]:= -Tr[LambdaR.ZA]*Tr[X.ZB]+Tr[LambdaR.ZB]*Tr[X.ZA];

(* check signs at switching point. Derivative of HamC, using DZ for derivative calculations. 
   The control in the Hamiltonian need not match the control used for the derivative.  *)
DHamC[Zu_, Zode_, X_, LambdaR_, Lambda1_, lambdacost_] := 
  Module[{doc = "Zode governs ode for X,LambdaR,Lambda1", Pode, 
    DLambdaR, DX, Pu}, Pode = Zode/Tr[Zode.X];
   DLambdaR = (br[Pode, LambdaR] - Tr[LambdaR.Pode]*br[Pode, X]) + 
     br[-Lambda1 + (3/2) lambdacost J, X];
   DX = br[Pode, X];
   Pu = Zu/Tr[Zu.X];
   -Tr[DLambdaR.Pu] + Tr[LambdaR.Pu]*Tr[DX.Pu]];

Dswitch[ZA_,ZB_,Zode_,X_,LambdaR_,Lambda1_,lambdacost_]:= 
  DHamC[ZA,Zode,X,LambdaR,Lambda1,lambdacost]-DHamC[ZB,Zode,X,LambdaR,Lambda1,lambdacost];

(* Triangular control.
   Pick the control matrix that maximizes the Hamiltonian, or if it is near a switching point,
   pick the control of the largest two that gives a positive derivative.
   The derivative is computed using the ODE.   *)

pickConstantControl[X_, LambdaR_, Lambda1_, lambdacost_, epsilon_] := 
 Module[{doc="possibly buggy",HamC100, HamC010, HamC001, sort, d,ZA,ZB}, 
  HamC100 = HamC[Z100, X, LambdaR];
  HamC010 = HamC[Z010, X, LambdaR];
  HamC001 = HamC[Z001, X, LambdaR];
  sort = Reverse[
    Sort[{{HamC100, Z100}, {HamC010, Z010}, {HamC001, Z001}}]];
  d = sort[[1, 1]] - sort[[2, 1]];
  If[d > epsilon, Return[{sort[[1, 2]], d}]];
  ZA = sort[[1, 2]];
  ZB = sort[[2, 1]];
  If[Dswitch[ZA, ZB, ZA, X, LambdaR, Lambda1, lambdacost] > 0, 
   Return[{ZA, d}]];
  If[Dswitch[ZB, ZA, ZB, X, LambdaR, Lambda1, lambdacost] > 0, 
   Return[{ZB, d}]];
  Echo["Failure in pickConstantControl"];
  {ZA, d}];

subLambda10 := subLambda10 = 
 Module[{doc = 
    "solution to ODE Lambda1 at time 0 up to a scalar, " <> 
     "satisfying transversality at tswgon, constant control 001" <> 
     "answer in terms of y0 and lambda1", tag = "MCA:lambda1", X0, P0,
    g001, h, h0}, X0 = (Phiz /. {x -> 0, y -> y0});
  P0 = P001[X0];
  g001 = MatrixExp[t (X0 + P0)].MatrixExp[-t P0] // Simplify;
  h = g001.Inverse[R] /. t -> tswgon // Simplify // Factor;
  h0 = h - (Tr[h]/2) I2 // Simplify // Factor;
  {Lambda10 -> lambda1 h0}];

triangleSubObsolete := triangleSubObsolete =
 Module[{doc = 
    "Use-book-formula solve for LambdaR, special initial conditions,"<>
	 "hyperbolic triangle used for 6k+2-gon", LambdaR00, X00, claim, 
   lambdacost = -1, P0, Lambda100, LPintegrand, LP, ellt, ell, St, 
   Stsw, LambdaRt, LambdaRtsw, Ham0, Xtsw, P1tsw, P3tsw, Switch31, sol, 
   LambdaRtV, LambdaRtswV, transversalityTest, detLambda1V},
  LambdaR00 = lambdaR {{0, y0^2}, {1, 0}};
  X00 = (Phiz /. {x -> 0, y -> y0});
  P0 = P001[X00];
  Lambda100 = (Lambda10 /. subLambda10);
  claim = {Tr[LambdaR00.X00] == 0, Tr[LambdaR00.(P001[X00] - P010[X00])] == 0} // 
     Simplify // Union;
  Claim[claim == {True}, "LambdaR-ode-error"];
  LPintegrand = 
   MatrixExp[-s (X00 + P0)].Lambda100.MatrixExp[
       s (X00 + P0)] - (3/2) lambdacost MatrixExp[-s P0].J.MatrixExp[
        s P0] // Simplify; 
  LP = Integrate[LPintegrand, {s, 0, t}] // Simplify; 
  ellt = Integrate[Tr[P0.(LambdaR00 - br[LP, X00])], {t, 0, t}] // Simplify; 
  ell = ellt /. t -> tswgon // Simplify;
  St = LambdaR00 - (br[LP + ellt P0, X00]) // Simplify; 
  Stsw = St /. t -> tswgon // Simplify;
  LambdaRt = MatrixExp[t P0].St.MatrixExp[-t P0] // Simplify; 
  LambdaRtsw = MatrixExp[tswgon P0].Stsw.MatrixExp[-tswgon P0] // Simplify; 
  Ham0 = Tr[(Lambda100 - (3/2) lambdacost J).X00] - 
     Tr[LambdaR00.Z001]/Tr[X00.Z001] // Simplify; 
  Xtsw = MatrixExp[tswgon P0].X00.MatrixExp[-tswgon P0] // Simplify; 
  P1tsw = Z100/Tr[Z100.Xtsw] // Simplify; 
  P3tsw = Z001/Tr[Z001.Xtsw] // Simplify; 
  Switch31 = Tr[LambdaRtsw.(P1tsw - P3tsw)] // Simplify; 
   sol = Solve[{Ham0 == 0, Switch31 == 0}, {lambdaR, lambda1}]//Only // 
    Simplify; 
  LambdaRtV = LambdaRt /. sol // Simplify; 
  LambdaRtswV = LambdaRtsw /. sol // Simplify;
  (* transversality of Lambda_R(t1)*)
  
  transversalityTest = LambdaRtswV - Inverse[R].LambdaR00.R /. sol // Simplify;
  Claim[transversalityTest == {{0, 0}, {0, 0}}, "transvers-error"];
  (*values of lambdaR,lambda1 reported in book*)
  sol;
  (*value of d= \det(\Lambda_1) reported in book*)
  
  detLambda1V = Det[Lambda100 /. sol] // Simplify;
  (* monotonicity of d *)
  D[detLambda1, y0] // Simplify;
  (* Plot[detLambda1, {y0, 1/Sqrt[3], 1}] *)

  Join[sol, {X0 -> X00,Lambda10->(Lambda100/.sol),LambdaR0->(LambdaRtV/.t->0),detLambda1 -> detLambda1V,LambdaR->LambdaRtV}]
  ];

triangleSub := 
 Module[{doc = 
    "Better version of triangleSub. Use-book-formula solve for \
LambdaR, special initial conditions," <> 
     "hyperbolic triangle used for 6k+2-gon, MCA:9670173", LambdaR00, 
   X00, claim, lambdacost = -1, P0, Lambda100, Xt, Lambda1t, LambdaRt,
    Ham0, P1tsw, P3tsw, Switch31, sol, LambdaRtV, ddet, LambdaRtswV, 
   transversalityTest, detLambda1V, skip, sqrtmdet},
  LambdaR00 = lambdaR {{0, y0^2}, {1, 0}};
  X00 = (Phiz /. {x -> 0, y -> y0});
  P0 = P001[X00];
  Lambda100 = (Lambda10 /. subLambda10);
  claim = {Tr[LambdaR00.X00] == 0, 
      Tr[LambdaR00.(P001[X00] - P010[X00])] == 0} // Simplify // Union;
  Claim[claim == {True}, "LambdaR-ode-error, MCA:9670173"];
  sqrtmdet = Sqrt[3] y0/2;
  Claim[-Det[P0] == sqrtmdet^2, "det, MCA:9670173"];
  {Xt, Lambda1t, LambdaRt} = 
   constantControlSolutionPreComputeDet[Z001, X00, Lambda100, 
      LambdaR00, Sqrt[3] y0/2] /. {t -> tswgon} // Simplify;
  P1tsw = Z100/Tr[Z100.Xt] // Simplify;
  P3tsw = Z001/Tr[Z001.Xt] // Simplify;
  Ham0 = Tr[(Lambda100 - (3/2) lambdacost J).X00] - 
     Tr[LambdaR00.Z001]/Tr[X00.Z001] // Simplify;
  Switch31 = Tr[LambdaRt.(P1tsw - P3tsw)] // Simplify;
  sol = Solve[{Ham0 == 0, Switch31 == 0}, {lambdaR, lambda1}] // 
     Only // Simplify;
  LambdaRtV = LambdaRt /. sol // Simplify;
  LambdaRtswV = LambdaRt /. sol // Simplify;
  (*transversality of Lambda_R(t1)*)
  transversalityTest = 
   LambdaRtswV == Inverse[R].LambdaR00.R /. sol // Simplify;
  Claim[transversalityTest, "MCA:9670173, transvers-error"];
  (*values of lambdaR,lambda1 reported in book*)
  sol;
  (*value of d= \det(\Lambda_1) reported in book*)
  detLambda1V = Det[Lambda100 /. sol] // Simplify;
  (* range *)
  
  Claim[And[0 == detLambda1V /. y0 -> 1/Sqrt[3], 
    9/4 == detLambda1V /. y0 -> 1], "range MCA:9670173"];
  (*monotonicity of d*)
  
  ddet = D[detLambda1V, y0] y0^9 // Simplify // Echo;
  Plot[ddet, {y0, 1/Sqrt[3], 1}] // Echo;
  ddet = ddet /. {y0 -> 1 - t};
  Series[ddet, {t, 0, 2}] // Echo; 
  Join[sol, {X0 -> X00, Lambda10 -> (Lambda100 /. sol), 
    LambdaR0 -> (LambdaRtV /. t -> 0), detLambda1 -> detLambda1V, 
    LambdaR -> LambdaRtV}]
   ];       


(* analysis of positivity of switching functions *)
(* positivity of switching functions *)

switch31t := switch31t = 
       Module[{doc="initial condition z=0+y0 I",P1, P3, LambdaRtV, X0, P0, Xt}, 
  X0 = (Phiz /. {x -> 0, y -> y0});
  P0 = P001[X0];
  Xt = MatrixExp[t P0].X0.MatrixExp[-t P0] // Simplify;
  LambdaRtV = LambdaR /. triangleSub;
  P1 = Z100/Tr[Z100.Xt] // Simplify;
  P3 = Z001/Tr[Z001.Xt] // Simplify;
  Tr[LambdaRtV.(P1 - P3)] // Simplify];

switch32t := switch32t = 
	      Module[{doc="initial condition z=0+y0 I",P2, P3, LambdaRtV, X0, P0, Xt}, 
  X0 = (Phiz /. {x -> 0, y -> y0});
  P0 = P001[X0];
  Xt = MatrixExp[t P0].X0.MatrixExp[-t P0] // Simplify;
  LambdaRtV = LambdaR /. triangleSub;
  P2 = Z010/Tr[Z010.Xt] // Simplify;
  P3 = Z001/Tr[Z001.Xt] // Simplify;
  Tr[LambdaRtV.(P2 - P3)] // Simplify];

switchPrincipalObsolete := 
  Module[{part32List, mainpartA, mainpart, mainpart1, mainpart2}, 
   part32List = Apply[List, switch32t];
   EchoOff[part32List];
   mainpartA = -(part32List // Last) // Simplify;
   mainpart = 
    switch32t *(3/2)*E^(Sqrt[3] t y0)*y0^3*(2 - E^(Sqrt[3]*t*y0)) // 
     Simplify;
   Claim0[mainpartA - mainpart // Simplify, "parts"];
   mainpart1 = 
    mainpart /. {t -> (Log[r] - Log[(1 + 3 y0^2)])/(Sqrt[3] y0)} // 
     FullSimplify;
   mainpart2 = 
    y^2 mainpart1 /. {y0 -> Sqrt[(y - 1)]/Sqrt[3]} // FullSimplify;
   mainpart2];

switchPrincipal := 
 Module[{doc = "PMP for 6k+2 gon, MCA:6384505", yf, rf, f, part32List,
    mainpartA, mainpart, mainpart1, df2},
  part32List = Apply[List, switch32t];
  Claim[switch31t == (switch32t /. {t -> tswgon - t}) // Simplify, 
   "MCA:6384505 sym"];
  mainpartA = -(part32List // Last) // Simplify;
  mainpart = 
   switch32t*(3/2)*E^(Sqrt[3] t y0)*y0^3*(2 - E^(Sqrt[3]*t*y0)) // 
    Simplify;
  Claim[mainpartA == mainpart // Simplify, "MCA:6384505, parts"];
  yf = 1 + 3 y0^2;
  rf = yf E^(Sqrt[3] y0 t);
  Claim[4 == rf /. t -> tswgon // Simplify, "MCA:6384505, rmax"];
  mainpart1 = 
   mainpart /. {t -> (Log[r] - Log[(1 + 3 y0^2)])/(Sqrt[3] y0)} // 
    FullSimplify;
  f = y^2 mainpart1 /. {y0 -> Sqrt[(y - 1)]/Sqrt[3]} // FullSimplify;
  Echo[{"f(y,r)=", f}];
  Claim0[f /. {r -> y}, "MCA:6384505, diag"];
  Echo[{"Df-diag", D[f, y] /. {r -> y} // Simplify, 
    "MCA:6384505, Ddiag"}];
  df2 = D[f, {y, 2}] // Simplify // Echo;
  ContourPlot[df2, {y, 2, 4}, {r, 2, 4}] // Echo;
  df2 /. {y -> 4, r -> 4} // Echo
	];	     

  smoothedOct := 
 Module[{doc = "MCA:9434755", thetak, y8, t8, X0, P0, Xt, int},
  thetak = Pi k/(3 k + 1) /. k -> 1;
  Claim[Pi/4 == thetak, "MCA:9434755"];
  y8 = Only[
    Select[y0 /. Solve[4/(3 y0^2 + 1) == 2 Cos[thetak], y0], 
     Positive]];
  Claim[y8 == Sqrt[(Sqrt[8] - 1)/3], "MCA:9434755"];
  t8 = tswgon /. y0 -> y8;
  Claim[t8 == Log[2]/(2 Sqrt[Sqrt[8] - 1]), "MCA:9434755,"];
  X0 = (Phiz /. {x -> 0, y -> y8});
  P0 = P001[X0];
  Xt = MatrixExp[t P0].X0.MatrixExp[-t P0] // Simplify;
  int = -6 Integrate[Tr[Xt.J], {t, 0, t8}] // Simplify;
  Claim[int == Sqrt[12] (8 - Sqrt[32] - Log[2])/(Sqrt[8] - 1) // 
    Simplify, "MCA:9434755"];
  int // N
	];

  smoothed2kp2 := Module[{doc = "MCA:1624111 6k+2", X0, P0, Xt, denom},
  X0 = (Phiz /. {x -> 0, y -> y0});
  P0 = P010[X0];
  Xt = MatrixExp[t P0].X0.MatrixExp[-t P0] // Simplify // Echo;
  Claim[R.X0.Inverse[R] == Xt /. t -> -tswgon // Simplify, 
   "MCA:1624111, transversality"];
  denom = Tr[Z010.Xt] /. {t -> -tswgon} // Simplify;
  Plot[tswgon, {y0, 1, 5}] // Echo;
		      ];

(* wbc-coordinates, equilibrium (circle solutions) *)

(* global defs for wbc coordinates *)
(* XX Notation changes in paper w_1 -> tilde w, z_1 -> tilde z, etc *)
(* DONE: beta1->rho, *)

sq[x_, xc_] := Sqrt[1 + x*xc];
esq[x_,xc_]:= Sqrt[e + x*xc];
RRc[w_, wc_, z_, zc_] := (wc*z + w*zc)/2;
Xw = {{-I sq[w, wc], w}, {wc, I sq[w, wc]}};
L1b = d1 {{I esq[b, bc], b}, {bc, -I esq[b, bc]}};
LRc = {{-I RRc[c, cc, w, wc]/sq[w, wc], c}, {cc, 
    I RRc[c, cc, w, wc]/sq[w, wc]}};
Zsu = alpha {{-I, rho z}, {rho zc, I}};
Psu = Zsu/Tr[Xw.Zsu];
muw = sq[w, wc] - rho RRc[w, wc, z, zc];
muw1 = sq[w1, w1c] - rho RRc[w1, w1c, z1, z1c];

wbc2z[{w_,b_,c_},rho_]:= {w/rho,-I b/(2 rho),c/(6 rho)};
wbceqs = (* {z3 == c/(6 rho), z2 == -I b/(2 rho), z1 == w/rho}; *)
Module[{z1r,z2r,z3r},
       {z1r,z2r,z3r}=wbc2z[{w,b,c},rho];
       {z1==z1r,z2==z2r,z3==z3r}];


test:=Module[{diff},
       diff=(muw - muw1 /. {w1 -> cc*w/Sqrt[c*cc],
    w1c -> c*wc/Sqrt[c*cc], z1 -> cc*z/Sqrt[c*cc],
    z1c -> c*zc/Sqrt[c*cc]}) // Simplify;
    Claim0[diff,"check-muw1"]];

Jsu = Cayley[J];

(* Matrix Identities of Appendix *)

moduleLieAlgebraIdentity:=
	Module[{doc = "verification of A.1.3, sl2 Lie algebra identity", f, a,
    b, c, d, b1, b2, b3, bb, ff}, 
  f[a_, b_, c_, d_] := 
   Tr[a.c]*Tr[b.d] - Tr[b.c]*Tr[a.d] + (1/2) Tr[br[a, b].br[c, d]];
  b1 = {{1, 0}, {0, -1}};
  b2 = {{0, 1}, {0, 0}};
  b3 = {{0, 0}, {1, 0}};
  bb = {b1, b2, b3};
  ff[i1_, i2_, i3_, i4_] := 
   f[bb[[i1]], bb[[i2]], bb[[i3]], bb[[i4]]] // Simplify;
  Table[ff[i, j, k, l], {i, 1, 3}, {j, 1, 3}, {k, 1, 3}, {l, 1, 3}] //
  Flatten // Union];

LieAlgebraIdentity:=Module[{doc = "Lie algebra identity"},
 br[J, br[J, br[J, X]]] == -4 br[J, X] // Simplify
		    ];

test8252847:=Module[{doc = "Appendix. Matrix Identities, MCA:8252847", X, Y, Z, 
  W},
 X = {{x11, x12}, {x21, -x11}};
 Y = {{y11, y12}, {y21, -y11}};
 Z = {{z11, z12}, {z21, -z11}};
 W = {{w11, w12}, {w21, -w11}};
 Claim[Tr[X.Z]*Tr[Y.W] - 
     Tr[Y.Z]*Tr[X.W] == -(1/2) Tr[br[X, Y].br[Z, W]] // Simplify, 
  "MCA:8252847"];
 Claim[br[X, br[X, Y]] == 2 Tr[X.X] Y - 2 Tr[X.Y] X // FullSimplify, 
  "MCA:5358122 ad^2"];
 Claim[br[X, br[X, Y]] == -2 Det[X] Y - 2 X.Y.X // FullSimplify, 
  "MCA:8252847"];
 Claim[Tr[br[X, Y].br[Z, W]] == - 2 Tr[X.Z]*Tr[Y.W] + 
     2 Tr[Y.Z]*Tr[X.W] // FullSimplify, "MCA:8252847"];
 Claim[X.X == -Det[X] I2];
 ];

circularControlCalcs:=Module[{doc = "MCA:5358122 circular control arithmetic", 
  zeta = -1/2 + I Sqrt[3]/2, Js, Z, LR, X1, quadratic},
 Claim[(1/3) {{-I, 
        2 (u0 + zeta u1 + zeta^2 u2)}, {2 (u0 + zeta^2 u1 + zeta u2), 
        I}} == Cayley[X /. abcsub] /. {u2 -> 1 - u1 - u0} // 
   FullSimplify, "MCA:5358122, cayley"];
 Claim0[(u0 + zeta u1 + zeta^2 u2)*(u0 + zeta^2 u1 + zeta u2) - (3/
        2) (u0^2 + u1^2 + u2^2) + (u0 + u1 + u2)^2/2 // Expand // 
   Factor, "MCA:5358122, circle map"];
 Claim[(1 - 4 (3 r^2 - 1)/2)/9 == (1 - 2 r^2)/3 // Simplify, 
  "MCA:5358122 r-value"];
 Claim[(2/3) (3 r^2 - 1)/(1/3) == (6 r^2 - 2) // Simplify, 
  "MCA:5358122 rho"];
 Claim[Cayley[J] == {{-I, 0}, {0, I}}, "MCA:5358122 Cayley J"];
 {Js, Z, LR, 
   X1} = {{{Js11, Js12}, {Js21, -Js11}}, {{Z11, 
     Z12}, {Z21, -Z11}}, {{LR11, LR12}, {LR21, -LR11}}, {{X11, 
     X12}, {X21, -X11}}};
 doc = "Here Js is short for [Jsu,Z]";
 Claim[Tr[Js.LR]*Tr[Z.X1] - 
     Tr[Z.LR]*Tr[Js.X1] == -Tr[br[Js, Z].br[LR, X1]]/2 // 
   FullSimplify, "MCA:5358122, tr-br"];
 Claim[br[Z, br[Z, Js]] == 2 Tr[Z.Z] Js - 2  Tr[Z.Js] Z  // 
   FullSimplify, "MCA:5358122 ad^2"];
 Z = {{-I alpha, beta z}, {beta/z, I alpha}};
 Claim[Tr[Z.Z]/Tr[Z.Jsu] == (alpha^2 - beta^2)/alpha // Simplify, 
  "MCA:5358122"];
 doc = "Here LR is short for [LambdaR,Z]";
 quadratic = alpha LR21 z^2 - 2 I beta LR11 z + alpha LR12;
 Claim[((alpha z/beta) (Tr[
         Z.LR] - (alpha^2 - beta^2)/alpha Tr[Jsu.LR]) == quadratic) //
    Simplify, "MCA:5358122 quadratic"];
 Solve[quadratic == 0, z] // Echo;
		      ];

hyperboloidCals:= Module[{doc = "MCA:1790833", tv, zv, Z},
 zv = (b + c)/2 + I a;
 tv = (b - c)/2;
 Claim[Cayley[X] == {{I tv, zv}, {Conjugate[zv], -I tv}} // 
   ComplexExpand, "MCA:1790833"];
 Jsu;
 Claim[Det[Xw] == 1, "MCA:1790833 detX"];
 Claim[Det[L1b] == d1^2 e, "MCA:1790833 det1"];
 Claim0[Tr[Xw.LRc], "MCA:1790833 ortho"];
 Cayley[Phiz] // Simplify;
 Zstar = {{-I alpha, beta z}, {beta/z, I alpha}} /. 
   beta -> alpha rho;
 Claim0[-Tr[Xw.Zstar]/(2 alpha) - (
        sq[w, wc] - rho RR[w, z]) /. {z -> Exp[I theta], w -> u + I v,
        wc -> u - I v} // Simplify // ComplexExpand // Simplify, 
  "MCA:1790833 mu"];
 ];

wpData = Module[{tag = "MCA:eqn-w", Xwp, XwODE, Xw12paper, diff},
   Xwp = Module[{Xwt, DXwt},
     Xwt = Xw /. {w -> w[t], wc -> wc[t]};
     DXwt = 
      D[Xwt, t] /. {w'[t] -> wp, wc'[t] -> wcp, w[t] -> w, wc[t] -> wc}
     ];
   XwODE = br[Psu, Xw] // Simplify;
   Xw12paper = (I (w - rho sq[w, wc] z)/muw);
   diff = {Xwp[[1, 2]], XwODE[[1, 2]] - Xw12paper} // Simplify;
   Claim0[diff[[2]], "ODE for w"];
   Xw12paper
   ];

bpData = Module[{tag = "MCA:eqn-b", L1bt, DL1bt, L1bODE, L1bpaper, r, 
    s},
   L1bt = L1b /. {b -> b[t], bc -> bc[t]};
   DL1bt = 
    D[L1bt, t] /. {b'[t] -> bp, bc'[t] -> bcp, b[t] -> b, bc[t] -> bc};
   L1bODE = br[L1b, Xw][[1, 2]];
   L1bpaper = 2 I (esq[b, bc] w + b sq[w, wc]);
   r = {DL1bt[[1, 2]], L1bODE}/d1 // Simplify;
   s = { r[[1]], r[[2]] -  L1bpaper} // Simplify; 
   Claim0[s[[2]], "b ODE"];
   L1bpaper
	 ];

bpDataAlt = 
 Module[{doc = "MCA:2384598, neck coordinates", L1, DL1, LD1ode, paper, sol},
  L1 = d1 {{I r[t], (Cos[theta] + I Sin[theta]) Sqrt[r[t]^2 + 1]},
      {(Cos[theta] - I Sin[theta]) Sqrt[r[t]^2 + 1], -I r[t]}} /. 
    theta -> theta[t];
  DL1 = D[L1, t] /. {theta[t] -> theta, theta'[t] -> thetap, 
     r[t] -> r, r'[t] -> rp};
  DL1ode = br[L1, Xw] /. {theta[t] -> theta, r[t] -> r};
  "sol";
  sol = ({rp, thetap} /. 
        Solve[{DL1[[1, 1]] == DL1ode[[1, 1]], 
          DL1[[1, 2]] == DL1ode[[1, 2]]}, {rp, thetap}] // 
       Only) /. {w -> u + I v, wc -> u - I v} // Simplify;
  (sol[[2]] - 2 Sqrt[1 + u^2 + v^2]) Sqrt[r^2 + 1]/(2 r) // Simplify;
  "paper";
  paper = {2 Sqrt[1 + r^2] RR[I (u + I v), Cos[theta] + I Sin[theta]],
      2 Sqrt[1 + u^2 + v^2] + 
      2 r RR[(u + I v), Cos[theta] + I Sin[theta]]/Sqrt[1 + r^2]} // 
    ComplexExpand;
  Claim[sol == paper // Simplify // ComplexExpand, "MCA:2384598"]
  ];

Hamwbccontrol = - RRc[w - rho sq[w, wc] z, wc - rho sq[w, wc] zc, c, 
       cc]/(muw sq[w, wc]);

Hamwbc = Module[{doc="Hamiltonian in wbc coordinates",
    tag = "MCA:ham-wbc", lambda = -1, ham, hampaper, 
    diff}, 
   ham = Tr[(L1b - (3 lambda/2) Jsu).Xw] - Tr[LRc.Psu];
   hampaper = (2 d1 RRc[w, wc, b, bc] + (2 d1 esq[b, bc] + 3*lambda) sq[w, 
         wc]) +Hamwbccontrol;
   diff = ham - hampaper // Simplify;
   Claim0[diff, "ham-wbc"];
   hampaper] // Simplify;

Angwbc = Module[{doc = "Angular momentum in wbc coordinates",
   tag = "MCA:ang-wbc", ang, angpaper, diff},
  ang = Tr[Jsu.(L1b + LRc)];
  angpaper = 2 d1 esq[b, bc] - 2 RRc[w, wc, c, cc]/sq[w, wc];
  diff = ang - angpaper // Simplify;
  Claim0[diff, "ang-wbc"];
  angpaper];

(* Check of ODE for c *)

(* notation change a1,2*b1,a1c -> xi0,xi1,xi2. *)

z1quad = Module[{doc = 
    "z1-quadratic eqn" <> "differentiate wrt cis(theta)", 
   tag = "MCA:z1-quadratic", f1, f2, f3, fac, paper, xi0, xi0c, xi1}, 
  f1 = -RRc[w1 - rho sq[w1, w1c] z1, w1c - rho sq[w1, w1c] z1c, 
     Sqrt[c*cc], Sqrt[c*cc]]/(muw1);
  f2 = f1 /. {z1 -> z1*E^(I theta), z1c -> z1c*E^(-I theta)};
  xi0 = 2 + w1*w1c - w1^2;
  xi0c = 2 + w1*w1c - w1c^2;
  xi1 = 2*rho sq[w1, w1c] (w1 - w1c);
  paper = xi0 + xi1 z1 - xi0c z1^2;
  fac = -I rho*Sqrt[c*cc]/(4*z1*muw1^2);
  f3 = Simplify[D[f2, theta]/fac /. {theta -> 0, z1c -> 1/z1}];
  Claim0[f3 - paper // Simplify, "z1-quadratic"];
  {paper, {xi0, xi1, xi0c}}];

cpData = Module[{doc = "check ODE for c and formula eq:wc'", 
   tag = "MCA:eqn-c MCA:eqn:wc'",
   LRct, DLRct, LRcODE, lambda = -1, term1, term2, 
   term1paper, term1diff, wcp, wcpaper, wcdiff, term2paper, 
   term2paperAlt, t3, ca1, cca1c, sqrt, t4, xi0, xi1, xi0c, xi1c, sqrtsub,
    t5}, LRct = 
   LRc /. {c -> c[t], cc -> cc[t], w -> w[t], wc -> wc[t]};
  DLRct = 
   D[LRct, t] /. {c'[t] -> cp, cc'[t] -> ccp, c[t] -> c, cc[t] -> cc, 
     w'[t] -> wp, wc'[t] -> wcp, w[t] -> w, wc[t] -> wc};
  term1 = br[-L1b + (3 lambda/2) Jsu, Xw] // Simplify;
  term1paper = -I ((2 d1 esq[b, bc] + 3 lambda) w + 
      2 d1 b sq[w, wc]);
  term1diff = (term1[[1, 2]] - term1paper) // Simplify;
  Claim0[term1diff, "ODE for c term 1"];
  wcp = {LRc[[2, 2]], term1[[2, 2]]}/I;
  wcpaper = {RRc[w, wc, c, cc]/sq[w, wc], 2 d1 RRc[I w, -I wc, b, bc]};
  wcdiff = wcp - wcpaper // Simplify;
  Claim[wcdiff == {0, 0}, "eq:wc'"];
  term2 = (br[Psu, LRc] - Tr[LRc.Psu]*br[Psu, Xw]) // Simplify;
  xi0 = (2 + w1*w1c - w1^2);
  xi0c = (2 + w1*w1c - w1c^2);
  xi1 = 2*rho (w1 - w1c)*sqrt;
  xi1c = -xi1;
  ca1 = 2 c + w*wc*c - w^2*cc;
  cca1c = 2 cc + w*wc*cc - wc^2*c;
  term2paper = 
   I*Sqrt[c*cc]*(1 - rho^2)*RRc[xi0, xi0c, z1, z1c]*
    z/(2 sq[w, wc]*muw^2);
  term2paperAlt = 
   I*(1 - rho^2)*RRc[ca1, cca1c, z, zc]*z/(2 sq[w, wc]*muw^2);
  LRcODE = term1 + term2[[1, 2]];
  term2[[2, 2]] // Simplify;
  t3 = ({term2, term2paperAlt} 4 I cc sq[w, wc] muw^2/c) /. {zc -> 
        1/z} /. {z -> c*z1/Sqrt[c*cc], w -> w1 c/Sqrt[c*cc], 
      wc -> w1c cc/Sqrt[c*cc]} // Simplify;
  sqrtsub = Solve[xi0 + xi1 z1 - xi0c z1^2 == 0, sqrt]//Only;
  t4 = t3 /. {Sqrt[1 + w1*w1c] -> sqrt, z1c -> 1/z1} /. sqrtsub // 
    Simplify;
  t5 = Collect[(t4[[1, 1, 2]] - t4[[2]]) // Simplify, z1];
  Claim0[t4[[1, 2, 2]], "eq:wc'-part2"];
  Claim0[t5, "ODE for c term 2"];
  term1paper + term2paperAlt];

(* Application to non-existence of periodic abnormal solutions when rho=1 *)

test6051339:=Module[{doc = "MCA:6051339. Derive ODE", Xwt, Dxw, Dxwode, wpsol, xi0, xi0c, eta2},
  Xwt = Xw /. {w -> w[t], wc -> wc[t]};
  Dxw = D[Xwt, t] /. {w'[t] -> wp, w[t] -> w, wc'[t] -> wcp, 
     wc[t] -> wc};
  Dxwode = br[LRc, Xw] // Simplify;
  wpsol = 
   Solve[{Dxw[[1, 2]] == r Dxwode[[1, 2]], 
       Dxw[[2, 1]] == r Dxwode[[2, 1]]}, {wp, wcp}] // Only // Echo;
  Claim[(Dxw == r Dxwode) /. wpsol // Simplify, "MCA:6051339 ode"];
  xi0 = (2 + w*wc - w^2 cc^2/(cc *c));
  xi0c = (2 + w * wc - wc^2 c^2/(cc *c));
  eta2 = xi0 + xi0c;
  Claim[Tr[LRc.LRc]/2 == c*cc eta2/(4 (1 + w*wc)) // Simplify, 
   "MCA:6051339"];
  Claim[L1b + LRc == 
     I Angwbc/2 {{1, 0}, {0, -1}} + {{0, c + b d1}, {cc + bc d1, 0}} //
     Simplify, "MCA:6051339"];
  Claim[Hamwbc - Hamwbccontrol + 3 Sqrt[1 + w wc] == Tr[Xw.L1b] // 
    Simplify, "MCA:6051339"];
  br[-L1b, Xw] // Factor
	     ];

testRhoAbnormal := 
 Module[{doc = 
    "MCA:5220458,calc of f0^2 appearing in eq:eqn-w, when rho=1", 
   tag = "MCA:rho-abnormal eqn:X'L (squared)", lhs, f1, f2, f3, xi1, 
   sol, quadpaper, xi0paper, xi1paper, xi0cpaper, Lsub, L1sub, Lval, 
   Lpaper},
  lhs = (w - sq[w1, w1c] z)/muw;
  Lsub = {L -> c (2 + w1*w1c - w1^2)*L1};
  f1 = 2 z*z1*cc*Sqrt[c*cc]*
         muw^2*(lhs^2 - L)/(c) /. {zc -> 1/z} /. {rho -> 1, 
        z -> c*z1/Sqrt[c*cc], w -> c*w1/Sqrt[c*cc], 
        wc -> cc*w1c/Sqrt[c*cc]} /. Lsub /. {sq[w1, w1c] -> sqw} // 
    Simplify;
  {quadpaper, {xi0paper, xi1paper, xi0cpaper}} = 
   z1quad /. {rho -> 1};
  f2 = (Collect[f1, 
         z1] /. {z1^4 -> (xi0paper + xi1paper z1)*z1^2/xi0cpaper})*
      xi0cpaper // Simplify // Factor;
  f2 = (Collect[f2, 
         z1] /. {z1^3 -> (xi0paper + xi1paper z1)*z1^1/xi0cpaper})*
      xi0cpaper // Simplify // Factor;
  L1sub = {L1 -> L2*sqw};
  f2 = f2*(2 + w1*w1c - w1^2)/(f2 /. z1 -> 0) /. L1sub // FullSimplify;
  xi1 = D[f2, z1] /. {z1 -> 0};
  sol = Solve[xi1 == xi1paper /. {rho -> 1}, L2] // Only // Simplify;
  f3 = f2 /. sol /. {sqw -> sq[w1, w1c]} // FullSimplify;
  Claim0[f3 - quadpaper // Simplify, "fail-f3"];
  Lpaper = c^2 (xi0paper^2)/(c*cc*(xi0paper + xi0cpaper));
  Lval = L /. Lsub /. L1sub /. sol /. {sqw -> sq[w1, w1c]} // Simplify;
  Claim0[Lval - Lpaper // Simplify, "fail-Lval"];
  Lpaper];


(* DEBUG: TCH 5/2/2024 corrected. *)

calcD3LRLR0 := 
 Module[{doc = "MCA:4147879,abnormal-third-derivative of <LR,LR>", 
   tag = "MCA:LR-triple", Apaper, K, Kpaper, K12sub, rpaperA, eqB, 
   bsub, cp, cppaper, ccppaper, ccp, r, rp, rp1, rpaper, etasub, 
   w1sub, wpsub, fac, paper, ham1, ham2, ham, hamAlt, xi0, xi1, xi0c, 
   skip, rp2}, K = L1b + LRc;
  Apaper = 2*d1*esqb - 2 RRc[w, wc, c, cc]/sq[w, wc];
  Claim[Angwbc == Apaper /. esqb -> Sqrt[e + b bc], 
   "MCA:4147879 Angwbc"];
  K12sub = {A -> (Apaper /. esqb -> esq[b, bc]), K12 -> d1*b + c, 
    K12c -> d1*bc + cc};
  Kpaper = {{I A/2, K12}, {K12c, -I A/2}};
  Claim[(K - Kpaper /. K12sub // Simplify) == {{0, 0}, {0, 0}}, "K"];
  "eliminate b" // Echo;
  eqB = {Apaper == A, K12 == d1*b + c};
  bsub = Solve[eqB, {esqb, b}] // Only;
  {paper, {xi0, xi1, xi0c}} = z1quad // Echo;
  cp = -d1*bpData /. {esq[b, bc] -> esqb} /. bsub // Simplify;
  ccp = -cp /. {K12 -> K12c, K12c -> K12, w -> wc, wc -> w, c -> cc, 
      cc -> c} // Echo;
  w1sub = {w1 -> cc*w/Sqrt[c*cc], w1c -> c*wc/Sqrt[c*cc]};
  cppaper = I xi0*c/sq[w, wc] - I*(w*A + 2*K12*sq[w, wc]) /. w1sub;
  ccppaper = -cppaper /. {K12 -> K12c, K12c -> K12, w -> wc, wc -> w, 
      c -> cc, cc -> c} /. w1sub;
  Claim0[cp - cppaper // Simplify, "cp-error 1"];
  Claim0[ccp - ccppaper // Simplify, "cp-error 2"];
  "ham" // Echo;
  ham1 = Tr[Xw.Kpaper];
  ham2 = Sqrt[c*cc]*eta/sq[w1, w1c]/2;
  ham = 2 d1*RRc[w, wc, b, bc] + 2*d1*esq[b, bc]*sq[w, wc] + ham2;
  hamAlt = ham1 + ham2;
  Claim0[hamAlt - ham /. K12sub // Simplify, "ham1+ham2-error"];
  etasub = Only[Solve[hamAlt == 0, eta]] /. w1sub // Simplify;
  "r" // Echo;
  r = Tr[br[LRc, Xw].K] // Simplify;
  rpaperA = Tr[br[LRc, Xw].Kpaper] // Simplify;
  rpaper = (c*wc - cc*w)*I*
        A + (I/sq[w, wc])*(K12c*xi0*c - K12*xi0c*cc) /. w1sub // 
     Simplify // Echo;
  Claim0[r - rpaper /. K12sub // Simplify, "r"];
  wpsub = {w'[t] -> -I*xi0*c/(Sqrt[c*cc]*eta), 
     wc'[t] -> I*xi0c*cc/(Sqrt[c*cc]*eta)} /. w1sub;
  fac = Sqrt[c*cc]*eta/sq[w, wc] - (K12c w + K12 wc + A sq[w, wc]) /. 
    w1sub;
  rp = (2*hamAlt*fac /. w1sub) + 
        D[rpaper /. {c -> c[t], cc -> cc[t], w -> w[t], wc -> wc[t]}, 
         t] /. {c[t] -> c, cc[t] -> cc, w[t] -> w, wc[t] -> wc, 
        c'[t] -> cppaper, cc'[t] -> ccppaper} /. wpsub /. w1sub // 
    Simplify;
  rp1 = (rp /. {eta^2 -> xi0 + xi0c} /. w1sub // 
         Simplify) /. {eta^2 -> xi0 + xi0c} /. w1sub // Simplify // 
    Factor;
  rp2 = D[rp1 /. {c -> c[t], cc -> cc[t], w -> w[t], wc -> wc[t]}, 
        t] /. {c[t] -> c, cc[t] -> cc, w[t] -> w, wc[t] -> wc, 
        c'[t] -> cppaper, cc'[t] -> ccppaper} /. wpsub /. w1sub // 
    Simplify;
  Claim0[rp2, "MCA:4147879 r''[t]=0"]];

HamAsymptotics := 
 Module[{doc = "asymptotics MCA:1897827", tsub, ham, ang, wbcsub},
  tsub = {w -> t w, wc -> t wc, b -> t^2 b, bc -> t^2 bc, c -> t^3 c, 
    cc -> t^3 cc, d1 -> 3/2, e -> 1, z -> c/Sqrt[c*cc] + a t, 
    zc -> cc/Sqrt[c*cc] + ac t}; 
  ham = Series[Hamwbc /. tsub, {t, 0, 3}] // Echo;
  ang = Series[Angwbc /. tsub, {t, 0, 4}] // Echo;
  Solve[wbceqs, {w, b, c}];
  wbcsub = {w -> rho z1, wc -> rho z1c, b -> 2 I rho z2, 
    bc -> -2 I rho z2c, c -> 6 rho z3, cc -> 6 rho z3c};
  Simplify[ham /. wbcsub, rho > 0] // Echo;
  ang /. wbcsub // Echo
  ];

FullerPoisson := 
 Module[{doc = "nonstandard poisson bracket,MCA:9136594", poisson, 
   z1v, z2v, z3v, hamFv, angFv, hamF, angF, vecs, p2, zsub, spiralsub},
  doc = "{{z1,z2,z3},{z1c,z2c,z3c}}"; 
  poisson[f_, 
    g_] := (2/I) (f[[1, 1]] *g[[2, 3]] - f[[2, 3]]*g[[1, 1]]) + (2/
       I) (-f[[1, 2]]*g[[2, 2]] + f[[2, 2]]*g[[1, 2]]) + (2/
       I) (f[[1, 3]]*g[[2, 1]] - f[[2, 1]]*g[[1, 3]]);
  z1v = {{1, 0, 0}, {0, 0, 0}};
  z2v = {{0, 1, 0}, {0, 0, 0}};
  z3v = {{0, 0, 1}, {0, 0, 0}};
  hamF = I/2 (z2 z1c - z2c z1) + Sqrt[z3 z3c];
  angF = z2 z2c - (z1 z3c + z1c z3);
  vecs[f_] := {{D[f, z1], D[f, z2], D[f, z3]}, {D[f, z1c], D[f, z2c], 
     D[f, z3c]}};
  hamFv = vecs[hamF];
  angFv = vecs[angF];
  Claim[poisson[z1v, hamFv] == - I z3/Sqrt[z3*z3c], 
   "MCA:9136594 z1"];
  Claim[poisson[z2v, hamFv] == z1, "MCA:9136594 z2"];
  Claim[poisson[z3v, hamFv] == z2, "MCA:9136594 z3"];
  Claim[poisson[angFv, hamFv] == 0 // Simplify, "MCA:9136594 angF"];
  doc = "Lie identity";
  p2[f_, g_] := (2/I) (D[f, z1]*D[g, z3c] - D[f, z3c]*D[g, z1]) + (2/
       I)*(-D[f, z2]*D[g, z2c] + D[f, z2c]*D[g, z2]) + (2/
       I)*(D[f, z3]*D[g, z1c] - D[f, z1c]*D[g, z3]);
  {f1, g1, h1} = {f[z1, z2, z3, z1c, z2c, z3c], 
    g[z1, z2, z3, z1c, z2c, z3c], h[z1, z2, z3, z1c, z2c, z3c]};
  Claim0[p2[f1, p2[g1, h1]] + p2[g1, p2[h1, f1]] + 
     p2[h1, p2[f1, g1]] // Simplify, "MCA:9136594 Jacobi"];
  zsub = {z1[t] -> z1, z1'[t] -> -I z3/Sqrt[z3*z3c], z1c[t] -> z1c, 
    z1c'[t] -> I z3c/Sqrt[z3*z3c], z2[t] -> z2, z2c[t] -> z2c, 
    z2'[t] -> z1, z2c'[t] -> z1c, z3[t] -> z3, z3c[t] -> z3c, 
    z3'[t] -> z2, z3c'[t] -> z2c};
  Claim0[D[
      hamF /. {z1 -> z1[t], z2 -> z2[t], z3 -> z3[t], z1c -> z1c[t], 
        z2c -> z2c[t], z3c -> z3c[t]}, t] /. zsub // Simplify, 
   "MCA:9136594 ham0"];
  Claim0[D[
      angF /. {z1 -> z1[t], z2 -> z2[t], z3 -> z3[t], z1c -> z1c[t], 
        z2c -> z2c[t], z3c -> z3c[t]}, t] /. zsub // Simplify, 
   "MCA:9136594 ang"];
  D[Sqrt[z3[t]*z3c[t]], t] /. zsub // Simplify;
  spiralsub = {z3 -> t^(3 - I)/10, z3c -> t^(3 + I)/10, 
    z2 -> (3 - I) t^(2 - I)/10, z2c -> (3 + I) t^(2 + I)/10, 
    z1 -> (3 - I) (2 - I) t^(1 - I)/10, 
    z1c -> (3 + I) (2 + I) t^(1 + I)/10};
  Claim0[Simplify[hamF /. spiralsub, t > 0], "MCA:9136594 spiral ham"];
  Claim0[Simplify[angF /. spiralsub, t > 0], "MCA:9136594 spiral ham"];
 ];

test8167780:= Module[{doc = 
   "MCA:8167780,real analytic manifold, grad AF,grad HF rank2. Assume r1r2r3\ne0. Needs cleaning up.  Better version in hand notes, Global Analysis III, 9/2/2021, page 13", hamF, 
  angF, dd, v, minor, sol, h0, a0, trigsub},
 hamF = I/2 (z2 z1c - z2c z1) + Sqrt[z3 z3c];
 angF = z2 z2c - (z1 z3c + z1c z3);
 minor[i_, j_] := Det[{Transpose[v][[i]], Transpose[v][[j]]}];
 trigsub = {z1 -> r1 (Cos[theta1] + I Sin[theta1]), 
   z1c -> r1 (Cos[theta1] - I Sin[theta1]), 
   z2 -> r2 (Cos[theta2] + I Sin[theta2]), 
   z2c -> r2 (Cos[theta2] - I Sin[theta2]), 
   z3 -> r3 (Cos[theta3] + I Sin[theta3]), 
   z3c -> r3 (Cos[theta3] - I Sin[theta3])};
 h0 = hamF /. trigsub // Simplify;
 a0 = angF /. trigsub // Simplify;
 dd[f_] := {D[f, r1], D[f, r2], D[f, r3], D[f, theta1], D[f, theta2], 
   D[f, theta3]};
 v = {dd[h0], dd[a0]} // Simplify // Echo;
 "case 1. Observe that linear dependence of last two rows forces trig" // Echo;
 v /. {theta2 -> theta1 + Pi/2 + Pi } // FullSimplify;
 {h0, a0, 
   v} = {h0, a0, v} /. {Sin[theta1 - theta3] -> 0, 
     Cos[theta1 - theta2] -> 0, Cos[theta1 - theta3] -> eps1, 
     Sin[theta1 - theta2] -> eps2} // Echo;
 {h0, a0, v} = {h0, a0, v} /. {eps1 -> 1, eps2 -> -1} // Echo;
 Solve[{minor[1, 2] == 0, a0 == 0}, {r1, r2}]
	      ];

FiberBundle := Module[{doc = "Omega fiber bundle", hamF, angF, zsub},
  hamF = I/2 (z2 z1c - z2c z1) + Sqrt[z3 z3c];
  angF = z2 z2c - (z1 z3c + z1c z3);
  zsub = {z1 -> 1, z1c -> 1, z2 -> x2 (eps2 cos2 + I sin2), 
    z2c -> x2 (eps2 cos2 - I sin2), z3 -> x3 (cos3 + I eps3 sin3), 
    z3c -> x3 (cos3 - I eps3 sin3)};
  hamF /. zsub // Simplify // Echo;
  angF /. zsub // Simplify // Echo;
	      ];

OmegaFlow := Module[{s2, c2, c3, s3, p1, p2, p3, v2, v3, v},
   s2 = x3/x2;
   c2 = Sqrt[1 - s2^2];
   c3 = x2^2/(2 x3);
   s3 = Sqrt[1 - c3^2];
   p1 = eps3 s3;
   p2 = eps2 c2;
   p3 = eps2 c2 c3 + eps3 s3 s2;
   v2 =  p2 - 2 x2 p1 // Simplify;
   v3 = x2 p3 - 3 x3 p1 // Simplify;
   "fixed points";
   Claim[{0, 0} == {v2, v3} /. {x2 -> 2, x3 -> 2}, "omega 22"];
   Claim[{0, 0} == {v2, v3} /. {x2 -> 2/Sqrt[10], x3 -> Sqrt[2]/5, 
      eps2 -> eps3}, "omega-star"];
   v = {v2, v3}/eps3 /. {eps2 -> eps3} // Simplify;
   Solve[{v == {0, 0}, x3 > 0, x2 > 0}, {x2, x3}] // Echo;
   "vector field";
   {v2, v3}
	     ];

flow[x2_, x3_, eps2_, 
   eps3_] := {-(eps3*x2*Sqrt[Abs[4 - x2^4/x3^2]]) + 
    eps2*Sqrt[
      Abs[1 - x3^2/x2^2]], -(eps3*Sqrt[Abs[4 - x2^4/x3^2]]*
       x3) + (eps2*x2^3*Sqrt[Abs[1 - x3^2/x2^2]])/(2*x3)};

StreamFlowOmegaGraphicsGrid5387527 = 
 Module[{doc = "MCA:5387527, Dynamical system on R_Omega Book Graphic Grid", flowpp, 
   flowmp, flowpm, flowmm, lp, fp, skip, Alabel, Blabel, Clabel, 
   Dlabel}, 
  flowpp = StreamPlot[
    flow[x2, x3, 1, 1], {x2, 0.01, 1.99}, {x3, 0.01, 1.99}, 
    RegionFunction -> 
     Function[{x2, x3, vx, vy, n}, And[x2^2/2 <=  x3 , x3 <= x2]], 
    PlotLabel -> "++"];
  flowmp = 
   StreamPlot[flow[x2, x3, -1, 1], {x2, 0.01, 1.99}, {x3, 0.01, 1.99},
     RegionFunction -> 
     Function[{x2, x3, vx, vy, n}, And[x2^2/2 <=  x3 , x3 <= x2]], 
    PlotLabel -> "-+"];
  flowpm = 
   StreamPlot[flow[x2, x3, 1, -1], {x2, 0.01, 1.99}, {x3, 0.01, 1.99},
     RegionFunction -> 
     Function[{x2, x3, vx, vy, n}, And[x2^2/2 <=  x3 , x3 <= x2]], 
    PlotLabel -> "+-"];
  flowmm = 
   StreamPlot[
    flow[x2, x3, -1, -1], {x2, 0.01, 1.99}, {x3, 0.01, 1.99}, 
    RegionFunction -> 
     Function[{x2, x3, vx, vy, n}, And[x2^2/2 <=  x3 , x3 <= x2]], 
    PlotLabel -> "--"];
  Alabel = ListPlot[{{1, 1} -> "A"}, PlotStyle -> PointSize[0.0]];
  Blabel = ListPlot[{{1, 0.5} -> "B"}, PlotStyle -> PointSize[0.0]];
  Clabel = ListPlot[{{1, 1} -> "C"}, PlotStyle -> PointSize[0.0]];
  Dlabel = ListPlot[{{1, 0.5} -> "D"}, PlotStyle -> PointSize[0.0]];
  lp = ListPlot[{{Sqrt[2], Sqrt[2]}} -> "transition point", 
    PlotStyle -> {PointSize[Large], Red}];
  fp = ListPlot[{{2/Sqrt[10], Sqrt[2]/5} -> "fixed point"}, 
    PlotStyle -> {PointSize[Large], Black}];
  GraphicsGrid[{{Show[{flowmp, lp, Alabel, Blabel}], 
     Show[{flowpp, lp, fp, Alabel, Dlabel}]}, {Show[{flowmm, lp, fp, 
       Blabel, Clabel}], Show[{flowpm, lp, Clabel, Dlabel}]}}]];

test := Module[{doc = "eigenvalues at fixed points Omega", jac, 
   starsub, v2, v3},
  {v2, v3} = OmegaFlow;
  starsub = {x2 -> 2/Sqrt[10], x3 -> Sqrt[2]/5, eps2 -> 1, 
    eps3 -> 1};
  jac = {{D[v2, x2], D[v3, x2]}, {D[v2, x3], D[v3, x3]}} /. starsub;
  Eigenvalues[jac] // Simplify];

chiOmega[absz1_, absz2_, absz3_] := {absz2/absz1^2, absz3/absz1^3};

sectionOmega[x2_, x3_, e2_, e3_] := Module[{s2, c2, c3, s3},
   s2 = x3/x2;
   c2 = Sqrt[1 - s2^2];
   c3 = x2^2/(2 x3);
   s3 = Sqrt[1 - c3^2];
   {{1, x2*(e2*c2 + I s2), x3*(c3 + I*e3*s3)},
    {1, x2*(e2*c2 - I s2), x3*(c3 - I*e3*s3)}}
				    ];



(* equilibrium equations for c0,d2 *)

(* g0til = 1/b0til *)

(* corrected 4/22/2023 *)

b0tilEquilibrium := b0tilEquilibrium = 
 Module[{tag = "MCA:b0til", needs = "wpData,bpData", bEqn, wbEqns, wbEqns1, 
   b0tilpaper, claim0, b0tilsub, omegaTilpaper, mu0til, w0ssub, w0br2sub, b0brsub, omegaTilsub,
    mu0tilsub}, 
  w0ssub = Only[Solve[w0tils == w0s/(1 + w0s), w0s]] /. {w0tils -> w0til^2};
  w0br2sub = {w0br2 -> ((1 + w0s) /. w0ssub // Simplify)};
  w0brsub = {w0br -> 1/Sqrt[1 - w0til^2]};
  Claim0[(w0br2/.w0br2sub)-(w0br^2/.w0brsub)//Simplify,"w0br"];
  wbEqns = {(-I omega w + wpData), (-I omega b + bpData)}/I /. {w -> w0, 
      wc -> w0, b -> b0, bc -> b0, z -> 1, zc -> 1} // Simplify;
  mu0til = (1 - rho*w0til);
  wbEqns1 = wbEqns /. {Sqrt[1 + w0^2] -> w0br, 
       Sqrt[e + b0^2] -> b0br} /. {w0 -> w0til w0br, b0 -> b0br/b0til, 
      omega -> omegaTil/w0br} // Simplify; 
  omegaTilsub = Only[Solve[wbEqns1[[1]] == 0, omegaTil]];
  omegaTilpaper = (w0til - rho)/(mu0til w0til);
  claim0 = (omegaTil /. omegaTilsub) - omegaTilpaper // Simplify;
  Claim0[claim0, "omegaTil-error"];
  bEqn = wbEqns1[[2]] /. omegaTilsub // Simplify;
  b0tilsub = 
   Only[Solve[bEqn == 0, b0til]] /. w0brsub // Simplify;

  b0tilpaper = (rho + w0til - 3 rho*w0til^2 + w0til^3)/(-2 w0til^2*mu0til);
  claim0 = (b0til /. b0tilsub) - b0tilpaper // Simplify;
  Claim0[claim0, "b0til formula"];
  Flatten[{w0ssub, w0br2sub, omegaTilsub, b0tilsub}]]; 

(* revised 1/2/2023 b0til=1/g1 g0til=1/b0til*)

(* XX Notation changes in paper, use tilde rather than subscripts *)

(* corrected 4/22/2023 *)

c0d1TilEquilibrium := c0d1TilEquilibrium = 
 Module[{tag = "MCA:c0d1Til", w0brsub,out, cph, cph1, cph2, cph3, cph4, cph5, 
    mu0til}, out[{a_, b_}, {a1_, b1_}] := {a*a1, b*b1};
     w0brsub = {w0br -> 1/Sqrt[1 - w0til^2]};
   cph = {(-omega I c + cpData)/I, Hamwbc};
   mu0til = (1 - rho w0til);
   cph1 = 
    out[cph, {Sqrt[1 + w0^2], mu0til/w0br}] /. {w -> w0, wc -> w0, 
       b -> b0, bc -> b0, c -> c0, cc -> c0, z -> 1, zc -> 1, 
       omega -> omegaTil/w0br} // FullSimplify;
   cph2 = cph1 /. {Sqrt[1 + w0^2] -> w0br, Sqrt[e + b0^2] -> b0*b0til};
   cph3 = (cph2 /. {w0 -> w0til w0br});
   cph4 = (cph3 /. w0brsub);
   cph5 = cph4 /. {d1 -> d1Til/b0};
   cph5 /. b0tilEquilibrium] // FullSimplify;

c0d1Tilsub = Only[Solve[c0d1TilEquilibrium == {0, 0}, {c0, d1Til}]] // Simplify;

w0tilcrit = Solve[(1/c0 /. c0d1Tilsub) == 0, w0til];

Echo["R1000"];

(* inconsistent eqs at w0tilcrit *)
test:= Module[{eq1, 
  eq2}, {eq1, 
   eq2} = (c0d1TilEquilibrium /. {w0til -> rho/(2 rho^2 - 1)} // 
    Simplify);
 EchoOff[eq1];
 eq2 /. (Only[Solve[eq1 == 0, c0]]) // Simplify];

modulePlotC0D1:= Module[{rhoN = 1.2},
  Plot[c0 /. c0d1Tilsub /. {rho -> rhoN}, {w0til, -1, 1/rhoN}]];

(* To do the abnormal case lambda=0, set lambda=0 in Hamwbc and cData *)
c0d1TilsubAbnormal := 
 Solve[(c0d1TilEquilibrium /. w0til -> rho/(-1 + 2 rho^2)) == {0, 
							       0}, {c0}] // Simplify;

b0tilc0d1TilAnalysis := 
  Module[{subs, b0tilp, b0tilV, neg1, b0tilnum, limit, det, detsub, 
     rhopole, c0d1Til, c0d1Tilsub}, subs = b0tilEquilibrium;
    b0tilV = b0til /. subs // Simplify;
    b0tilp = D[b0til /. subs, w0til] // Simplify // Factor;
    b0tilnum = 2 w0til^2*(-1 + rho w0til)*b0tilV // Simplify;
    rhopole = Only[Solve[b0tilnum == 0, rho]];
    limit = Limit[b0tilV, w0til -> -Infinity];
    neg1 = Solve[(b0tilV) == -1, w0til];
    c0d1Til = (c0d1TilEquilibrium /. subs // Simplify);
    det = 
     Det[{D[c0d1Til, c0], D[c0d1Til, d1Til]}] // Simplify // Factor;
    detsub = Solve[det == 0, w0til];
    c0d1Tilsub = 
     Only[Solve[{c0d1Til == {0, 0}}, {c0, d1Til}]] // Simplify;
    {limit, neg1, c0d1Til, det, detsub, c0d1Tilsub};
    c0d1Tilsub] // Simplify;

test := Module[{c0V, d1TilV, 
    beta = 1.1}, {c0V, d1TilV} = {c0, d1Til} /. b0tilc0d1TilAnalysis;
   Plot[d1TilV /. 
     rho -> beta, {w0til, -beta/(1 + 2 beta),(*beta/(-1+2beta^2),*)
		   1/beta}]];


(* assumes [b]_eps, eps = 1 *)

equilPoint[w0N_,rhoN_]:=
Module[{w0tilN,sub,
  omegaTilN,b0tilN,d1TilN,omegaN,c0N,b0N,d1N},
  sub = {rho->rhoN,w0til->w0tilN};
  w0tilN = w0N/Sqrt[1+w0N^2];
  {b0tilN,omegaTilN}={b0til,omegaTil}/.b0tilEquilibrium/.sub;
  {c0N,d1TilN}={c0,d1Til}/.c0d1Tilsub/.sub;
  b0N=b0/.Only[Solve[b0tilN == Sqrt[1 + b0^2]/b0,b0]];
  d1N = d1TilN/b0N;
  omegaN = omegaTilN/Sqrt[1+w0N^2];
  {omegaN,w0N,b0N,c0N,d1N,rhoN}
];


(* size of upper-half-plane triangle and determinant Lambda1 *)
plotTriInCircum := Module[{d, X0, P0, w, w2, X2},
   d = detLambda1 /. triangleSub;
   X0 = (Phiz /. {x -> 0, y -> y0});
   P0 = P001[X0];
   X2 = MatrixExp[tswgon*P0/2].X0.MatrixExp[-tswgon*P0/2];
   w2 = Abs[(Cayley[X2] // Simplify)[[1, 2]]];
   w = (Cayley[X0] // Simplify)[[1, 2]];
   ParametricPlot[{{d, w}, {d, w2}}, {y0, 0.7, 1}, PlotStyle -> Red]];

plotMid := 
 Module[{doc = "Saved as mathematica-plot-tri-in-circum.pdf", 
   tag = "MCA:inradius-circum", beta = 1.5, subs, c0d1Tilsub, jsub, 
   d1, eps, det, w0d, mid},
  subs = b0tilEquilibrium;
  c0d1Tilsub = b0tilc0d1TilAnalysis;
  jsub = Join[subs, c0d1Tilsub] /. {w0til -> w0/Sqrt[1 + w0^2]} // 
    Simplify;
  d1 = d1Til/b0;
  eps = 1;
  det = eps d1^2;
  w0d = {det, Abs[w0]} /. {b0 -> 1/Sqrt[b0til^2 - 1]} /. 
     jsub /. {rho -> beta};
  mid = ParametricPlot[
    w0d, {w0, -0.24, 0}, {PlotRange -> {{1.9, 2.25}, {0, 0.35}}, 
     PlotStyle -> Blue}];
  Show[mid, plotTriInCircum]];

(*
Export["~/Desktop/mathematica-plot-tri-in-circum.pdf", plotMid, "PDF"];
*)

(* Fuller system, triangular control, chattering solution, appendix *)
modulePlotFuller:= Module[{z00, z10, z20, z30, z101, z201, z301, f, zeta},
 z00 = -I;
 z10 = z101 + z00 (t - 1);
 z20 = z201 + z101 (t - 1) + z00 (t - 1)^2/2;
 z30 = z301 + z201 (t - 1) + z101 (t - 1)^2/2 + z00 (t - 1)^3/6;
 z101 = (1/(r zeta - 1)) z00 (r - 1);
 z201 = (1/(r^2 zeta - 1)) *(z00 (r - 1)^2/2 + z101 (r - 1));
 z301 = (1/(r^3 zeta - 1))*(z00 (r - 1)^3/6 + z101 (r - 1)^2/2 + 
      z201 (r - 1)) // Simplify;
 EchoOff[{"mixed-signs",{Re[z301*zeta^2], 
     Im[z301*zeta^2]} /. {zeta -> Exp[4 Pi I/3]} /. {r -> {6.2741, 
      6.2742}}}];
 f[zetachoice_] := 
  Simplify[
     Re[Conjugate[1 - zetachoice]*z30] /. {zeta -> Exp[4 Pi I/3]}, 
     r \[Element] Reals] /. {r -> 6.275} // Simplify;
 Plot[{f[Exp[2 Pi *I/3]], f[Exp[4*Pi*I/3]]}, {t, 1, 6.2741}]];
	    
(* Make denominator real to get polynomial condition *)
test:=Module[{z301x, poly, poly6,zeta},
 z301x = -I*(zeta^2 + 2 r + 2 r^2 + r^3 zeta)*(r*zeta^2 - 
     1) (r^2 zeta^2 - 1) (r^3 zeta^2 - 1);
 poly = Simplify[z301x - Conjugate[z301x] /. {zeta -> Exp[4 Pi I/3]}, 
    r \[Element] Reals] // Factor;
 poly6 = Apply[List, poly] // Last;
 NSolve[poly6 == 0, r] // FullForm;
 poly6];

(* Start ODEs, Global Numerical Solutions *)

quadraticSol = 
  Module[{doc = "solution z* of control and its complex conjugate", 
    paper, xi0, xi1,b1, xi0c, Delta4, ztilRoot, ztilRootc, zRoot, 
    Nc}, {paper, {xi0, xi1, xi0c}} = z1quad;
   b1 = xi1/2;
   Delta4 = b1^2 + xi0*xi0c;
   ztilRoot = (b1 + Sqrt[Delta4])/(xi0c);
   ztilRootc = (-b1 + Sqrt[Delta4])/xi0;
   Claim0[paper /. {ztil -> ztilRoot} // Simplify];
   Nc = Sqrt[c*cc];
   zRoot = {ztilRoot*c/Nc, ztilRootc*cc/Nc};
   FullSimplify[{z -> zRoot[[1]], zc -> zRoot[[2]]} /. {w1 -> cc*w/Nc, 
      w1c -> c*wc/Nc}]];
    
b0sol = Module[{doc = 
     "Generic b0 {Reb,bsq} for numerical ODE, given w0,c0,Ang0,d1,rho",
   (*rho=3/2,e0=1,d1i=3/2,*)val, bsqsub, Nb}, 
   val = ({Hamwbc, Angwbc - Ang0} /. {w -> w0, wc -> w0, z -> 1, 
         zc -> 1, c -> c0, cc -> c0} // 
       Simplify) /. {Sqrt[b*bc + e] -> bsq};
   bsqsub = (Only[Solve[val[[2]] == 0, bsq]]);
   val1 = (val[[1]] /. bsqsub // Simplify) /. {(b + bc) -> 2 Reb};
   Join[Only[Solve[val1 == 0, Reb]], bsqsub]];

(* Explore regions of valid initial parameters *)

checkPositivity := 
 Module[{doc = "explore graphically the positivity of pos1 and imb2", 
   zs, zsc, w0i = 2, c0i = 1, rhoN = 11/10, d1i = 3/2, e0 = 1, 
   Ang00i = 3, Nb2, signb = 1, pos1, imb2, reb, bsub, w0max},
  {zs, zsc} = quadraticSol;
  bsub = b0sol /. {rho -> rhoN, d1 -> d1i, e -> e0, 
      Ang0 -> Ang00i} // Simplify;
  w0max = If[rhoN > 1, 1/Sqrt[rhoN^2 - 1], 5];
  (*compute initial value of bbased on conserved quantities*)
  
  Nb2 = (bsq^2 - e0) /. bsub // Simplify;
  pos1 = bsq - Max[e0, 1] /. bsub;
  reb = Reb /. bsub;
  imb2 = Nb2 - reb^2 // Simplify;
  (*For initial conditions to be valid,pos1,imb2 must be positive*)
  Plot3D[{imb2, 0}, {w0, 0, w0max}, {c0, 0, 10}]];

(* Solve ODEs numerically *)

ComputeB0[{
  w0i_, c0i_, rhoN_, d1i_, e0_, Ang0i_, signb_}] := 
  Module[{doc="compute b0, when not given",bsub, w0max, wcsub, Nb2, pos1, reb, imb2, b0},
   bsub = 
    b0sol /. {rho -> rhoN, d1 -> d1i, e -> e0, Ang0 -> Ang0i} // 
     Simplify;
   wcsub = {w0 -> w0i, c0 -> c0i};
   (*compute initial value of b0,based on conserved quantities*)
   Nb2 = (bsq^2 - e0) /. bsub // Simplify;
   pos1 = bsq - Max[e0, 1] /. bsub;
   Claim[(pos1 /. wcsub) >= 0, "pos1-CB"];
   reb = Reb /. bsub;
   imb2 = Nb2 - reb^2 // Simplify;
   Claim[(imb2 /. wcsub) >= 0, "imb2-CB"];
   b0 = reb + I*signb*(Sqrt[imb2]) /. wcsub;
   b0
   ];

(* with computed value of b0 *)

solveODE[{w0i_, c0i_, rhoN_, d1i_, e0_, Ang0i_, signb_}, rg_] := 
  solveODEB[{w0i, ComputeB0[{w0i, c0i, rhoN, d1i, e0, Ang0i, signb}], 
    c0i, rhoN, d1i, e0, rg}];

(* with provided value of b0 *)

solveODEB[{w0i_, b0i_, c0i_, rhoN_, d1i_, e0_,rg_}] :=

    Module[{doc = 
     "solve hyperboloid coordinate (w,b,c) ODE with circular control \
ang given parameters", wcsub, w0max, sub1, sub2, eqns, init, 
    sol, ang, ham, zt},
   w0max = If[rhoN > 1, 1/Sqrt[rhoN^2 - 1], 5];
   sub1 = {w*wc -> Abs[w]^2, b*bc -> Abs[b]^2, c*cc -> Abs[c]^2};
   sub2 = {rho -> rhoN, d1 -> d1i, e -> e0, w -> w[t], b -> b[t], 
     c -> c[t], wc -> Conjugate[w[t]], bc -> Conjugate[b[t]], 
     cc -> Conjugate[c[t]]};
   (*main ode*)
   eqns = {wx'[t] == wpData, bx'[t] == bpData, cx'[t] == cpData} /. 
        quadraticSol /. sub1 /. sub2 /. {wx -> w, bx -> b, cx -> c};
   init = {w[0] == w0i, b[0] == b0i, c[0] == c0i};
   sol = NDSolve[Join[eqns, init], {w, b, c}, {t, -rg, rg}];
   ang = Angwbc /. quadraticSol /. sub1 /. sub2;
   ham = Hamwbc /. quadraticSol /. sub1 /. sub2;
   zt = z /. quadraticSol[[1]] /. sub1 /. sub2;
   {sol, ang, ham, zt, rg}
   ];




test:=Module[{tag="MCA:chaos",
  doc = "plot nearby initial values to show numerical chaos", 
  sol, ang, ham, zt, rg, sol2}, {sol, ang, ham, zt, rg} = 
  solveODE[{1.5, 0.5, 11/10, 3/2, 1, 3, 1}, 30];
 {sol2, ang, ham, zt, rg} = 
  solveODE[{1.495, 0.5, 11/10, 3/2, 1, 3, 1}, 30];
 Plot[{Evaluate[Abs[w[t]]] /. sol, 
   Evaluate[Abs[w[t]]] /. sol2}, {t, -rg, rg}]];

(* Example, w0 = -0.2, rho=1.1 *)

test:=Module[{tag="MCA:equil-error",doc = "equilPoint, numerical error", 
    doc2="graphic exported as equilibrium-numerical-error.pdf",
    omegaN,w0N, b0N, c0N, d1N, rhoN, AngN, eps, sgnb,
   sol, ang, ham, zt, rg}, 
 {omegaN,w0N, b0N, c0N, d1N, rhoN} = equilPoint[-0.2,1.1];
 eps = 1; sgnb = 1; rg = 2.5;
 AngN = Angwbc /. {d1 -> d1N, b -> b0N, bc -> b0N, e -> eps, c -> c0N,
     cc -> c0N, w -> w0N, wc -> w0N};
 {sol, ang, ham, zt, rg} = 
  solveODEB[{w0N, b0N, c0N, rhoN, d1N, eps, rg}];
 Plot[Evaluate[  
  Abs[w[t]-w0N*Exp[I*omegaN*t]]
  + Abs[b[t]-b0N*Exp[I*omegaN*t]]
  + Abs[c[t]-c0N*Exp[I*omegaN*t]] /. sol], {t, -rg, rg}]];



test:=Module[{doc = "near singular locus of Fuller", ztowbc, wcsub3, args, 
  e0, rg = 20, sol, ang, ham, zt, t = 1/50},
 ztowbc = 
  Solve[{z3 == c/(6 rho), z2 == -I b/(2 rho), z1 == w/rho}, {w, 
      b, c}][[1]] /. {z1 -> (2 - I)*(3 - I)*t/10, 
    z2 -> (3 - I)*t^2/10, z3 -> t^3/10};
 wcsub3 = {w0 -> w, b0 -> b, c0 -> c, rho -> 11/10, d1 -> 3/2, 
     e0 -> 1, Ang0i -> 3, signb -> 1} /. ztowbc // N;
 args = {w0, b0, c0, rho, d1, e0,rg} //. wcsub3;
 {sol, ang, ham, zt, rg} = solveODEB[args];
 Plot[{Evaluate[Abs[w[t]]] /. sol}, {t, -rg, rg}]];

(* Other possible plots


prec = 10^5;
Plot[Round[Evaluate[{ang, ham}]*prec]/prec /. sol, {t, -rg, rg}];
Plot[Evaluate[{Abs[w[t]], Im[c[t]/w[t]]}] /. sol, {t, -rg, rg}];
(*main plot*)
ParametricPlot3D[
  Evaluate[{Re[c[t]/w[t]], Im[c[t]/w[t]], Abs[w[t]]}] /. sol, {t, -rg,
    rg}];

(*plot optimal control*)zt = z /. quadraticSol[[1]] /. sub1 /. sub2;
Plot[Evaluate[Abs[zt]] /. sol, {t, -rg, rg}];
ParametricPlot3D[Evaluate[{Re[zt], Im[zt], t}] /. sol, {t, -rg, rg}];
(*note how solutions diverge in a chaotic fashion*)Plot[{Evaluate[
    Abs[w[t]]] /. sol, Evaluate[Abs[w[t]]] /. sol2}, {t, -rg, rg}]


*)



       
(* Compute Jacobian relationship between Fuller and Reinhardt z1,z2,z3.
   Definition of Reinhardt z1,z2,z3 as derivatives.  *)

(* Some use of {z10out, z20out, z30out} from other file. *)

(*
DEBUG wbcout is deprecated. Replace with {z10out,z20out,z30out}.
 *)

(* repeated from other file *)

palindrome = 1 - 5 r - 7 r^2 - 5 r^3 - 7 r^4 - 5 r^5 + r^6;
rpal = r /. 
	  NSolve[palindrome == 0, r, Reals, WorkingPrecision -> 50][[2]];

{z10out, z20out, z30out} = Module[{sqrt3, r = rpal,z1,z2,z3}, sqrt3 = Sqrt[3];
   z1 = -1 + I (r - 1)/(sqrt3 (1 + r));
   z2 = -(r^3 - 1)/(sqrt3 (r^3 + 1)) + 
     I (1 - 3 r - 2 r^2 - 3 r^3 + r^4)/(3 ( 1 + r + r^3 + r^4));
   z3 = -2 (1 + r - 4 r^3 - 7 r^4 - 9 r^5 - 7 r^6 - 4 r^7 + r^9 + 
        r^10)/(9*(1 + r)^2 (1 - r + r^2) (1 + r^3 + r^6));
   {z1, z2, z3}];
Echo[{"test z10out",rescale[{z10out, z20out, z30out}, 0.9007]}];



wbcout =Module[{w,b,c,rho=2,z},
       z = wbc2z[{w,b,c},rho];
       {w,b,c}/.Only[Solve[EqTable[z,{z10out,z20out,z30out}],{w,b,c}]]];
 (* Module[{w, b, c, rho = 2},
   {w, b, c} /. 
    Solve[{z30out == c/(6 rho), z20out == -I b/(2 rho), 
       z10out == w/rho}, {w, b, c}][[1]]
	 ]; *)


test:=Module[{singsub, ser, ccpData, bcpData, wcpData, DD, z3R, z2R, z1R, 
  z0R, z3cR, z2cR, z1cR, wbcsub, wbccsub, Jac22}, 
 singsub = {e -> 1, d1 -> 3/2, lambdacost -> -1};
 ser[F_, n_] := 
  Series[(F) /. singsub /. {w -> t w, wc -> t wc, b -> t^2 b, 
     bc -> t^2 bc, c -> t^3 c, cc -> t^3 cc}, {t, 0, n}];
 ccpData = Module[{c1, c2}, c1 = cpData;
   c2 = -c1 /. {c -> cc, cc -> c, b -> bc, bc -> b, w -> wc, wc -> w, 
      z -> zc, zc -> z};
   c2 // Simplify];
 bcpData = Module[{b1, b2}, b1 = bpData;
   b2 = -b1 /. {b -> bc, bc -> b, w -> wc, wc -> w} // Simplify];
 wcpData = Module[{w1, w2}, w1 = wpData;
   w2 = -w1 /. {w -> wc, wc -> w, zc -> z, z -> zc} // Simplify];
 DD[F_] := 
  Module[{F1, DF}, 
   F1 = (F /. {c -> c[t], cc -> cc[t], b -> b[t], bc -> bc[t], 
       w -> w[t], wc -> wc[t]});
   DF = D[F1, t] /. {c'[t] -> cpData, cc'[t] -> ccpData, 
      b'[t] -> bpData, bc'[t] -> bcpData, w'[t] -> wpData, 
      wc'[t] -> wcpData, c[t] -> c, cc[t] -> cc, b[t] -> b, 
      bc[t] -> bc, w[t] -> w, wc[t] -> wc}];
 z3R = c/(6 rho);
 z2R = DD[z3R];
 z1R = DD[z2R];
 z0R = DD[z1R];
 z3cR = cc/(6 rho);
 z2cR = DD[z3cR];
 z1cR = DD[z2cR];
 ser[z3R, 3];
 ser[z2R, 2];
 ser[z1R, 1];
 ser[z0R, 2];
 wbcsub = 
  Solve[{z3 == Normal[ser[z3R, 3]], z2 == Normal[ser[z2R, 2]], 
      z1 == Normal[ser[z1R, 1]]}, {w, b, c}][[1]] /. t -> 1; 
 wbccsub = {wc -> rho z1c, bc -> -2 I*rho z2c, cc -> 6 rho z3c};
 Jac22[{f1_, f2_}, {x_, y_}] := 
  Det[{{D[f1, x], D[f1, y]}, {D[f2, x], D[f2, y]}}];
 ser[Jac22[{z1R, z1cR}, {w, wc}], 2];
 ser[Hamwbc, 3] /. wbcsub /. wbccsub // Simplify];	   



(* RESTART REINHARDT *)
			    
(* New Section Outward Reinhardt spirals *)

RCayley[t_, x_, y_] := Module[{a, b, c},
   {a, b, c} = {a, b, c} /. 
     Only[Solve[{t == (b - c)/2, x == (b + c)/2, y == a}, {a, b, c}]];
   {{a, b}, {c, -a}}
   ];

Zindexed[i_] := Switch[Mod[i, 3, 1], 1, Z100, 2, Z010, _, Z001];
Zindexed[0] - Zindexed[3];
{Zindexed[1], Zindexed[2], Zindexed[3]};

buildswitches[X0_, L0_, LambdaR0_, i_] := 
  Module[{doc = "", lambdacost = -1, X, L, LambdaR, switchA, 
    switchB,mode="pre"}, {X, L, LambdaR} = 
    constantControl[Zindexed[i], X0, L0, LambdaR0, mode];
   switchA = 
   normalizedSwitch[Zindexed[i], Zindexed[i + 1], X, LambdaR];
   switchB = 
    normalizedSwitch[Zindexed[i], Zindexed[i + 2], X, LambdaR];
   {switchA, 
    switchB, {Tr[X.Zindexed[1]], Tr[X.Zindexed[2]], 
	      Tr[X.Zindexed[3]]}}];

test := Module[{rr, A},
    rr := RandomReal[{-0.02, 0.02}];
    A := {{rr, rr}, {rr, rr}};
    buildswitches[J + A, J + A, J + A, 1]] // Chop;


(* This wb+Lie hybrid approach is obsolete.
   Now, Lie algebra coordinates are introduced directly.
 *)

hyperboloid2Lie[r_, zout_] := 
  Module[{z1, z2, z3, w, b, c, d1 = 3/2, eps = 1, rho = 2, X, Lambda1,
     LambdaR, wbr, bbr, 
    Rcw}, {z1, z2, z3} = {zout[[1]]*r, zout[[2]]*r^2, zout[[3]]*r^3};
   {w, b, c} = {w, b, c} /. 
     Solve[{z3 == c/(6 rho), z2 == -I b/(2 rho), z1 == w/rho}, {w, b, 
        c}][[1]];
   wbr = sq[w, Conjugate[w]];
   bbr = sq[b, Conjugate[b]];
   Rcw = RRc[c, Conjugate[c], w, Conjugate[w]];
   X = RCayley[-wbr, Re[w], Im[w]];
   Lambda1 = d1*RCayley[bbr, Re[b], Im[b]];
   LambdaR = RCayley[-Rcw/wbr, Re[c], Im[c]];
   {X, Lambda1, LambdaR}//Chop];

(* Some use of {z10out, z20out, z30out} from other file. *)

test := Module[{X, L1, LR},
   EchoOff[hyperboloid2Lie[r, {x1 + I y1, x2 + I y2, x3}]];
   {X, L1, LR} = hyperboloid2Lie[0.01, {z10out, z20out, z30out}];
   {Det[X], Det[L1], Tr[X.LR]} // Simplify//Chop];

(* Elsewhere there is a ReinhardtPoincareLie implemented.
   This version uses all switches and tests all boundaries of the star domain.
   The other version is faster but more specialized.
   Both use WhenEvent *)

ReinhardtPoincareLieControlled[True] := True;

ReinhardtPoincareLieControlled[{{X0_, L10_, LR0_}, Zindex_, toffset_}] := 
  Module[{chiA, chiB, D1, D2, D3, tsw, teps = 1.0/10^5, tfinal = 1.2, 
    event, X, L1, LR, lambdacost = -1, index},
    If[Or[toffset >= tfinal,Tr[X0.Zindexed[i]]>=0],
    Return[{{{X0, L10, LR0}, Zindex, toffset}, "E"}]];
   {chiA, chiB, {D1, D2, D3}} = 
    buildswitches[X0, L10, LR0, Zindex] // Chop;
   event = "E";
   tsw = tfinal - toffset;
   (* fake ODE for sake of WhenEvent *)
   
   NDSolve[{x'[t1] == 0, x[teps] == 0,
     WhenEvent[
      t1 - 0.99 > 0, {event = "X", tsw = t1, Echo["hi"], 
       "StopIntegration"}],
     WhenEvent[(D1 /. t -> t1) > 0, {tsw = t1, event = "D", 
       "StopIntegration"}],
     WhenEvent[(D2 /. t -> t1) > 0, {tsw = t1, event = "D",
				     "StopIntegration"}],
     WhenEvent[(D3 /. t -> t1) > 0, {tsw = t1, event = "D",
				     "StopIntegration"}],
     WhenEvent[(chiA /. t -> t1) < 0, {tsw = t1, event = "A",
				       "StopIntegration"}, "DetectionMethod" -> "Interpolation"],
     WhenEvent[(chiB /. t -> t1) < 0, {tsw = t1, event = "B", 
				       "StopIntegration"}, "DetectionMethod" -> "Interpolation"]}, x, {t1, teps, tfinal}];
   EchoOff[{event, tsw}];
   {X, L1, LR} = 
    constantControlSolution[Zindexed[Zindex], X0, L10, LR0, 
      lambdacost] /. {t -> tsw};
   index = Switch[event,
     "A", Zindex + 1,
     "B", Zindex - 1,
     _, Zindex];
   Sow[{X0, Zindex, tsw}];
   EchoOff[{X0, Zindex, tsw}];
   Which[
    Or[event == "E", event == "D"], True,
    True, {{X, L1, LR}, index, toffset + tsw}]
   ];

plotOne[{X0_, Zindex_, tsw_}] := Module[{Zu, P0, expP0, expmP0, X},
   Zu = Zindexed[Zindex];
   P0 = Zu/Tr[Zu.X0];
   expmP0 = MatrixExp[-t P0]; expP0 = expmP0 /. {t -> -t};
   X = expP0.X0.expmP0;
   ParametricPlot[IPhi[X], {t, 0, (tsw)}]
   ];

plotStarDomain := {ParametricPlot[{-1/Sqrt[3], t}, {t, 0, 3}, 
    PlotStyle -> Red, PlotRange -> {{-0.9, 0.9}, {0, 3}}],
   ParametricPlot[{1/Sqrt[3], t}, {t, 0, 3}, PlotStyle -> Red],
   ParametricPlot[1/Sqrt[3] {Cos[t], Sin[t]}, {t, 0, Pi}, 
		  PlotStyle -> Red]};

dataR[r_]:= Module[{X0, L10, LR0, index, reap, value, init},
   {X0, L10, LR0} = hyperboloid2Lie[r, {z10out, z20out, z30out}]//ComplexExpand//Chop;
   index = 2;
   {value, reap} =
    Reap[Nest[ReinhardtPoincareLieControlled, {{X0, L10, LR0}, index, 0}, 8]];
   Claim[value, "trajectory not finished"];
   reap[[1]]
	    ];

plotR[r_] := Map[plotOne,dataR[r]];

(*
Module[{X0, L10, LR0, index, reap, value, init},
   {X0, L10, LR0} = hyperboloid2Lie[r, {z10out, z20out, z30out}]//ComplexExpand//Chop;
   index = 2;
   {value, reap} =
    Reap[Nest[ReinhardtPoincareLieControlled, {{X0, L10, LR0}, index, 0}, 8]];
   Claim[value, "module not finished"];
   (* If[Not[TrueQ[value]],Echo[reap]]; *)
   Map[plotOne, reap[[1]]]
   ];
 *)

test:=
Show[Join[plotStarDomain,plotR[1/1000],plotR[2/1000],plotR[0.5/\
1000]]];

outwardTriangularSpirals:=Module[{label="MCA:outward-spirals"},
	Show[Join[plotStarDomain, plotR[4/1000], plotR[2/1000], plotR[1/1000],
   plotR[2/1000], plotR[0.5/1000], plotR[0.25/1000], plotR[1/8000], 
		  plotR[1/16000], plotR[1/32000]]]];

(*
Module[{X0, L10, LR0, index, reap, value, init},
 {X0, L10, LR0} = hyperboloid2Lie[0.5/1000, {z10out, z20out, z30out}];
 index = 2;
 z = ReinhardtPoincareLieControlled[{{X0, L10, LR0}, index, 0}];
 z = ReinhardtPoincareLieControlled[z];
 z = ReinhardtPoincareLieControlled[z];
 z = ReinhardtPoincareLieControlled[z]
 ]

 *)

Rot[X_, k_] := Module[{k1 = Mod[k, 3]},
   MatrixPower[R, k1].X.Inverse[MatrixPower[R, k1]]];
Rot[{{0, 1}, {0, 0}}, 2];


rotatedataR[r_] := Module[{data, d2}, data = dataR[r];
				      d2 = Map[IPhi[Rot[#[[1]], 1 + (#[[2]])]] &, data]];


(*
data = Sort[
	Flatten[Table[rotatedataR[(10 + 1*i)/10000], {i, 1, 45}], 1]];
 *)


test:=Module[{label="MCA:switching-wall",data,ifun},
data = Sort[
	Flatten[Table[rotatedataR[(10 + 1*i)/10000], {i, 1, 45}], 1]];
ifun = Interpolation[data]; Show[plotStarDomain, 
 Plot[{ifun[x], 1 + 2.388 x}, {x, 0, 1/Sqrt[3]}, 
      Epilog -> Point[data]], Epilog -> Point[data]]];

slopeSpiralWall := 
 Module[{doc = "angle of spiral wall coming out of I=singular locus", 
   x, y, rcurve}, 
  rcurve = Simplify[
    IPhi[hyperboloid2Lie[r, {z10out, z20out, z30out}][[1]]], 
    r \[Element] Reals];
  {x, y} = D[rcurve, r] /. r -> 0;
  y/x];

Echo["R1500"];

test :=
Module[{p1, x0, y0, p2},
 {x0, y0} = {0.1, 0.2};
 p1 = linFrac[R, {0, 1} + {x0, y0}];
 p2 = t {x0, y0} /. 
   Only[Solve[p1 s + (1 - s) {0, 1} == t {x0, y0}, {s, t}]];
 {p1, p2}];

test:=Module[{tag = "MCA:generic-dynamics", doc="Lemma in Mahler chapter about how generic conditions give outward spirals",p1, point, h, r},
 point = 0.5 {Cos[2 Pi/3 *95/100], Sin[2 Pi/3 * 95/100]};
 {h, r} = {h, r} /. 
   NSolve[{(-1/2 - h)^2 + 3/4 == 
       r, ((x - h)^2 + y^2 /. {x -> point[[1]], y -> point[[2]]}) == 
       r}, {h, r}][[1]];
 EchoOff[{h, r}];
 p1 = {ParametricPlot[{Cos[t], Sin[t]}, {t, 0, 2 Pi}],
   ParametricPlot[{-1, 0} + {Cos[t], Sin[t]}, {t, -Pi/3, 0}],
   ParametricPlot[{-1, 0} + {Cos[t], Sin[t]}, {t, 0, Pi/3}, 
    PlotStyle -> {Black, Thick}],
   ParametricPlot[{1/2, Sqrt[3]/2} + {Cos[t], Sin[t]}, {t, Pi, 
     4 Pi/3}],
   ParametricPlot[{1/2, -Sqrt[3]/2} + {Cos[t], Sin[t]}, {t, 2 Pi/3, 
     Pi}],
   ParametricPlot[t {Cos[2 Pi/3], Sin[2 Pi/3]}, {t, 0, 1}, 
    PlotStyle -> {Black, Thick}],
   ParametricPlot[t {Cos[4 Pi/3], Sin[4 Pi/3]}, {t, 0, 1}],
   ParametricPlot[{h, 0} + Sqrt[r]*{Cos[t], Sin[t]}, {t, 0, 2 Pi}, 
    PlotStyle -> {Dashed, Orange}],
   ParametricPlot[Sqrt[point.point] {Cos[t], Sin[t]}, {t, 0, 2 Pi}, 
    PlotStyle -> {Dashed, Green}],
   Graphics[{Red, PointSize[Large], Point[{point}]}],
   Graphics[{Orange, PointSize[Large], 
     Point[{h, 0} + Sqrt[r]*{Cos[-0.1], Sin[-0.1]}]
     }]};
 Show[p1]
];

Hamiltonian[Z_, X_, L1_, LR_, lambdacost_] := 
  Tr[(L1 - (3/2) lambdacost J).X] - Tr[LR.Z]/Tr[X.Z];

LRfromXL1[X_, L1_] := 
  Module[{doc = 
      "compute LambdaR, using Ham=0,switch=0, e2-e3 switching point", 
     lambdacost = -1, lR11, lR12, lR21, LR, eq1, sw, ham},
    EchoOff[{X, L1}];
    LR = {{lR11, lR12}, {lR21, -lR11}};
    eq1 = Tr[X.LR];
    sw = switch[Z010, Z001, X, LR];
    ham = Hamiltonian[Z001, X, L1, LR, lambdacost];
    EchoOff[{eq1, sw, ham} // Simplify];
    LR /. 
	Only[Solve[{eq1 == 0, sw == 0, ham == 0}, {lR11, lR12, lR21}]]];

test := Module[{rr, r1}, rr := RandomReal[{-0.01, 0.01}];
   r1 = rr;
   LRfromXL1[J, -(3/2) J + {{rr, r1}, {rr, -r1}}]];

WfromX[X_] := (X[[1, 2]] + X[[2, 1]])/2 + I X[[1, 1]];

XfromW[w_] := Module[{brw}, brw = Sqrt[1 + Abs[w]^2];
			    RCayley[-brw, Re[w], Im[w]]];

BfromL1[L1_] := Module[{doc = "assumes d1=3/2", d1 = 3/2},
		       WfromX[L1]/d1];

L1fromB[b_] := Module[{d1 = 3/2, brb},
   brb = Sqrt[1 + Abs[b]^2];
   d1  RCayley[brb, Re[b], Im[b]]];

test:=Module[{w = 1 + I, b = 1 + I}, 
  Claim0[WfromX[XfromW[w]] - (w), "WfromX"];
  Claim0[BfromL1[L1fromB[b]] - b, "BfromL1"]
  ];


(* This wb+Lie hybrid approach is obsolete.
   Now, Lie algebra coordinates are introduced directly.
 *)


hyperboloid2Lie2[{w_, b_}] := Module[{X, L1, LR},
   X = XfromW[w];
   L1 = L1fromB[b];
   LR = LRfromXL1[X, L1];
   {X, L1, LR}];

test:= Module[{r, zout, o, w, b, c},
   r = 1/1000;
   zout = {z10out, z20out, z30out};
   o = hyperboloid2Lie[r, zout] // Chop;
   {w, b, c} = wbcout;
   Echo[{"hyperboloid2Lie",o - hyperboloid2Lie2[{w*r, b*r^2}]}]
   ];

(* normwb[{w_, b_}] := Sqrt[Im[w]^2 + Abs[b]^2]; -> complexNorm *)

Fwb[True]:= True;

Fwb[{w0_, b0_}] := 
  Module[{doc = "one step of Reinhardt, assuming control=2.", w, b, 
    X0, L10, LR0, index, X2, L2, LR2, newindex, tsw,gL},
   {X0, L10, LR0} = hyperboloid2Lie2[{w0, b0}];
   index = 2;
   gL =     ReinhardtPoincareLieControlled[{{X0, L10, LR0}, index, 0}];
   If[Length[gL]!=3,Return[gL]];
   {{X2, L2, LR2}, newindex, tsw} = gL;
   Claim0[newindex - 1, "bad index"];
   If[Not[TrueQ[newindex == 1]], (gldata = {{X0, L10, LR0}, index, 0};
      Echo[{"bad data", {{X0, L10, LR0}, index, 0}, {{X2, L2, LR2}, 
        newindex, tsw}}])];
   
   Claim[tsw > 0, "bad time"];
   {WfromX[X2]*zeta, BfromL1[L2]*zeta}
   ];

x1scaled[{w0_, b0_}] := rescale[{w0, b0}, 1/Abs[Re[w0]]];


computeFwb[r_] := Module[{w, dummy, b, w2, b2},
  {w, b, dummy} = wbcout;
  {w, b} = x1scaled[{w, b}];
  {w2, b2} = x1scaled[Fwb[{w*r, b*r^2}]];
  {{w, b}, {w2, b2}}
  ];

testContract := 
  Module[{width = 1/200, rmax = 1/10^3, r, w, w0, b0, dummy, w1, b1, 
    w2, b2, rr, s, wbout, fwbout, max, quot},
   s := RandomReal[{1/20, 1}];
   r = s*rmax;
   {wbout, fwbout} = computeFwb[r];
   rr := RandomReal[{-1, 1}]*width;
   {w0, b0, dummy} = wbcout;
   {w0, b0} = x1scaled[{w0, b0}];
   EchoOff[{w0, b0}];
   {w1, b1} = {w0, b0} + {I*rr, rr + I*rr};
   {w2, b2} = x1scaled[Fwb[{w1*r, b1*r^2}]];
   (* check w2,b2 in original rectangle *)
   
   max = Max[Abs[Im[w2] - Im[w0]], Abs[Re[b2] - Re[b0]], 
      Abs[Im[b2] - Im[b0]]]/width;
   quot = complexNorm[{w2, b2} - fwbout]/
     complexNorm[{w1, b1} - wbout];
   {width, rmax, r, w1, b1, "max", max} 
   ];

test := Module[{tab, n = 10}, 
  tab = Table[(If[Mod[i, 100] == 0, Echo[i/100]]; testContract), {i, 
     n}];
  {n, Select[tab, Last[#] == Max[Map[Last, tab]] &]}];

(* empirically, with rmax=1/10^3, width=1/100 => max < 0.33 *)
(* With old norm \
Im[w]^2+Abs[b]: {r,w1,b1,quot}: \
{{0.0008760613029732274`,-1.`+0.4238435738332968` \
\[ImaginaryI],-0.13165100200370763`-0.5726680285341296` \
\[ImaginaryI],2.545364706075034`}}.
New norm Sqrt[Im[w]^2+Abs[b]^2]: {width,r,w1,b1,quot}: \
{{1/100,0.0006736961764637868`,-1.`+0.42008335772246724` \
\[ImaginaryI],-0.1307617956911888`-0.5718293970918661` \
\[ImaginaryI],0.6409745218420152`}} 

quot>1, with width=rmax=1/1000.


*****
seems give quot<1, with width=1/200, rmax=1/1000.
1000 trials
quot:
{{1/200, 1/1000, 
  0.000676118, -1. + 0.416608 I, -0.131148 - 0.571549 I, 0.52533}}
10000 trials

{10000, {{1/200, 1/1000, 
   0.000680725, -1. + 0.417388 I, -0.13241 - 0.570414 I, "quot", 
   0.483004}}}

1000 trials
max:
{{1/200, 1/1000, 
  0.000665773, -1. + 0.423525 I, -0.132004 - 0.568327 I, 0.615002}}

{10000, {{1/200, 1/1000, 
   0.000647131, -1. + 0.42349 I, -0.129799 - 0.567946 I, "max", 
   0.610701}}}
*****

*)

test:= Module[{d, r, w0, b0, quot, dummy, w1, b1},
 {{r, w1, b1, 
    quot}} = {{0.0008760613029732274, -1. + 
     0.4238435738332968*I, -0.13165100200370763 - 
     0.5726680285341296*I, 2.545364706075034}} (* %1689 *);
 EchoOff[quot];
 {w0, b0, dummy} = wbcout;
 {w0, b0} = x1scaled[{w0, b0}];
 d = complexNorm[{w1, b1} - {w0, b0}];
 {w1, b1} = {w0, b0} + { I/100, 0};
 Echo[({w1, b1} - {w0, b0}) 100];
 {complexNorm[{w1, b1} - {w0, b0}], 
  complexNorm[x1scaled[Fwb[{w1*r, b1*r^2}]] - 
    x1scaled[Fwb[{w0*r, b0*r^2}]]]};
 Plot[complexNorm[
    x1scaled[Fwb[{w1*r, b1*r^2}]] - x1scaled[Fwb[{w0*r, b0*r^2}]]]/
   d, {r, 1/10^4, 1/100}]
       ];

				     
				     (* rough draft *)

test:=Module[{x, y, w},
 EchoOff[ComplexExpand[IPhi[XfromW[Rew + I Imw]]]];
 w = wbcout[[1]];
 w = Rew + I Imw;
 x = Re[w];
 y = Im[w];
 ComplexExpand[x + Sqrt[1 + x^2 + y^2]]];

Inregion[w_] := Module[{x, y, o},
   {x, y} = {Re[w], Im[w]};
   o = And[y > 0, y^2 + 2 x < 0];
   If[Not[o], Echo[{"out of region", w}]];
   o];
InregionFirst[w_List] := Inregion[First[w]];

mkRandomSample[width_, rmin_, rmax_] := 
  Module[{r, rr, w0, b0, dummy, w1, b1},
   r = RandomReal[{rmin, rmax}];
   rr := RandomReal[{-1, 1}]*width;
   {w0, b0, dummy} = wbcout;
   {w0, b0} = x1scaled[{w0, b0}];
   EchoOff[{w0, b0}];
   {w1, b1} = {w0, b0} + {I*rr, rr + I*rr};
   {w1*r, b1*r^2}
  ];

mkCornerSample[{w0_, b0_}, width_, rmin_, rmax_, n_] := 
  Module[{doc = "Input w0 should be x1 normalized: Abs[Re[w0]]=1", 
    dummy, e, rtab, tab},
   e = {-1, 1};
   rtab = Table[rmin + (i/(n - 1))*(rmax - rmin), {i, 0, n - 1}];
   tab = Flatten[
     Table[{w0, b0} + {I*e[[i]], e[[j]] + I*e[[k]]}*width, {i, 1, 
       2}, {j, 1, 2}, {k, 1, 2}], 2];
   tab = Join[{{w0, b0}}, tab];
   tab = Flatten[
     Table[{rtab[[j]], tab[[i, 1]]*rtab[[j]], 
       tab[[i, 2]]*rtab[[j]]^2}, {i, 1, Length[tab]}, {j, 1, 
       Length[rtab]}], 1];
   tab
  ];

test := Module[{w0, b0, dummy},
   {w0, b0, dummy} = wbcout;
   {w0, b0} = x1scaled[{w0, b0}];
   mkCornerSample[{w0, b0}, 1/200, 1/10^4, 1/10^3, 3] // Length];

testOutward := 
  Module[{width = 1/200, rmax = 1/10^3, w1, b1, fwb, scale, iter = 20},
   {w1, b1} = mkRandomSample[width, rmax/10, rmax];
   fwb = Nest[(InregionFirst[#]; Fwb[#]) &, {w1, b1}, iter];
   If[TrueQ[fwb], Return["done"]];
   scale = Power[(Abs[Re[First[fwb]]]/r), 1/iter] // N;
   Echo[scale];
   Echo[Inregion[First[fwb]]];
   fwb];
test := Union[Table[testOutward, {i, 50}]];

(* .. needs to be cleaned up ...  *)

outward1[{w0_, b0_}, width_, rmin_, rmax_] := 
  Module[{tab, r, fwout, fbout, w1, b1, scale, newwidth, f, dummy},
   tab = mkCornerSample[{w0, b0}, width, rmin, rmax, 3];
   tab = Table[
     ({r, w1, b1} = tab[[i]];
      InregionFirst[{w1, b1}];
      f = Fwb[{w1, b1}];
      If[Length[f] != 2, Return[f]];
      {w1, b1} = f;
      scale = Abs[Re[w1]];
      {w1, b1} = x1scaled[{w1, b1}];
      {scale/r, w1, b1}
      ),
     {i, 1, Length[tab]}];
   {dummy, fwout, fbout} = Apply[Plus, tab]/Length[tab];
   scale = Map[First, tab] // Min;
   newwidth = Table[({dummy, w1, b1} = tab[[i]];
       {Abs[Im[w1 - fwout]], Re[b1 - fbout], Im[b1 - fbout]}
       ), {i, 1, Length[tab]}] // Max;
   {{fwout, fbout}, scale, newwidth}
  ];

  test := Module[{w0, b0, dummy, rmin, rmax, scale, width, out},
  {w0, b0, dummy} = wbcout;
  {w0, b0} = x1scaled[{w0, b0}];
  Echo[{w0, b0}];
  {rmin, rmax} = {1/7000, 1/1000};
  (* start loop *)
  Do[
   (out = outward1[{w0, b0}, 1/200, rmin, rmax];
    If[Length[out] != 3, Return[out]];
    {{w0, b0}, scale, width} = out;
    Echo[{{w0, b0}, scale, width}];
    width = Max[width, 1/200];
    {rmin, rmax} = {rmax, scale*rmax}),
   {5}];
  (* end loop *)
  {{rmin, rmax}, IPhi[XfromW[w0]]}
       ];


testSL := Module[{w0, b0, r, r1 = 1, X0, L10, LR0, lambdacost = -1, X, 
   L1, LR, i = 2, switchB, tsub, w, b, o},
  r = 1/10^10;
  Echo[x1scaled[Take[wbcout, 2]]];
  {w0, b0} = N[Rationalize[x1scaled[Take[wbcout, 2]], 1/10^10], 10000];
  EchoOff[{w0, b0}];
  {X0, L10, LR0} = hyperboloid2Lie2[{r w0, r^2 b0}];
  Echo[errorAbs[{Tr[X0.LR0], 
     Hamiltonian[Z010, X0, L10, LR0, lambdacost]}]];
  Echo[Precision[{X0, L10, LR0}]];
  Echo[N[{X0, L10, LR0}]];
  {X, L1, LR} = constantControl[Z010, X0, L10, LR0, "pre"] // Simplify;
  (* to here *)
  Echo[Precision[{X, L1, LR} /. t -> 1/100]];
  switchB = 
   normalizedSwitch[Zindexed[i], Zindexed[i + 2], X, LR] // Simplify //
     Chop;
  Echo[Precision[switchB /. t -> 1/10]];
  EchoOff[switchB];
  tsub = {t -> (t /. 
       FindRoot[switchB/r^3, {t, 37*r/10}, WorkingPrecision -> 5000])};
  Echo[{"mid", N[switchB /. t -> (t/2 /. tsub)]}];
  Echo[{"s0", N[switchB /. t -> 0]/r^3}];
  Echo[Precision[t /. tsub]];
  Echo[N[t /. tsub]];
  Echo[{Hamiltonian[Z010, X, L1, LR, lambdacost], Tr[(X - X0).Z010], 
     Tr[X.LR]} /. tsub];
  w = WfromX[X /. tsub] zeta;
  b = BfromL1[L1 /. tsub] zeta;
  Echo[N[{(t/r /. tsub), -Re[w]/r, x1scaled[{w, b}]}]];
  Plot[{switchB, 0, r^2*(t - (t /. tsub))}, {t, 0, 13 (t /. tsub)/10},
    WorkingPrecision -> 5000] 
  
  ];


testA := Module[{w0, b0, X0, L10, LR0, lambdacost = -1, X, L1, LR, 
   i = 2, switchB, tsub, w, b, o},
  (* r=1/10^10; *)
  Echo[x1scaled[Take[wbcout, 2]]];
  {w0, b0} = Rationalize[x1scaled[Take[wbcout, 2]], 1/10^10];
  Echo[{w0, b0}];
  
  {X0, L10, LR0} = 
   Simplify[hyperboloid2Lie2[{r w0, r^2 b0}], r \[Element] Reals];
  
  (*
  Echo[errorAbs[{Tr[X0.LR0],Hamiltonian[Z010,X0,L10,LR0,
  lambdacost]}]];
  Echo[Precision[{X0,L10,LR0}]];
  Echo[N[{X0,L10,LR0}]];
  *)
  {X, L1, LR} = constantControl[Z010, X0, L10, LR0, "pre"];
  Series[LR, {r, 0, 1}]
  (*
 Echo[Precision[{X,L1,LR}/.t\[Rule]1/100]];
 switchB = \
normalizedSwitch[Zindexed[i],Zindexed[i+2],X,LR]//Simplify//Chop;
 Echo[Precision[switchB/.t\[Rule]1/10]];
 EchoOff[switchB];
 tsub= {t \[Rule] \
(t/.FindRoot[switchB/r^3,{t,37*r/10},WorkingPrecision\[Rule]5000])};
 Echo[{"mid",N[switchB/.t\[Rule](t/2/.tsub)]}];
 Echo[{"s0",N[switchB/.t\[Rule]0]/r^3}];
 Echo[Precision[t/.tsub]];
 Echo[N[t/.tsub]];
 Echo[{Hamiltonian[Z010,X,L1,LR,lambdacost],Tr[(X-X0).Z010],Tr[X.LR]}/.\
tsub];
 w=WfromX[X/.tsub] zeta;
 b = BfromL1[L1/.tsub] zeta;
 Echo[N[{(t/r/.tsub),-Re[w]/r,x1scaled[{w,b}]}]];
 Plot[{switchB,0,r^2*(t-(t/.tsub))},{t,0,13(t/.tsub)/10},\
WorkingPrecision\[Rule]5000] 
 *)
 ];

test:=Module[{X, L1},
 X = XfromW[1 + 0.2 I];
 {Tr[X], Det[X]};
 L1 = L1fromB[0.3 + 0.4 I];
 {Tr[L1], Det[L1]};
 BfromL1[L1];
 L1 = L1fromB[0] // Chop;
 BfromL1[L1];
 L1 == -3/2 J;
 XfromW[0] == J
 ];

test:=Det[RCayley[t, x, y]];

test := Module[{doc = "test ODE solutions, constant control", Z, X0, 
    L10, LR0, lambdacost = -1, X, L, LR, Xbis, Lbis, LRbis, Xter, 
    Lter, LRter, error, P, odeX, o, odeL, odeLR, ham, debug}, Z = Z010;
   X0 = N[J + {{1/10, -2/10}, {3/20, -1/10}}];
   X0 = X0/Sqrt[Det[X0]];
   L10 = N[-3/2 J + {{1/8, 1/7}, {1/6, -1/8}}];
   LR0 = N[{{1/10, 1/11}, {1/12, -1/10}}];
   MatrixExp[t X0] - MatrixExpSL[t, X0];
   EchoOff[{Z, X0, L10, LR0, lambdacost}];
   {X, L, LR} = 
    constantControlSolutionNegDet[Z, X0, L10, LR0, lambdacost] // 
     Simplify;
   EchoOff[{X, L, LR}];
   {Xbis, Lbis, LRbis} = 
    constantControlSolution[Z, X0, L10, LR0, lambdacost] // Simplify;
   {Xter, Lter, LRter} = 
    constantControl[Z, X0, L10, LR0, "pre"] // Simplify;
   EchoOff[{Xter, Lter, LRter}];
   EchoOff[Precision[{Xbis, Lbis, LRbis} /. t -> 1/10]];
   error = 
    Apply[Plus, Map[Abs, Flatten[{X - Xbis, L - Lbis, LR - LRbis}]]];
   o := Plot[error, {t, 0, 3/10}];
   P = Z/Tr[X0.Z];
   odeX = D[X, t] - br[P, X] // Simplify // Chop;
   o := Plot[errorAbs[odeX], {t, 0, 0.3}];
   odeL = D[L, t] - br[L, X] // Simplify // Chop;
   o := Plot[errorAbs[odeL], {t, 0, 0.3}];
   odeLR = 
    D[LR, t] - ((br[P, LR] - Tr[LR.P]*br[P, X]) + 
       br[-L + (3/2) lambdacost J, X]);
   o := Plot[errorAbs[odeLR], {t, 0, 0.3}];
   ham = Hamiltonian[Z, X0, L10, LR0, lambdacost] - 
     Hamiltonian[Z, X, L, LR, lambdacost];
   o := Plot[ham, {t, 0, 0.3}];
   Plot[errorAbs[{odeX, odeL, odeLR, ham, X - Xbis, L - Lbis, 
      LR - LRbis, X - Xter, L - Lter, LR - LRter}], {t, 0.2, 0.3}]];

(*Module[{Z,X0,L10,LR0,lambdacost=-1,X,L,LR,a,b,c,l11,l12,l21,lR11,\
lR12,lR21},Z=Z010;
X0={{a,b},{c,-a}};
L10={{l11,l12},{l21,-l11}};
LR0={{lR11,lR12},{lR21,-lR11}};
{X,L,LR}=constantControl[Z,X0,L10,LR0]]*)

(* Module[{c,Rec,Imc,X,L1,LR,Xt,L1t,LRt,o},
X = Simplify[ComplexExpand[XfromW[r x1+I r y1]],{r\[Element] \
Reals,r>0}];
o=L1 = Simplify[ComplexExpand[L1fromB[r^2 x2+I r^2 y2]],{r\[Element] \
Reals,r>0}];
LR=(Simplify[ComplexExpand[LRfromXL1[X,L1]],{r\[Element] \
Reals,r>0}]);
Rec=(LR[[1,2]]+LR[[2,1]])/2;
Imc=LR[[1,1]];
Series[L1,{r,0,4}];
ComplexExpand[Det[X]];
(*
ComplexExpand[Det[L1]];
o=Series[X-J,{r,0,1}];
Series[L1 + (3/2)J,{r,0,2}];
Series[LR,{r,0,3}];
{Xt,L1t,LRt}=constantControl[Z010,X,L1,LR,"pre"];
*)
o
]
 *)
Echo["R2000"];

constantsolsJunk := 
  Module[{doc = "assumes Det[X]=1", X, L1, LR, Xt, L1t, LRt, switch, 
    switch0, switch2, switch3, switchLRdiff, Dswitch, d, o,rx21sol,rl21sol},
   X = J + r {{x11, x12}, {x12 + r*rx21, -x11}};
   rx21sol = Solve[Det[X] == 1, rx21] // Flatten;
   X = X /. rx21sol;
   L1 = -(3/2) J + r^2 (3/2) {{l11, l12}, {l12 + r^2*rl21, -l11}};
   rl21sol = Solve[Det[L1] == 9/4, rl21] // Flatten;
   L1 = L1 /. rl21sol;
   Echo[{rx21sol, rl21sol}];
   LR = Simplify[LRfromXL1[X, L1]];
   (*
   LR = {{0,0},{0,0}}; 
   LR = r^3 {{lR11,lR12},{lR21,-lR11}};
   *)
   {Xt, L1t, LRt} = 
    constantControlSolutionPreComputeDet[Z010, X, L1, LR, detmsqrt];
   o = switch = normalizedSwitch[Z010, Z100, Xt, LRt] /. {t -> t*r};
   d = -Sqrt[-Det[Z010]]/Tr[X.Z010] // Simplify;
   Echo[d];
   (*
   switch0 = switch/.{x11\[Rule]0,x12\[Rule]0,xr21\[Rule]0,
   l11\[Rule]0,l12\[Rule]0,rl21\[Rule]0,lR11\[Rule]0,lR12\[Rule]0,
   lR21\[Rule]0};
   switchLRdiff = switch - (switch/.{lR11\[Rule]0,lR12\[Rule]0,
   lR21\[Rule]0});
   o=Series[switch,{r,0,5}];
   switch2=switch/.{E^u_ \[Rule] 1 + u + u^2/2 + (u^3/6) + (u^4/
   24) E4[u]};
   switch3 = switch/.{E^u_ \[Rule] E0[u]};
   Series[switch3,{r,0,4}]/.{E0[0]\[Rule]1,E0'[0]\[Rule]1,E0''[
   0]\[Rule]1,E0'''[0]\[Rule]1,E0''''[0]\[Rule]C}//Simplify;
   Series[switch2,{r,0,4}]//Simplify;
   Series[(R.Xt.Inverse[R]-J)/.{t\[Rule]r*t},{r,0,1}]//Simplify;
   Series[LRt/.{t\[Rule]t*r},{r,0,3}];
   Series[switchLRdiff,{r,0,3}];
   *)
   Dswitch = D[switch, t];
   (*
   Dswitch=D[Dswitch,{r,4}]/.{t\[Rule]7.4,r\[Rule]0.0001,
   x11\[Rule] 0.418,x12\[Rule]-1,l11\[Rule]-0.859,l12\[Rule]-0.197}
   *)
  ];

junk := Module[{X, L1, LR, swG, poly, o},
   {X, L1, LR} = constantsolsJunk;
   swG = normalizedSwitch[Z010, Z100, X, LR] /. {t -> t*r};
   (* cubic term is leading term *)
   
   poly = -4/
      9 (2 Sqrt[3] t^3 + 9 t^2 x1 + 3 Sqrt[3] t x2 + 9 x1 x2 - 
       3 Sqrt[3] t^2 y1 + 9 t y2 + 9 y1 y2) r^3;
   Series[swG, {r, 0, 4}]];


(* obsolete  
sl2out1 = Module[{doc = "Convert hyperbolid outward equilibrium to sl2 coordinates, \
normalized st X11=1", X, L1, LR, scale, r},
   {X, L1, LR} = ComplexExpand[hyperboloid2Lie[r, {z10out, z20out, z30out}]];
   scale = EchoOff[Normal[Series[((X - J)/r)[[1, 1]],{r,0,0}]]];
   Claim[0 < scale, "sl2out x12pos"];
   Normal[
    Series[{(X - J)/(scale r), (L1 + (3/2) J)/(scale r)^2, 
      LR/(scale r)^3}, {r, 0, 0}]]
   ];


sl2outc1 = Module[{Xtil,L1til,LRtil},
		  {Xtil,L1til,LRtil}=sl2out1;
		  {Xtil[[2,1]],L1til[[1,1]],L1til[[2,1]]}];
*)

sl2out1 = Module[{doc="fixed point out in Lie",X, L1, LR, scale = 2 y1},
  {X, L1, LR} = 
   ComplexExpand[
    hyperboloid2Lie[r, {x1 + I y1, x2 + I y2, x3 + I y3}]];
  {X, L1, LR} = 
   Normal[Series[{(X - J)/(scale r), (L1 + (3/2) J)/(scale r)^2, 
		  LR/(scale r)^3}, {r, 0, 0}]];
    Claim[X[[1, 1]] == 1, "hyperboloid2Lie0out - Note normalization"];
  {X,L1,LR} /. {x1 -> Re[z10out], 
		y1 -> Im[z10out], x2 -> Re[z20out], y2 -> Im[z20out],
		x3->Re[z30out],y3->Im[z30out]}
	  ];

hyperboloid2Lie0out = 
 Module[{doc = "fixed point out in Lie", X, L1, LR},
  {X, L1, LR} = sl2out1;
  {X[[2, 1]], L1[[1, 1]], L1[[2, 1]]}];

(* Obsolete:

sl2out = Module[{doc = 
     "Convert hyperbolid outward equilibrium to sl2 coordinates, \
normalized st X12==-1", X, L1, LR, w, b, x12, r},
   {w, b} = Take[ wbcout, 2];
   {X, L1, LR} = ComplexExpand[hyperboloid2Lie2[{r w, r^2 b}]];
   x12 = ((X - J)/r)[[1, 2]];
   Claim[0 < Normal[Series[-x12, {r, 0, 0}]], "sl2out x12pos"];
   Normal[
    Series[{(X - J)/(-x12 r), (L1 + (3/2) J)/(-x12 r)^2, 
      LR/(-x12 r)^3}, {r, 0, 0}]]
   ];
sl2outc = {sl2out[[1, 1, 1]], sl2out[[2, 1, 1]], sl2out[[2, 2, 1]]};

Clear[x11, x12, x21, l11, l12, l21, l11, tr, t, d1, lR11, lR12, 
  LR21];
Clear[LambdaRtilSol];

 *)

(* Implementation of ReinhardtPoincare map in Lie algebra coordinates *)

constantSolData := 
 constantSolData =  
  Module[{doc = 
     "takes active control Zu = Z010, switching toward Z100", 
    Lambda10psi, Psi, P0, expmX0P0, expX0P0, expmP0, expP0, Lambda10, 
    X0, igrand, igrandJ, o, lambdacost = -1, psi, igrandpsi, LambdaR0,
     LambdaRA, LambdaRB, X, L1, ZP},
   X0 = J + {{x11, x12}, {x21, -x11}};
   Lambda10 = -(3/2) J + {{l11, l12}, {l21, -l11}};
   LambdaR0 = {{lR11, lR12}, {lR21, -lR11}};
   tr (* Tr[Z010.X0] *);
   P0 = Z010/tr;
   EchoOff[P0];
   expmX0P0 = MatrixExpSymbolic[-t , (X0 + P0), d1]; 
   expX0P0 = (expmX0P0 /. {t -> -t}); 
   expmP0 = MatrixExpSymbolic[-t, P0, d1]; expP0 = expmP0 /. {t -> -t};
   EchoOff[expP0];
   igrand = Simplify[expmX0P0.Lambda10.expX0P0];
   igrandJ = Simplify[expmP0.J.expP0];
   EchoOff[igrand];
   Psi = Integrate[igrand - (3/2) lambdacost*igrandJ, {t, 0, t}] // 
     Simplify;
   igrandpsi = -Tr[P0.(Psi.X0 - X0.Psi)] // Simplify;
   EchoOff[igrandpsi];
   o = psi = Integrate[igrandpsi, {t, 0, t}] // Simplify;
   LambdaRA = -(br[Psi, X0] + psi br[P0, X0]) // Simplify;
   LambdaRB = LambdaR0 - t Tr[P0.LambdaR0]*br[P0, X0];
   X = expP0.X0.expmP0 // Simplify;
   L1 = expP0.expmX0P0.Lambda10.expX0P0.expmP0 // Simplify;
   ZP = expmP0.Z100.expP0 // Simplify;
   {X, L1, ZP, LambdaRA + LambdaRB}
   ];

switchtil[ZP_, X0_, LRtil_] := 
  Tr[ZP.LRtil]*Tr[Z010.X0] - Tr[Z010.LRtil]*Tr[ZP.X0];

(* obsolete: replace with x21star *)
x11starObsolete[r_] := (1 - r)/(Sqrt[3] r);

x21star[r_]:= Sqrt[3] - 1/r;


(* Elsewere ReinhardtPoincareLieControlled does implementation with control input
   The version here should be faster, because it uses constantSolData for ODE solutions.
   It uses switchtil for the switching function, which uses control Z010.
   So we must be in the region with Z010 switching.  
 *)

(* edited Dec 7, 2023 to replace x21=-1 with new normalization x11=1 *)

ReinhardtPoincareLie[{instar_, r_, x210_, l110_, l210_,___}] := 
  Module[{x110=1,X0, L10, LambdaR0, X, L1, ZP, LambdaRtil, d1V, l11V, l12V, 
    l21V, lR11V, lR12V, lR21V, tV, trV, x11V, x12V, x21V, x, dummy, 
    sub, sw, t1sw, R2, Xf, L1f, scale, event, starDenom1, instar2},
	 If[Not[instar], Return[{instar, r, x210, l110, l210}]];
	 If[x210<= N[x21star[r]],Return[{False,r,x210,l110,l210}]];
   {x11V, x21V, l11V, l21V} = {r*x110, r*x210, l110*r^2, l210*r^2};
   X0 = J + {{x11V, x}, {x21V, -x11V}};
   {X0, x12V} = {X0, x} /. Flatten[Solve[Det[X0] == 1, x]];
   EchoOff[(X0 - J)/r];
   trV = Tr[X0.Z010];
   d1V = -Sqrt[-Det[Z010]]/trV;
   EchoOff[Sqrt[-Det[Z010]]];
   L10 = -(3/2) J +  {{l11V, x}, {l21V, -l11V}};
   EchoOff[L10];
   {L10, l12V} = {L10, x} /. Flatten[Solve[Det[L10] == 9/4, x]];
   EchoOff[{(L10 + (3/2) J)/r^2, Det[L10]}];
   LambdaR0 = LRfromXL1[X0, L10];
   {{lR11V, lR12V}, {lR21V, dummy}} = LambdaR0;
   sub = {d1 -> d1V, l11 -> l11V, l12 -> l12V, l21 -> l21V, 
     lR11 -> lR11V, lR12 -> lR12V, lR21 -> lR21V, t -> r*t1, 
     tr -> trV, x11 -> x11V, x12 -> x12V, x21 -> x21V};
   {X, L1, ZP, LambdaRtil} = constantSolData /. sub;
   EchoOff[LambdaRtil];
   sw = switchtil[ZP, X0, LambdaRtil];
   starDenom1 = Tr[X.Z100];
   event = "N";
   t1sw = {t1 -> 10.0};
   NDSolve[{x'[ts] == 0, x[0] == 0, 
     WhenEvent[
      ts - 20 > 0, {event = "X", t1sw = {t1 -> ts}, 
       Echo["Unreachable: Upper time limit ReinhardtPoincareLie"], "StopIntegration"}],
      WhenEvent[(starDenom1 /. t1 -> ts) > 0, {t1sw = {t1 -> ts}, event = "D",
        "StopIntegration"}], 
     WhenEvent[(sw /. t1 -> ts) < 0, {t1sw = {t1 -> ts}, event = "A", 
       "StopIntegration"}, "DetectionMethod" -> "Interpolation"]}, 
    x, {ts, 0, 10}];
   instar2 = (event == "A");
   EchoOff[{instar2, (event == "A"), event, t1sw}];
   EchoOff[{Det[X /. t1sw], Det[L1 /. t1sw]}];
   R2 = R.R;
   {Xf, L1f} = {R2.X.Inverse[R2] - J, R2.L1.Inverse[R2] + (3/2) J} /. 
     t1sw;
   scale = Abs[Xf[[1, 1]]];
   Claim[Xf[[1, 1]] > 0, "xf11 (negative r)"];
   EchoOff[scale];
   EchoOff[scale/r];
   Flatten[{instar2, scale,
	    {Xf[[2, 1]]/scale, Transpose[L1f][[1]]/scale^2},(t1/.t1sw),r}]
   ];

(* edited 12/7/2023, new normalization *)

test := Module[{r, x21, l11, l21},
   {r, x21, l11, l21} = Flatten[{10^-5, hyperboloid2Lie0out}];
   Take[ReinhardtPoincareLie[{True, r, x21, l11, l21}],5] - {True, r, x21, l11, l21}];

nestListUnstableCurve[r_] := 
  Module[{doc = "unstable curve estimate, generally 1/rpal <= r <= 1",
     eps = 10.0^-3, nestDepth = 8, nl}, 
   nl = NestList[ReinhardtPoincareLie, 
     Flatten[{True, r*eps, hyperboloid2Lie0out}], nestDepth];
   Select[nl, First[#] &]];

onetest := nestListUnstableCurve[RandomReal[{1/rpal, 1}]];

unstableCurveData := unstableCurveData = 
   Module[{rval, tab, count = 100}, 
    rval = (1/rpal)*Table[rpal^(i/count), {i, 1, count}];
    tab = Flatten[Map[nestListUnstableCurve, rval], 1];
    Map[Drop[#,1]&, tab]
    ];

plotUnstableCurve := Module[{tag="MCA:unstable-curve",
			     doc="unstable curve (r,x21(r))",data12, unstablePlot, starBoundary},
 data12 = Sort[Map[Take[#, 2] &, unstableCurveData]];
 unstablePlot = ListLinePlot[data12, PlotRange -> {{0, 0.25}, {-3.2, -2.2}}];
 starBoundary = Plot[Sqrt[3] - 1/r, {r, 0.2, 0.25}, PlotStyle -> Directive[Red]];
 Show[unstablePlot, starBoundary]];


(* Most of the rest is junk, up until ExtractCoords and asymptotics. *)
(* junk *)
rdata := rdata = 
  Module[{tab, data, takesmall, rrs, ratio},
   SeedRandom[0];
   takesmall[x_] := Select[x, #[[2]] < 0.6 &];
   tab = Table[onetest, {i, 1, 100}];
   tab = Map[takesmall, tab];
   rrs[x_] := Map[#[[2]] &, x];
   tab = Map[rrs, tab];
   ratio[x_] := 
    Table[{x[[i]], x[[i + 1]]/x[[i]]}, {i, 1, Length[x] - 1}];
   tab = Flatten[Map[ratio, tab], 1] // Sort;
   tab];

junk := (
	rdata;
Last[rdata]
Show[ListLinePlot[Drop[rdata, 200]], Epilog -> Point[rdata]];
rfit[x_] = Fit[rdata, {1, x}, x];
Clear[rfix];
rfit2[x_] := x rfit[x];
rfit[0.2];
Plot[{rfit[x/Sqrt[7]], rfit[x]/Sqrt[7]}, {x, 0, 0.2}];
Module[{r1, r2},
 {r1, r2} = {0.1, 0.1};
 {rfit2[r1], rfit2[r2]}
]);

plotSwitchCurveDeprecated := Module[{ifun2, ifun, data2, datasparse},
   data2 = Map[{#[[1]], #[[2]]} &, unstableCurveData];
   ifun = Interpolation[data2]; 
   datasparse = {{0, ifun[0]}, {0.3, ifun[0.3]}, {0.639, ifun[0.639]}};
   Echo[{"switch", datasparse}];
   ifun2[x_] = Fit[datasparse, {1, x, x^2}, x];
   Plot[{ifun2[r], Min[1, (1 - r)/(Sqrt[3] r)]}, {r, 0.01, 1},
    Epilog -> Point[data2], PlotRange -> {{0, 1}, {0, 0.5}}]];
Clear[plotSwitchL11Curve, plotSwitchCurve];
mkfun[case_] := Module[{data2, ifun, datasparse, ifun2},
   data2 = Map[{#[[1]], #[[case]]} &, unstableCurveData];
   data2 = Select[data2, First[#] < 0.2 &];
   ifun = Interpolation[data2]; 
   datasparse = {{0, ifun[0]}, {0.1, ifun[0.1]}, {0.2, ifun[0.2]}};
   EchoOff[{"l11", datasparse}];
   Fit[datasparse, {1, r, r^2}, r]
		];
test:=(
x11fit[r_] = mkfun[2];
l11fit[r_] = mkfun[3];
l21fit[r_] = mkfun[4];
l21fit[0.1]);

plotSwitchXCurve[case_] := 
  Module[{doc = "case=2,3,4", fit, ifun2, ifun, data2, datasparse},
   fit[r_] = mkfun[case];
   data2 = Map[{#[[1]], #[[case]]} &, unstableCurveData];
   Plot[fit[r], {r, 0, 0.2},
    Epilog -> Point[data2]]];
test:= plotSwitchXCurve[4]; 

testContractSL := 
 Module[{doc = 
    "rewrite of testContract, later testContract is to be deprecated",
    width = 1/200, r, rmid, w, xmid0, xmid1, x0, x1, y0, y1}, 
  rmid = RandomReal[{10^-2, 10^-1}];
  xmid0 = {True, r, x11fit[r], l11fit[r], l21fit[r]};
  EchoOff[xmid0];
  r = rmid*RandomReal[{1/Sqrt[7.0], Sqrt[7.0]}];
  xmid1 = ReinhardtPoincareLie[xmid0];
  w := RandomReal[{-width, width}];
  x0 = Join[{True, r}, Drop[xmid0, 2] + {w, w, w}];
  x1 = ReinhardtPoincareLie[x0];
  {y0, y1} = Map[Sqrt[error2[Drop[#, 2]]] &, {xmid0 - x0, xmid1 - x1}];
  {y1/y0, xmid0[[2]]}
  ]

test := Table[testContractSL, {1}] // Sort // Last;

(* test that we hit the boundary *)

testBoundary := 
  Module[{doc = "", width = 1/200, r, rmid, w, xmid0, x1, x0, y0, y1},
    rmid = RandomReal[{0.2, 0.3}];
   xmid0 = {True, rmid, x11fit[rmid], l11fit[rmid], l21fit[rmid]};
   w := RandomReal[{-width, width}];
   x0 = Join[{True, rmid}, Drop[xmid0, 2] + {w, w, w}];
   x1 = ReinhardtPoincareLie[x0];
   If[First[x1], x1, {}]
   ];
testBoundary2 := 
  Module[{doc = "", width = 1/200, r, rmid, w, xmid0, x1, x0, y0, y1},
    rmid = RandomReal[{0.05, 0.1}];
   xmid0 = {True, rmid, x11fit[rmid], l11fit[rmid], l21fit[rmid]};
   w := RandomReal[{-width, width}];
   x0 = Join[{True, rmid}, Drop[xmid0, 2] + {w, w, w}];
   x1 = ReinhardtPoincareLie[x0];
   If[First[x1], {}, x0]
  ];

test := Union[Table[testBoundary, {1}]]
test := Union[Table[testBoundary2, {100}]]

junk := Module[{dataquadratic},
   dataquadratic[x_] = Module[{data},
     data = {{0, 0.4186}, {0.3, 0.389},(*{0.631,
       0.331}*){0.639, 0.326}};
     (1 - r)/(Sqrt[3] r) /. r -> 0.631;
     Fit[data, {1, x, x^2}, x]
     ];
   dataquadratic[0.1]];

nextest := Module[{r},
   r = RandomReal[{0.1, 0.2}];
   {r, ReinhardtPoincareLie[Flatten[{True, r, hyperboloid2Lie0out}]]}
	   ];

test := Module[{doc = "find r where we hit star boundary", tab},
   tab = Table[nextest, {i, 1, 50}];
   {Sort[Select[tab, #[[2, 1]] &]], 
    Sort[Select[tab, Not[#[[2, 1]]] &]]}
	];

(* Deprecate, Use ReinhardtPoincareLie *)

(*
test := Module[{X0, L10, LambdaR0, X, L1, ZP, LambdaRtil, d1V, l11V, 
    l12V, l21V, lR11V, lR12V, lR21V, tV, trV, x11V, x12V, x21V, r, x, 
    dummy, sub, sw, t1sw, R2, Xf, L1f, scale},
   r = 10^-4;
   EchoOff[{sl2out1[[1, 1, 1]], sl2out1[[1, 1, 2]], sl2out1[[2, 1, 1]], 
     sl2out1[[2, 1, 2]]}];
   {x11V, x21V, l11V, l21V} = {r*sl2out1[[1, 1, 1]], 
     sl2out1[[1, 2, 1]]*r, sl2out1[[2, 1, 1]]*r^2, 
     sl2out1[[2, 2, 1]]*r^2};
   X0 = J + {{x11V, x}, {x21V, -x11V}};
   {X0, x12V} = {X0, x} /. Flatten[Solve[Det[X0] == 1, x]];
   Echo[(X0 - J)/r];
   trV = Tr[X0.Z010];
   d1V = -Sqrt[-Det[Z010]]/trV;
   (* EchoOff[Sqrt[-Det[Z010]]]; *)
   
   L10 = -(3/2) J +  {{l11V, x}, {l21V, -l11V}};
   EchoOff[L10];
   {L10, l12V} = {L10, x} /. Flatten[Solve[Det[L10] == 9/4, x]];
   Echo[{(L10 + (3/2) J)/r^2, Det[L10]}];
   LambdaR0 = LRfromXL1[X0, L10];
   (*
   EchoOff[LambdaR0/r^3];
   EchoOff[{Tr[LambdaR0.X0],switch[Z010,Z001,X0,LambdaR0],Hamiltonian[
   Z010,X0,L10,LambdaR0,-1]}//Chop];
   EchoOff[LambdaR0];
   *)
   {{lR11V, lR12V}, {lR21V, dummy}} = LambdaR0;
   sub = {d1 -> d1V, l11 -> l11V, l12 -> l12V, l21 -> l21V, 
     lR11 -> lR11V, lR12 -> lR12V, lR21 -> lR21V, t -> r*t1, 
     tr -> trV, x11 -> x11V, x12 -> x12V, x21 -> x21V};
   {X, L1, ZP, LambdaRtil} = constantSolData /. sub(*//Simplify*);
   EchoOff[LambdaRtil];
   sw = switchtil[ZP, X0, LambdaRtil](*//Simplify*);
   t1sw =
    FindRoot[sw, {t1, 3.5}];
   EchoOff[t1sw];
   EchoOff[{Det[X /. t1sw], Det[L1 /. t1sw]}];
   R2 = R.R;
   {Xf, L1f} = {R2.X.Inverse[R2] - J, R2.L1.Inverse[R2] + (3/2) J} /. 
     t1sw;
   scale = Abs[Xf[[2, 1]]];
   EchoOff[scale];
   EchoOff[scale/r];
   {Xf/scale, L1f/scale^2}
   ];
 *)

skip := RepeatedTiming[test]

test := Module[
   {doc = "compute tsw using second method of switching function", X0,
     L10, LambdaR0, X, L1, LR, ZP, LambdaRtil, d1V, l11V, l12V, l21V, 
    lR11V, lR12V, lR21V, x11V, x12V, x21V, r, x, dummy, sub, sw, tsw, 
    R2, Xf, L1f, scale},
   r = 10^-4;
   
   EchoOff[{sl2out1[[1, 1, 1]], sl2out1[[1, 1, 2]], sl2out1[[2, 1, 1]], 
     sl2out1[[2, 1, 2]]}];
   {x11V, x21V, l11V, l21V} = {r*sl2out1[[1, 1, 1]], 
     sl2out1[[1, 2, 1]]*r, sl2out1[[2, 1, 1]]*r^2, 
     sl2out1[[2, 2, 1]]*r^2};
   X0 = J + {{x11V, x}, {x21V, -x11V}};
   {X0, x12V} = {X0, x} /. Flatten[Solve[Det[X0] == 1, x]];
   L10 = -(3/2) J +  {{l11V, x}, {l21V, -l11V}};
   {L10, l12V} = {L10, x} /. Flatten[Solve[Det[L10] == 9/4, x]];
   (*
   {x11V,x12V,l11V,l12V} = {r*sl2out1[[1,1,1]],-1*r,sl2out1[[2,1,
   1]]*r^2,sl2out1[[2,1,2]]*r^2};
   X0 = J + {{x11V,x12V},{x,-x11V}};
   {X0,x21V} = {X0,x}/.Flatten[Solve[Det[X0]\[Equal]1,x]];
   EchoOff[X0];
   L10 = -(3/2) J +  {{l11V,l12V},{x,-l11V}};
   {L10,l21V}= {L10,x}/.Flatten[Solve[Det[L10]\[Equal]9/4,x]];
   *)
   EchoOff[{(L10 + (3/2) J)/r^2, Det[L10]}];
   LambdaR0 = LRfromXL1[X0, L10];
   {X, L1, LR} = 
    constantControlSolutionNegDet[Z010, X0, L10, LambdaR0, -1];
   sw = normalizedSwitch[Z010, Z100, X, LR] /. {t -> r*t1};
   tsw = FindRoot[sw, {t1, 3.5}];
   {X, L1, LR} = {X, L1, LR} /. {t -> r*t1} /. tsw;
   EchoOff[{Det[X], Det[L1]}];
   R2 = R.R;
   {Xf, L1f, LR} = {R2.(X - J).Inverse[R2], 
     R2.(L1 + (3/2) J).Inverse[R2], R2.LR.Inverse[R2]};
   scale = Abs[Xf[[2, 1]]];
   EchoOff[scale];
   {Xf/scale, L1f/scale^2}
   ];

skip := test;

(* Jul 16, 2023 *)
test:=Module[{doc = "MCA. Formula for LR", X, L1},
  X = J + r {{x11, x12}, {x21, -x11}};
  (* x21=x21/.Solve[Det[X]\[Equal]1,x21]//Only; *)
  
  L1 = -(3/2) J + r^2 {{l11, l12}, {l21, -l11}};
  EchoOff[Solve[Det[L1] == 9/4, l21]];
  Series[LRfromXL1[X, L1]/r^3, {r, 0, 0}];
  LRfromXL1[X, L1]];

CfromLR[LR_] := 
 Module[{doc = "assumes form of LR in book", l11, l12, l21, l22},
  {{l11, l12}, {l21, l22}} = LR;
  (l12 + l21)/2 + I l11
 ];

MCAzfix1 := 
 Module[{doc = "interpretation of fixed point in Fuller", 
   tag = "MCA:zfix1", X00til, L10til, LR0til, w, b, c, detLambda10},
  {X00til, L10til, LR0til, 
    detLambda10} = {X0, Lambda10, LambdaR0, detLambda1} /. 
      triangleSub /. (y0 -> 1 - r) // Simplify;
  EchoOff[Series[Sqrt[detLambda10], {r, 0, 2}]];
  {w, b, c} = {WfromX[X00til], BfromL1[L10til], CfromLR[LR0til]};
  {w, b, c} = 
   Echo[Normal[{Series[w, {r, 0, 1}], Series[b, {r, 0, 2}], 
      Series[c, {r, 0, 3}]}]];
  rescale[{z1, z2, z3} /. {z1 -> w0/rho, z2 -> -I b0/(2 rho), 
      z3 -> c0/(6 rho)} /. {rho -> 2, w0 -> w, b0 -> b, c0 -> c}, 
	  2/r]];



(* replaced by asymptotics below *)

(*
testNov20obsolete :=
Module[{o, X0, x, x12V, l12V, L10, LambdaR0, L1, LR, X, d1, rho = 2, 
  z10, z20, z30, z10t, z20t, z30t, z1, z2, z3},
 X0 = J + r {{x11V, x}, {x21V, -x11V}};
 {X0, x12V} = {X0, x} /. Flatten[Solve[Det[X0] == 1, x]];
 L10 = -(3/2) J + r^2 {{l11V, x}, {l21V, -l11V}};
 {L10, l12V} = {L10, x} /. Flatten[Solve[Det[L10] == 9/4, x]];
 LambdaR0 = LRfromXL1[X0, L10];
 LambdaR0 = r^3 {{lR11, lR12}, {lR21, -lR11}};
 {X, L1, LR} = 
  constantControlSolutionPreComputeDet[Z010, X0, L10, LambdaR0, 
    d1] /. {t -> r*t1};
 o = (Normal[Series[X, {r, 0, 1}]] - J)/r;
 d1 = Sqrt[-Det[Z010]]/Tr[X0.Z010];
 
 Normal[Series[L1, {r, 0, 2}] + (3/2) J]/r^2 // Expand;
 Normal[Series[LR, {r, 0, 3}]]/r^3 // Expand;
 Normal[Series[WfromX[X], {r, 0, 1}]]/r // Expand;
 Normal[Series[WfromX[X0], {r, 0, 1}]]/r // Expand;
 Normal[Series[BfromL1[L1], {r, 0, 2}]]/r^2 // Expand;
 z10 = Normal[Series[WfromX[X0]/(r rho), {r, 0, 0}]];
 z10t = Normal[Series[WfromX[X]/(r rho), {r, 0, 0}]];
 z20 = Normal[-I  Series[BfromL1[L10]/(2 rho r^2), {r, 0, 0}]] // 
   Expand;
 z20t = Normal[-I  Series[BfromL1[L1]/(2 rho r^2), {r, 0, 0}]] // 
   Expand;
 z30 = Normal[Series[CfromLR[LambdaR0]/(6 rho r^3), {r, 0, 0}]];
 z30t = Normal[Series[CfromLR[LR]/(6 rho r^3), {r, 0, 0}]];
 {z1, z2, z3} = 
  solveCubicODE[zeta, {z10, z20, z30}] /. t -> t1 // ComplexExpand;
  
 o = Normal[
   Series[Hamiltonian[Z010, X, L1, LR, -1] - 
     Hamiltonian[Z100, X, L1, LR, -1]/r^3, {r, 0, 0}]];
 o  = {coeff[o/(24), t1, 3], 
    coeff[ComplexExpand[RR[zeta - 1, z3]], t1, 3]} // Simplify;
 Series[Tr[(L1 + (3/2) J).J], {r, 0, 3}];
 Series[(L1 + (3/2) J), {r, 0, 2}];
 o
];
 *)

(* Nov 28, 2023 current: *)

Echo["R2600"];

ExtractCoords[X_, L1_] := 
  Module[{doc = "(r,tildex)=(r,x11,l11,l21)in R4", x11, l11, l21, r, 
    X1, L},
   X1 = X - J;
   r = -X1[[2, 1]];
   x11 =  X1[[1, 1]]/r;
   L = L1 + (3/2) J;
   l11 = L[[1, 1]]/r^2;
   l21 = L[[2, 1]]/r^2;
   {r, x11, l11, l21}
  ];

asymptotics := 
 Module[{doc = "MCA:2446603", o, rho = 2, d1 = 3/2, det1, X0, x11V, 
   x12V, l12V, xzsub, L10, LambdaR0, LambdaR0series, L1, LR, X, Xtil, 
   L1til, LRtil, z10, z20, z30, z10t, z20t, z30t, z0, z1, z2, z3, Xsu,
    L1su, w, b, c, scale, chi21out, LRsu, R1, Xr, L1r, LR0sub, Ham100,
    Ham010, Ham001, hamF0, hamFzeta, hamF2, chi21, x3, y3, x2, y2, 
   z3bis, sw, xtilout, zeta = -1/2 + I Sqrt[3]/2}, 
  X0 = J + r {{x11V, x12V}, {-1, -x11V}};
  X0 = J + r {{x11V, x12V}, {x21V, -x11V}};
  x11V = 1;
  {X0, x12V} = {X0, x12V} /. Only[Solve[Det[X0] == 1, x12V]] // 
    Simplify;
  Echo[{"X0", X0}];
  Echo["star domain"];
  xzsub = Only[Solve[X0[[2]] == Phiz[[2]], {x, y}]];
  Solve[(x == 1/Sqrt[3] /. xzsub), x21V] // Echo;
  L10 = -(3/2) J + r^2 {{l11V, l12V}, {l21V, -l11V}};
  {L10, l12V} = {L10, l12V} /. Flatten[Solve[Det[L10] == 9/4, l12V]];
  Echo[{"L10", L10}];
  EchoOff[{"LR0", LRfromXL1[X0, L10]/r^3 // Simplify}];
  EchoOff[{"LR0-alt", 
    LRfromXL1[X0, -(3/2) J + r^2 {{l11, l12}, {l21, -l11}}]/r^3 // 
     Simplify}];
  LambdaR0series = 
   Echo[Normal[Series[LRfromXL1[X0, L10]/r^3, {r, 0, 0}]]];
  LR0sub = {lR11 -> LambdaR0series[[1, 1]], 
    lR12 -> LambdaR0series[[1, 2]], lR21 -> LambdaR0series[[2, 1]]};
  {"LR0sub", LR0sub} // Echo;
  {"lR12+lR21", {lR12 + lR21} /. LR0sub} // Echo;
  LambdaR0 = r^3 {{lR11, lR12}, {lR21, -lR11}};
  Echo["control Z010"];
  {X, L1, LR} = 
   constantControlSolutionPreComputeDet[Z010, X0, L10, LambdaR0, 
     det1] /. {t -> r*s};
  Echo[{"X-J[[2,1]]", Series[(X - J)[[2, 1]], {r, 0, 2}]}];
  (*asymptotics with z*){Xsu, L1su, LRsu} = {Cayley[X], Cayley[L1], 
    Cayley[LR]};
  {z1, z2, z3} = 
   wbc2z[{Xsu[[1, 2]], L1su[[1, 2]]/d1, LRsu[[1, 2]]}, rho];
  Echo[{"z1", Series[z1, {r, 0, 1}]}];
  {z1, z2, z3} = 
   Normal[Series[{z1/r, z2/r^2, z3/r^3}, {r, 0, 0}]] // Echo;
  z0 = D[z1, s];
  Echo[{"z limit", z0, z1, z2, z3} /. s -> 0];
  Echo[{"ode", D[z3, s] - z2, D[z2, s] - z1, D[z1, s] - z0, 
     z0 + I zeta} // Simplify];
  {x3, y3} = {Re[z3], Im[z3]} /. s -> 0 // ComplexExpand // Echo;
  {x2, y2} = {Re[z2], Im[z2]} /. s -> 0 // ComplexExpand // Echo;
  "ham" // Echo;
  hamF0 = (RR[z1, z2*I] + RR[1, x3 + I y3] /. s -> 0) /. LR0sub // 
    ComplexExpand;
  hamFzeta = (RR[z1, z2*I] + RR[zeta, x3 + I y3] /. s -> 0) // 
    ComplexExpand;
  hamF2 = (RR[z1, z2*I] + RR[Conjugate[zeta], x3 + I y3] /. s -> 0) //
     ComplexExpand;
  {"ham u=1", hamF0} // Echo;
  {"hamF at s=0", 
    Claim[{hamFzeta, hamF2} == {0, 0} /. LR0sub // Simplify, 
     "MCA:2446603 wall"]} // Echo;
  {"hamF 2nd order", (RR[zeta - Conjugate[zeta], x2 + I y2] /. 
         s -> 0 /. LR0sub // ComplexExpand // Simplify)} // Echo;
  {"hamF0s", 
    Claim[Simplify[
         Normal[Series[
            Hamiltonian[Z100, X0, L10, LambdaR0, -1], {r, 0, 3}]]/
          r^3] == (24) hamF0 /. LR0sub // Simplify]} // Echo;
  {"hamFzetas", 
    Claim[
     Simplify[
         Normal[Series[
            Hamiltonian[Z010, X0, L10, LambdaR0, -1], {r, 0, 3}]]/
          r^3] == (24) hamFzeta /. LR0sub // Simplify]} // Echo;
  {"hamFzeta2s", 
    Claim[Simplify[
         Normal[Series[
            Hamiltonian[Z001, X0, L10, LambdaR0, -1], {r, 0, 3}]]/
          r^3] == (24) hamF2 /. LR0sub // Simplify]} // Echo;
  z3bis = (x3 + I y3) /. 
    First[Solve[{hamFzeta == 0, hamF2 == 0}, {x3, y3}]];
  Echo[Cayley[LambdaR0series][[1, 2]]/(6 rho) - z3bis // Simplify];
  scale = -1/(2*Re[z10out]);
  zout = {z10out*scale, z20out*scale^2, z30out*scale^3};
  xtilout = 
   Solve[Drop[(EqTable[{Re[z1], Re[z2], Re[z3], Im[z1], Im[z2], 
           Im[z3]} // ComplexExpand, 
         Join[Re[zout], Im[zout]] // ComplexExpand] /. s -> 0), 
      1], {x11V, l11V, l21V, lR11, lR12, lR21}] // First;
  Echo[{"xtilout", Take[xtilout, 3]}];
  (*fixed point data*)
  Ham100 = Hamiltonian[Z100, X, L1, LR, -1];
  Ham010 = Hamiltonian[Z010, X, L1, LR, -1];
  Ham001 = Hamiltonian[Z001, X, L1, LR, -1];
  chi21 = Normal[Series[(Ham010 - Ham100)/r^3, {r, 0, 0}]];
  chi21out = chi21 /. xtilout // Simplify // Chop;
  sw = First[Solve[chi21out == 0, s, Reals]];
  R1 = Transpose[R];
  o = Series[(X - J)/r, {r, 0, 0}];
  Series[(X0 - X)/r, {r, 0, 0}];
  Xtil = NormalSeries[(X - J)/r, {r, 0, 0}] /. sw /. xtilout;
  L1til = NormalSeries[(L1 + (3/2) J)/r^2, {r, 0, 0}] /. sw /. xtilout;
  LRtil = LR/r^3 /. sw /. xtilout;
  Xr = R1.Xtil.R;
  -Xr[[1, 1]]/Xr[[2, 1]];
  L1r = R.L1til.R1;
  ExtractCoords[Xr, L1r];
  (Normal[Series[X, {r, 0, 1}]] - J)/r;
  det1 = Sqrt[-Det[Z010]]/Tr[X0.Z010];
  Normal[Series[L1, {r, 0, 2}] + (3/2) J]/r^2 // Expand;
  Normal[Series[LR, {r, 0, 3}]]/r^3 // Expand;
  o];

test := Module[{J1, o},
 J1 = (-3/2) J + r^2 {{l11, l12}, {l21, -l11}};
 o = Solve[Det[J1] == 9/4, l12];
 J1 = J + r {{x11, x12}, {-1, -x11}};
 Solve[Det[J1] == 1, x12]; o];

test := Module[{chiB, controlVec, z3},
  chiB = t^2 + 6 t y1 + 12 y2;
  controlVec[u_] := 
   ComplexExpand[{RR[u, x3 + I y3], RR[u, x2 + I y2], 
     RR[u, x1 + I y1]}];
  {controlVec[1], controlVec[zeta], 
    controlVec[Conjugate[zeta]]} /. {x3 -> 0, y3 -> 0};
  z3[u_] := solveCubicODE[u, x1 + I y1, x2 + I y2, 0] // Last;
     Abs[zeta - 1];
     Solve[-t^3/(4 Sqrt[3]) + Sqrt[3] t^2/2 + Sqrt[3] t + Sqrt[3.0] ==
        0, t];
     Module[{m = (3 + Sqrt[3.])/2}, 
      Solve[-t^3/(4 Sqrt[3]) + (t^2/2)  m + t m + 3/2 == 0, t, Reals]];
  chiB /. t -> 0;
  Solve[t^2 - 6 t - 12.0 == 0, t]];


test:=Module[{doc = "SAVE: lack of symmetry of Reinhardt switching functions", X0, x, 
  x12V, L10, l12V, LambdaR0, L1, LR, X, d1, d1001, X001, L1001, LR001,
   swdiff, o},
 X0 = J + r {{x11V, x}, {x21V, -x11V}};
 {X0, x12V} = {X0, x} /. Flatten[Solve[Det[X0] == 1, x]];
 L10 = -(3/2) J + r^2 {{l11V, x}, {l21V, -l11V}};
 {L10, l12V} = {L10, x} /. Flatten[Solve[Det[L10] == 9/4, x]];
 (* LambdaR0=LRfromXL1[X0,L10]; *)
  
 LambdaR0 =  r^3 {{lR11, lR12}, {lR21, -lR11}}; 
 {X, L1, LR} = 
  constantControlSolutionPreComputeDet[Z010, X0, L10, LambdaR0, 
    d1] /. {t -> r*t1}; 
 {X001, L1001, LR001} =
  constantControlSolutionPreComputeDet[Z001, X0, L10, LambdaR0, 
    d1]  /. {t -> r*t1}; 
 swdiff = 
  switch[Z010, Z001, X, LR] + switch[Z001, Z010, X001, LR001];
 o = Series[swdiff, {r, 0, 4}];
 o
      ];

Echo["R2700"];


(* Hypotrochoids Appendix .*)
hypotrochoid[r0_, r1_, r2_, t_] := Module[{},
   {(r2 - r1) Cos[t] + r0 Cos[-(r2 - r1) t/r1],
    (r2 - r1) Sin[t] + r0 Sin[-(r2 - r1) t/r1]}
   ];
FigHypotrochoid := Module[{r1 = 2.498, r0 = -10, r2},
  r2 = r2 /. Only[Solve[(r2 - r1)/r1 == 1/7, r2]];
  {r0, r1, r2};
  ParametricPlot[hypotrochoid[r0, r1, r2, t], {t, 0, 14 Pi}] // Echo;
		   ];

Echo["R-LOADED"];

(* PART II *)



(* Repeated Global Definitions *)
Echoing= False;
EchoOff[x_] := If[Echoing,Echo[x],x];

MCAID := Module[{doc = "create random identifier"}, 
  StringJoin["MCA:", ToString[RandomInteger[{10^6, 10^7}]]]];

Claim::usage="Claim[bool], Claim[bool,falsemsg]";

Claim[x_] := If[Not[TrueQ[x]], Echo[{"Failed Claim",x}],x];
Claim[x_, msg_] := If[Not[TrueQ[x]], Echo[{"Failed Claim",msg, x}],x];
Claim0[x_, msg_] := If[Not[TrueQ[x == 0]], Echo[{"Failed Claim",msg, x}],x];

Only[x_] := (Claim[Length[x] == 1, "Only"]; First[x]);

id:= RandomInteger[{10^6,10^7}];

complexNorm[zs_] := 
	Sqrt[Total[Abs[zs]^2]];

test := (complexNorm[{3 + 4 I, 1 + I}]^2 - (25 + 2))

RR[z1_, z2_] := Re[Conjugate[z1]*z2];

rescale[zs_, f_] := 
  Module[{doc = "weighted homogeneous rescaling"}, 
   Table[zs[[k]]*f^k, {k, 1, Length[zs]}]];

test = rescale[{1, 1, 1, 1}, 2];


(* End repeated Global Definitions *)

norm2[x_] := Simplify[x.x];

round[x_] := Round[x, 10^-5] // N // InputForm;

phiNorm[{z1_, z2_, z3_}] :=
	(Abs[z1]^6 + Abs[z2]^3 + Abs[z3]^2)^(1/6);

test :=phiNorm[{1, 1, 1}];

palindrome = 1 - 5 r - 7 r^2 - 5 r^3 - 7 r^4 - 5 r^5 + r^6;
rpal = r /. 
	  NSolve[palindrome == 0, r, Reals, WorkingPrecision -> 50][[2]];


phiscale[z_] := ComplexExpand[rescale[z, 1/phiNorm[z]]];

hamF[{z1_, z2_, z3_}, u_] := RR[z1, z2*I] + RR[u, z3];

solveCubicODE[u_, z10_, z20_, z30_] :=
  Module[{z1, z2, z3},
   z1 = -I*u*t + z10;
   z2 = -I*u*t^2/2 + z10*t + z20;
   z3 = -I*u*t^3/6 + z10*t^2/2 + z20*t + z30;
   {z1, z2, z3}];

solveCubicODE[u_, z_] := solveCubicODE[u, z[[1]], z[[2]], z[[3]]];

(* All zetas other than this should be local variables in modules *)

zeta = -1/2 + Sqrt[3] I/2; (* Exp[2 Pi I/3]; *)
zete = -1/2 + e Sqrt[3] I/2;

{chiA, chiB} = 
 Module[{doc = "chiA,chiB with u=zete", chiB, chiA, z3, 
   u = zete}, 
  z3 = solveCubicODE[u, x1 + I y1, x2 + I y2, x3] // Last;
  chiB = ComplexExpand[RR[zeta - zeta^2, z3]/Sqrt[3]/t];
  chiA = ComplexExpand[RR[u - 1, z3]/Sqrt[3]];
  {chiA, chiB}];

(*
obsolete:=Module[{doc = "obsolete. Only does u=1 control",solsystem,fixedpointFullerPoincare,z30val}, 
  solsystem = {r zeta1 z10 == -I t + z10, 
     r^2 zeta1 z20 == -I t^2/2 + z10 t + z20, 
     r^3 zeta1 z30 == -I t^3/6 + z10 t^2/2 + z20 t + z30} /. 
    t -> tsw;
  fixedpointFullerPoincare = Solve[solsystem, {z10, z20, z30}][[1]];
  z30val = z30 /. fixedpointFullerPoincare;];
 *)

fixedpointFullerPoincare := fixedpointFullerPoincare = Module[{doc="fixed point of Fuller-Poincare, symbolic form in tsw,u,r,zeta1",
  sol, solsystem}, 
  sol = solveCubicODE[u, {z10, z20, z30}] /. t -> tsw;
  solsystem = 
   Table[zeta1*r^i*({z10, z20, z30}[[i]]) == sol[[i]], {i, 1, 3}];
  Flatten[Solve[solsystem, {z10, z20, z30}]]];


zfix1 :=
	Module[{doc="the fixed point for r=1, corresponding to smoothed 6k+2-gons",tag="MCA:zfix1"},
	       {z10, z20, z30} /. fixedpointFullerPoincare /. {r -> 1, 
							       zeta1 -> zeta, u -> zeta^2, tsw -> Sqrt[3]} // FullSimplify];

zoutExact := zoutExact = 
  Module[{doc = "exact formula for outward equilibrium. r is palindrome rpal", z1, 
    z2, z3, zout, x1, y1, x2, y2, x3, 
    y3}, {z1, z2, 
     z3} = {z10, z20, z30} zeta /. fixedpointFullerPoincare /. {u -> 1, tsw -> 1, 
      zeta1 -> Exp[4 Pi I/3]};
   zout = 
    Simplify[
      ComplexExpand[
       rescale[{z1, z2, z3}, 1/Abs[Re[z1]]]], {r \[Element] Reals, 
       r > 0}] // Factor;
   {x1, y1, x2, y2, x3, y3} = 
    ComplexExpand[{Re[zout[[1]]], Im[zout[[1]]], Re[zout[[2]]], 
       Im[zout[[2]]], Re[zout[[3]]], Im[zout[[3]]]}] // Simplify;
   Claim[x1 == -1, "x1"];
   Claim[PolynomialRemainder[y3, palindrome, r] == 0, "y3"];
   y3 = 0;
   {{x1 , y1}, {x2 , y2}, {x3, y3} }
  ];

computeTswExact:=tswExact = Module[{doc = 
    "exact formula for tsw at equilibrium in hyperboloid coordinates, \
zoutExact", z1, z2, z3, x1, y1, x2, y2, x3, y3, switch, tsw, tswN, 
   poly, p1}, {{x1, y1}, {x2, y2}, {x3, y3}} = zoutExact;
  {z1, z2, z3} = 
   solveCubicODE[
     zeta, {s x1 + I s y1, s^2 x2 + I s^2 y2, s^3 x3 + I s^3 y3}] // 
    Expand;
  poly = PolynomialRemainder[ComplexExpand[RR[zeta - 1, z3]], 
       palindrome, r]/s^3 /. {t -> t*s} // Factor;
  EchoOff[poly];
  tsw = (2/Sqrt[3]) (r^2 + r + 1)/(r + 1);
  p1 = poly /. {t -> tsw} // Simplify;
  Claim0[PolynomialRemainder[p1, palindrome, r], "p1"];
  EchoOff[poly /. r -> rpal];
  tswN = t /. Flatten[NSolve[poly == 0 /. r -> rpal, t, Reals]];
  Claim0[tswN - tsw /. r -> rpal // Chop, "tswN"];
  tsw];

  (* computation of the solutions of fixed points *)

computeFullerFixedPoints :=  Module[{doc="fixed points",neg, rrat1, rrat2, np, roots, sol1, sol2},
  neg = z30 zeta1^2/tsw^3/.fixedpointFullerPoincare/.u->1;
  EchoOff[{neg /. zeta1 -> 1 // Simplify, "not real"}];
  rrat1 = ComplexExpand[Im[neg /. zeta1 -> zeta]] // Simplify;
  rrat2 = ComplexExpand[Im[neg /. zeta1 -> zeta^2]] // Simplify;
  np = rrat1/((r - 1)*palindrome) // Factor;
  Claim[Solve[np == 0, r] == {}, "palindrome"];
  Claim[rrat1 == rrat2, "sol"];
  roots = NSolve[rrat1, r, Reals];
  sol1 = Select[
    Table[{roots[[i]], neg /. {zeta1 -> zeta} /. roots[[i]]}, {i, 1, 
       Length[roots]}] // Chop, #[[2]] < 0 &];
  sol2 = Select[
    Table[{roots[[i]], neg /. {zeta1 -> zeta^2} /. roots[[i]]}, {i, 1,
        Length[roots]}] // Chop, #[[2]] < 0 &];
  {{"zeta", sol1}, {"zeta^2", sol2}}];

{z10out, z20out, z30out} = 
 Module[{ztil, zs}, 
  zs = {z10, z20, z30} /. fixedpointFullerPoincare /. {r -> rpal, zeta1 -> Exp[4 Pi I/3],
      tsw -> 1, u -> 1};
  Claim0[hamF[zs, 1] // Chop,"hamF out"];
  ztil = phiscale[zs] zeta // Chop];

{z10in, z20in, z30in} = {Conjugate[z10out], -Conjugate[z20out], 
			 Conjugate[z30out]};


(* Fuller Poincare map *)

rotateFullerObsolete[z_] := 
  Module[{doc = 
     "rotate s.t. zk has largest |Re|, where k is as large as \
possible (usually zk=z3). If z3 != 0 and on a wall, this outputs \
z3 real and negative.", zk, zz, index, out}, 
   zk = Last[Select[z, Chop[ComplexExpand[Abs[#]]] > 0 &]];
   zz = {zk, zeta*zk, zeta^2*zk};
   index = Ordering[Abs[Re[N[zz]]]] // Last;
   out = ComplexExpand[{z, zeta*z, zeta^2*z}[[index]]] // Chop;
   out];

rotateFullerIndex[z_, index_] := Module[{doc="rotate st Re[]<0"},
   If[Chop[N[Re[z[[index]]]]] < 0, Return[z]];
   If[Chop[N[Re[z[[index]] zeta]]] < 0, Return[z zeta]];
   z zeta^2
				 ];

rotateFullerALT[z_] := Module[{rfi, ca, ri = rotateFullerIndex},
   ca = Chop[Abs[z]];
   rfi = If[ca[[3]] > 0, ri[z, 3], 
     If[ca[[2]] > 0, ri[z, 2], ri[z, 1]]];
   Chop[rfi]
   ];

rotateFuller[z_] := 
  Module[{az = Chop[Abs[z]], i}, 
   i = Which[az[[3]] > 0, 3, az[[2]] > 0, 2, True, 1];
   Chop[rotateFullerIndex[z, i]]];

(*
rotateFullerObsolete[z_] := 
  Module[{i}, 
   i = Which[Chop[Abs[z[[3]]]] > 0, 3, Chop[Abs[z[[2]]]] > 0, 2, True,
      1];
   Chop[rotateFullerIndex[z, i]]];

rotateFuller[z_] := Module[{rfi, ca, ri = rotateFullerIndex},
   ca = Chop[Abs[z]];
   rfi = If[ca[[3]] > 0, ri[z, 3], 
     If[ca[[2]] > 0, ri[z, 2], ri[z, 1]]];
   Chop[rfi]
   ];
 *)

test:=rotateFuller[{1, 2, -zeta^2}]
test:=rotateFuller[{1, -zeta, 0}]
test:=rotateFuller[{zeta^2, 2 zeta^2, (-1 + I/10) zeta^2}] // ComplexExpand

							      
rescaleFullerWall[z_]:= Module[{doc="use virial to make z3 = -1 (if on a wall). Division by zero if z3=0",zx,r},
			       zx = rotateFuller[z];
			       r = Abs[zx[[3]]]^(1/3);
			       Claim[r > 0,"rescaleFullerWall"];
			       rescale[zx,1/r]];

test := rescaleFullerWall[{2 + 3 I, 3 + 4 I, zeta *(-7.0)}];


(* old version 
rescaleFullerWall[{z1_, z2_, z3_}] := 
  Module[{doc = 
     "normalize by forcing Fuller wall: z3=-1. Assumes z3 starts in a \
wall", r, zeta1},
   zeta1 = -Conjugate[z3/Abs[z3]];
   r = Abs[z3]^(1/3);
   rescale[zeta1*{z1, z2, z3}, 1/r] // Chop];
 *)

(* A version FullerPoincare is implemented next, which takes triples {z1,z2,z3}
   and does a more careful computation of first control.  *)

FullerPoincarePair[{z10_, z20_}] := 
	Module[{doc="discrete Fuller-Poincare dynamical system, Fuller wall form z30 =-1",
		u, z1, z2, z3, switchA, switchB, tA, tB, tsw},
   (* 1. set control *)   
   Claim[Chop[Im[z20]] != 0, "bad input"];
   u = If[Im[z20] > 0, zeta, zeta^2];
   EchoOff[{"u", u}];
   (* 2. Compute switching times *)
   {z1, z2, z3} = 
	 solveCubicODE[u, {z10, z20, -1}];
   switchA = ComplexExpand[RR[z3, u - 1]];
   switchB = ComplexExpand[RR[Simplify[(z3 + 1)/t], u - u^2]];
   tB = NSolve[(switchB == 0) && (t > 0), t, Reals];
   tA = NSolve[(switchA == 0), t, Reals];
   tsw = Min[Select[(t /. Join[tA, tB]), Positive]];
   {z1, z2, z3} = rescaleFullerWall[({z1, z2, z3} /. {t -> tsw})];
   EchoOff[{"z,tsw,hamF=", {z1, z2, z3, tsw, hamF[{z1, z2, z3}, u]}}];
   {z1, z2}
   ];

z3reduced[{z10_, z20_}, u_] := (-I/6)*t^2*u + (t*z10)/2 + z20; 

Claim[z3reduced[{z10, z20}, 
    u] ==
   (-z30 + solveCubicODE[u, {z10, z20, z30}][[3]])/t // 
      Simplify];

FullerPoincareU[{z10_, z20_, z30_}, u_] := 
 Module[{doc = 
    "Fuller Poincare dynamical system one step, assumes control u is zeta or zeta^2,
    u-u^2 is pure imaginary, z30 is real and drops out of switchB.
    No post-processing with virial group.",
   z1, z2, z3, z, switchA, switchB, tA, tB, tsw},
  {z1, z2, z3} = solveCubicODE[u, {z10, z20, z30}];
  switchA = ComplexExpand[RR[z3, u - 1]];
  switchB = ComplexExpand[RR[z3reduced[{z10, z20}, u], u - u^2]];
  tB = NSolve[(switchB == 0) && (t > 0), t, Reals];
  tA = NSolve[(switchA == 0), t, Reals];
  tsw = Min[Select[(Flatten[{t} /.Join[tA, tB]]), Positive]];
  EchoOff[{tsw, {switchA, tA}, {switchB, tB}}];
  z = {z1, z2, z3} /. {t -> tsw}];

ControlVector[{z1_, z2_, z3_}, u_] := 
	ComplexExpand[{RR[z3, u], RR[z2, u], RR[z1, u]}];

FirstControlLong[z_] := 
  Module[{v, s, s23}, 
   v = {ControlVector[z, 1], ControlVector[z, zeta], 
     ControlVector[z, Conjugate[zeta]]};
   EchoOff[v];
   s = Ordering[v];
   s23 = {s[[2]], s[[3]]};
   If[v[[s[[2]]]] == 
     v[[s[[3]]]],(*tie*)(EchoOff[{"first control tie ", v}];
     Which[s23 == {1, 2}, 1, s23 == {2, 3}, zeta, s23 == {1, 3}, 
      zeta^2]), {1, zeta, Conjugate[zeta]}[[Last[s]]]]];

FirstControl[z_] := Module[{},
   If[Chop[Re[z[[3]]]] < 0 && Chop[Im[z[[3]]]] == 0,
    Which[Chop[Im[z[[2]]]] > 0, zeta,
     Chop[Im[z[[2]]]] < 0, Conjugate[zeta],
     True, FirstControlLong[z]],
    FirstControlLong[z]]
		    ];

test = FirstControl[{1 + I, 0, 0}];

FullerPoincare[z_] := FullerPoincareU[z, FirstControl[z]];


rFullerPoincare[z_] := rotateFuller[FullerPoincare[rotateFuller[z]]];

rphiFullerPoincare[z_] := phiscale[rFullerPoincare[z]];

test:=Module[{z},
   z = rFullerPoincare[{z10in, z20in, z30in}];
   phiscale[z] - {z10in, z20in, z30in}] // Chop;

(* backwards *)

tauSymmetry[{z1_,z2_,z3_}]:= Conjugate[{z1,-z2,z3}];

revrphiFullerPoincare[z_]:= tauSymmetry[rphiFullerPoincare[rotateFuller[tauSymmetry[z]]]];

test:= Module[{zin,z},
	      zin = N[phiscale[{1+2I,2+3I,-1}]];
	      z = rphiFullerPoincare[zin];
	      zin-revrphiFullerPoincare[z]//Chop
       ]


(*Calculation of Stability at fixed point *)

linearizeXi[x_] := Module[{xisub}, xisub = {xi1 -> 0, xi2 -> 0, xi3 -> 0};
   (x /. xisub) + xi1 (D[x, xi1] /. xisub) + 
    xi2 (D[x, xi2] /. xisub) + xi3 (D[x, xi3] /. xisub)];

test:= linearizeXi[1/(1 + xi1)];

computeJacQout:=
	Module[{doc="compute eigenvalues and eigenvectors of Jacobian around fixed point qout, MCA:2776759",
		tsw1, zeta, zN0out, zXi, z1til, z2til, z3til, xi4, 
  switch, tswtil, r0til, A1, eqs, A},
 zeta = Exp[2 Pi I/3];
 zN0out = rescaleFullerWall[{z10out, z20out, z30out}];
 Claim[RR[zN0out[[2]], zeta - zeta^2] > 0, 
  "Check maximum principle for u=zeta"];
 zXi = zN0out + {xi1 + I xi2, xi3 + I xi4, 0};
 xi4 = linearizeXi[
   xi4 /. Solve[0 == Chop[ComplexExpand[hamF[zXi, zeta]]], 
      xi4][[1]]];
 Claim0[linearizeXi[ComplexExpand[hamF[zXi, zeta]] // Chop], "hamF"];
 {z1til, z2til, z3til} = solveCubicODE[zeta, zXi];
 switch = ComplexExpand[RR[zeta - 1, z3til]];
 tsw1 = (t /. 
    NSolve[(switch /. {xi1 -> 0, xi2 -> 0, xi3 -> 0}) == 0, t, 
      Reals][[1]]);
 Claim0[Chop[switch /. {t -> tsw1, xi1 -> 0, xi2 -> 0, xi3 -> 0}], 
  "switch time"];
 (*Newton's method*) 
 tswtil = linearizeXi[tsw1 - (switch/D[switch, t]) /. {t -> tsw1}];
 Claim0[linearizeXi[Chop[switch /. t -> tswtil]] // Chop, "switch root"];
 r0til = linearizeXi[(Chop[linearizeXi[-z3til/N[zeta^2, 50] /. {t -> tswtil}]])^(1/3)];
 A1 = linearizeXi[{z1til/(r0til zeta^2), z2til/(r0til^2 zeta^2), 
       z3til/(r0til^3 zeta^2)} /. {t -> tswtil}] - zN0out // Chop;
 Claim0[Chop[linearizeXi[ComplexExpand[hamF[zN0out + A1, zeta]]]], 
  "new ham"];
 Claim0[A1[[3]], "z3 change"];
 eqs = ComplexExpand[{Re[A1[[1]]], Im[A1[[1]]], Re[A1[[2]]]}];
 A = Table[D[eqs[[i]], {xi1, xi2, xi3}[[j]]], {i, 1, 3}, {j, 1, 3}];
 (*All less than 1.0 in magnitude!*)
	   {Eigenvalues[A], SingularValueList[A]}];


polyData = Module[{yv, xx3, z1, z2, z3, poly, disc, co},
   yv := {-1 + I y1v, x2v + I y2v, xx3};
   xx3 = xx3 /. Solve[ComplexExpand[hamF[yv, zeta]] == 0, xx3][[1]];
   {z1, z2, z3} = solveCubicODE[zeta, yv];
   poly = ComplexExpand[4 Sqrt[3] RR[z3, zeta - 1]];
   disc = ComplexExpand[Discriminant[poly, t]];
   co = coeff[poly, t, 3];
   {{z1, z2, z3}, poly, disc, co}
   ];

(* end of Jacobian *)
 

(* Aug 13 *)

genericrtheta := 
 Module[{doc = "z3=0, analysis of Fuller", z1, z2, z3, zs, utest, 
   switchA, switchB, tA, tB},
  z1 = Cos[theta] + I Sin[theta];
  z2 = r*z1;
  z3 = 0;
  zs = {z1, z2, z3};
  utest = zeta;
  {z1, z2, z3} = solveCubicODE[utest, zs];
  switchA = ComplexExpand[RR[z3, utest - 1]]/t // Simplify;
  tA = Solve[switchA == 0, t] // Simplify;
  Echo[{"tA", tA}];
  switchB = 
   ComplexExpand[RR[z3, utest - Conjugate[utest]]]/t // Simplify;
  Echo[{"switches", switchA, switchB}];
  tB = Echo[Solve[switchB == 0, t]];
  Echo[{"disc", Discriminant[switchA, t] // Simplify, 
    Discriminant[switchB, t] // Simplify}];
  Echo[{"result", Resultant[switchA, switchB, t]} // Simplify]
 ];


Echo["F400"];

(* CLASSICAL LOAD POINT *)

(* March 2024 endgame, adapted from fuller-feb6-2024.nb *)

zeta2 = Conjugate[zeta];
polarsub = {x1 -> r1 Cos[theta1], y1 -> r1 Sin[theta1], 
   x2 -> r2 Cos[theta2], y2 -> r2 Sin[theta2], 
   x3 -> 2 r1 r2 Sin[theta1 - theta2]};
hamF[{x1 + I y1, x2 + I y2, x3}, zete] /. polarsub // 
ComplexExpand // TrigExpand;

(hamF[{x1 + I y1, x2 + I y2, x3x}, zete] /. polarsub/.{x3x->x3})//ComplexExpand//Factor

(*Utilities*)

controlvector[sub_] := 
  Map[ControlVector[{x1 + I y1, x2 + I y2, 0} /. polarsub /. 
   sub, #] &, {1, zeta, zeta^2}] // N;

unitize[{r1_, r2_}] := 
  Module[{doc = "make cords st r1+r2=1", mu}, 
   mu = (r1 + Sqrt[r1^2 + 4 r2])/2;
   {r1/mu, r2/mu^2}];

Claim0[Module[{r1, r2},
 {r1, r2} = unitize[{r, s}];
 r1 + r2 -1// Simplify],"unitize"];

(* March 22, 2024. r2,psi,theta2 ordering of variables globally *)

cords[{z1_, z2_, z3_}] := 
  Module[{doc = "extract r2,psi,theta2", r1, r2, theta2, 
    psi}, {r1, r2} = unitize[{Abs[z1], Abs[z2]}];
   theta2 = Arg[z2];
   psi = theta2 - Arg[z1];
   psi = psi+ If[psi < 0, 2 Pi,0];
   {r2, psi, theta2}];

z3reducedk[{z10_, z20_, z30_}, u_, k_] := 
  Switch[k, 0, -I*u*t^3/6 + z10*t^2/2 + z20*t + z30, 
   1, (-I/6)*t^2*u + (t*z10)/2 + z20, 2, (-I/6)*t*u + (z10)/2, 
	 3, (-I/6)*u, _, 0];

switchFn[z0_, u1_, v1_, reduced_] := 
  ComplexExpand[RR[z3reducedk[z0, u1, reduced], u1 - v1]];

Clear[switchTimes,switchTime];

switchTimes[chi_]:=
    Module[{doc = "Return 0, if no positive root", nsol}, 
   nsol = NSolve[(chi == 0) && (t > 0), t, Reals];
   If[Length[nsol] == 0, {}, t /. nsol]];

switchTimes[z0_, u1_, v1_, reduced_] :=
	switchTimes[switchFn[z0,u1,v1,reduced]];

switchTime[chi_]:=
	Module[{doc = "time", tsws}, tsws = switchTimes[chi];
        If[Length[tsws] == 0, 0, Min[tsws]]];

switchTime[z0_, u1_, v1_, reduced_] := switchTime[switchFn[z0,u1,v1,reduced]];

switchTimeFirst[chiA_, chiB_] := Module[{doc="Return 0, if no positive root",ts, tsw},
   ts = Join[NSolve[(chiB == 0) && (t > 0), t, Reals], 
     NSolve[(chiA == 0) && (t > 0), t, Reals]];
   If[ts == {}, (Echo["switchTimeFirst, none found"]; 0), 
      Min[t /. ts]]];

test:=switchTimeFirst[(t - 2)*(t + 1), t - 3]

Disc[polyt_]:= Discriminant[polyt,t];

Disc[z0_,u1_,v1_,reduced_]:= Disc[switchFn[z0,u1,v1,reduced]];

(* Disc was DeltaFn *)

lemmaSwitchReversal := 
 Module[{mathca = "MCA:7477621,MCA:lem:switch-reversal", z, zstar, 
   chi, chistar}, 
  z = solveCubicODE[u0 + I u1, x1 + I y1, x2 + I y2, x3 + I y3];
  chi = ComplexExpand[RR[d0 + I d1, z[[3]]] /. {t -> ts - t}];
  EchoOff[Table[D[chi, {t, k}] /. t -> 0, {k, 0, 3}]];
  zstar = solveCubicODE[u0 - I u1, tauSymmetry[z /. t -> ts]];
  chistar = ComplexExpand[RR[d0 - I d1, zstar[[3]]]];
  Claim0[chistar - chi // Simplify, "MCA:7477621"];
  Table[D[chistar - chi, {t, k}] /. t -> 0, {k, 0, 3}]];


lemmaNegativeControl := 
  Module[{mathca = "MCA:1407931:lem:negative-control", z, zstar}, 
   z = tauSymmetry[
     solveCubicODE[u0 + I u1, x1 + I y1, x2 + I y2, 
       x3 + I y3] /. {t -> -t}];
   zstar = 
    solveCubicODE[u0 - I u1, 
     tauSymmetry[{x1 + I y1, x2 + I y2, x3 + I y3}]];
   Claim[z == zstar // ComplexExpand // Simplify, "MCA:1407831"]];

lemmaNegativeControl := 
  Module[{mathca = "MCA:1407931:lem:negative-control", z, zstar}, 
   z = tauSymmetry[
     solveCubicODE[u0 + I u1, x1 + I y1, x2 + I y2, 
       x3 + I y3] /. {t -> -t}];
   zstar = 
    solveCubicODE[u0 - I u1, 
     tauSymmetry[{x1 + I y1, x2 + I y2, x3 + I y3}]];
   Claim[z == zstar // ComplexExpand // Simplify, "MCA:1407831"]];

lemmaControlSymmetry := Module[{doc = "MCA:7021404"},
  Claim0[RR[zeta - zeta^2, 
      Last[solveCubicODE[zeta, x1 + I y1, x2 + I y2, x3 + I y3]]] +
     RR[zeta^2 - zeta, 
      Last[solveCubicODE[zeta^2, x1 + I y1, x2 + I y2, x3 + I y3]]] //
	 ComplexExpand, "MCA:7021404"]];

lemmaNonzero = Module[{doc = "MCA:9042347", z, zw, zz},
   z = solveCubicODE[1, x1 + I y1, x2 + I y2, x3 + I y3];
   zw = {Re[z], Im[z]} // ComplexExpand;
   zz = {x1 + I y1, x2 + I y2, x3 + I y3} /. 
     Only[Solve[
       zw == {{0, 0, 0}, {0, 0, 0}}, {x1, y1, x2, y2, x3, y3}]];
   Claim[zz == I {t, -t^2/2!, t^3/3!}, "MCA:9042347"]];

lemmaNoSingular = Module[{doc = "MCA:7251608, singular arcs", u3, Du3},
  u3 = (1/2) Integrate[u[s] (t - s)^2, {s, 0, t}];
  {D[u3, t], D[u3, {t, 2}], D[u3, {t, 3}]};
  Integrate[(1/2) (-1/2) (t - s)^2, {s, 0, t}]
		  ];



Echo["F500"];

test := FirstControl[{zeta, 0, 0}];
test := rotateFuller[FullerPoincare[rotateFuller[{zeta, 0, 0}]]];
(* Start Here *)
(* rotate redone *)

test := rotateFuller[{1, 2, -zeta^2}];
test := rotateFuller[{1, -zeta, 0}];
test := rotateFuller[{zeta^2, 2 zeta^2, (-1 + I/10) zeta^2}] // 
  ComplexExpand;


(* Obsolete 
funY[sub_] := 
  Module[{doc = "one-step-back", z0}, 
   z0 = {x1 + I y1, x2 + I y2, x3} /. polarsub /. sub;
   revrphiFullerPoincare[z0]];

funYCwithx3[sub_, u_] := 
  Module[{doc = "x3 need not be zero, y2=0", z0}, 
   z0 = {x1 + I y1, x2, x3} /. polarsub /. sub;
   rotateFuller[tauSymmetry[FullerPoincareU[z0, u]]]];

 *)

(* Use these *)
Clear[DataY2, data, DataZ, DataGeneric, DataGenericS];

DataZ[r2_, psi_, theta2_] := 
  {(1 - r2) Cos[psi - theta2] - I (1 - r2) Sin[psi - theta2], 
   r2 Cos[theta2] + I r2 Sin[theta2], -2 (1 - r2) r2 Sin[psi]};

Claim[DataZ[r, psi, 
    theta2o] - ({x1 + I y1, x2 + I y2, x3} /. 
       polarsub /. {r1 -> 1 - r, r2 -> r} /. {theta2 -> theta2o, 
      theta1 -> theta2o - psi}) == {0, 0, 0}, "DataZ"];

Claim0[hamF[DataZ[r, psi, theta], zeta] // ComplexExpand // 
       FullSimplify, "DataZ hamF"];

DataSZ[s1_, theta2_] :=
  {s1 Cos[theta2] + 
     I s1 Sin[theta2], (1 - Abs[s1]) Cos[theta2] + 
			I (1 - Abs[s1]) Sin[theta2], 0};

Claim[(DataSZ[s1, theta2o] - 
     Module[{doc = 
        "NB: z3=0, Allow negative r1, remove psi"}, {x1 + I y1, 
          x2 + I y2, x3} /. polarsub /. {r1 -> s1, 
         r2 -> 1 - Abs[s1]} /. {theta2 -> theta2o, 
        theta1 -> theta2o}]) == {0, 0, 0}, "DataSZ"];

										      
DataGeneric[zet1_, zet2_, k_, r_, psi_, 
   theta2_] :=
  {DataZ[r, psi, theta2], zet1, zet2, k};

DataGeneric[zet1, zet2, k, r, psi, theta2o] -
   Module[{doc = 
      "NB: y3=0"}, {{x1 + I y1, x2 + I y2, x3} /. 
        polarsub /. {r1 -> 1 - r, r2 -> r} /. {theta2 -> theta2o, 
       theta1 -> theta2o - psi}, zet1, zet2, k}] // Flatten // Union

(*to do,rewrite these*)
(* Eliminate these *)
							       

DataY20[zet1_, zet2_, k_, r_, psi_, 
   theta2_] :=
  {{(1 - r) Cos[psi - theta2] - 
     I (1 - r) Sin[psi - theta2], 
    r Cos[theta2], -2 (1 - r) r Sin[psi]}, zet1, zet2, k};

DataY20[zet1, zet2, k, r, psi, theta2] - 
   Module[{doc = "NB: y2=0,y3=0", data}, 
    data = {{x1 + I y1, x2, x3} /. polarsub /. {r1 -> 1 - r, 
         r2 -> r} /. {theta2 -> theta2, theta1 -> theta2 - psi}, 
	    zet1, zet2, k}] // Flatten // Union

 (* cordTauFull was fndata *)
					  
cordTauFull[data_] := Module[{doc="one step of tau-Fuller PoincareU with known data",
 tsw, z0, u, z}, u = data[[2]];
   z0 = data[[1]];
   tsw = Apply[switchTime, data];
   z = rotateFuller[solveCubicODE[u, z0] /. {t -> tsw}];
   cords[tauSymmetry[z]]];

test := cordTauFull[DataGeneric[zeta, 1, 1, 0.1, 0, Pi/2]];

(* Discontinuity, procedures *)

(*
getFarthest[x_, xs_] := Module[{doc="select from xs element furthest from x",y},
   y = Map[{Abs[x - #], #} &, xs];
   Sort[y, #1[[1]] < #2[[1]] &] // Last // Last];
test:= getFarthest[3, {2, -5, 0, 4, 5, 6, 7}];
 *)

getNearestPair[xs_, ys_] := Module[{doc="select from xs,ys pair closest together",z},
   z = First[
     Sort[Flatten[
       Table[{xs[[i]], ys[[j]], Abs[xs[[i]] - ys[[j]]]}, {i, 1, 
         Length[xs]}, {j, 1, Length[ys]}], 1], #1[[3]] < #2[[3]] &]];
   {Take[z, 2], Select[xs, # != z[[1]] &], Select[ys, # != z[[2]] &]}
   ];
test := getNearestPair[{0.1, 0.7, 0.9}, {0.5, 0.95, 0.11}];

visibleResultant[chi1_,chi2_] := 
    Module[{docs = 
	    "precondition: resultant(chi1,chi2)=0, true if \
tdouble is the least of the positive roots",  t1s,  t2s, 
	    tdoubles, tpos,echo=EchoOff,ignore},
	   echo["visRes"];
	   (*chi1 = Apply[switchFn, dataA0 /. r -> r0];*)
     t1s = t /. NSolve[chi1 == 0, t, Reals];
     (*     chi2 = Apply[switchFn, dataB1 /. r -> r0]; *)
     t2s = t /. NSolve[chi2 == 0, t, Reals];
     {{tdoubles, t1s, t2s},ignore} = echo[{getNearestPair[t1s, t2s],"visRes:getNearestPair"}];
     If[Min[tdoubles] <= 0, Return[False]];
     tpos = Select[Join[t1s, t2s], # > 0 && # < Min[tdoubles] &];
     If[Length[tpos] > 0, Return[False]];
     echo[True]];

visibleB[chiA_,chiB_] := 
    Module[{docs = 
       "precondition chiB is quadratic poly with a double root. Return true if that double \
root is the least of the positive roots of chiA,chiB",
	    DchiB, tdouble, 
      tAs,echo=EchoOff}, 
	    (*     chiB = Apply[switchFn, dataB1 /. r -> r0]; *)
	   DchiB = D[chiB, t];
	   {tdouble}= t/.NSolve[DchiB == 0, t, Reals];
     tAs = Solve[chiA==0 && t>0 && t< tdouble,t,Reals];
     If[Length[tAs] > 0, Return[False]];
     echo[True]];

visibleA[chiA_,chiB_] := 
    Module[{loc = 
       "precondition disc chiA=0, Return True if that double is \
the least of the positive roots.  Allow for posibility that disc chiA is slightly negative.",
	     DchiA, Dtsw, t1, t2, tdouble, 
      tB, tAs, tA,echo=EchoOff}, echo["visA"];
		    (* chiA = Apply[switchFn, dataA0 /. r -> r0]; *)
     DchiA = D[chiA, t];
     Dtsw = NSolve[DchiA == 0, t, Reals];
     If[Length[Dtsw] != 2, echo["visibleA:two solutions expected"];
      Return[False]];
     {t1, t2} = t /. Dtsw;
     tdouble = If[Abs[chiA /. t -> t1] < Abs[chiA /. t -> t2], t1, t2];
     If[tdouble <= 0, Return[False]];
     tB = NSolve[chiB==0 && t > 0 && t < tdouble,t,Reals];
     If[Length[tB]>0,Return[False]];
     tAs = t/.NSolve[chiA==0,t,Reals];
     tA=Sort[tAs,Abs[#1-tdouble]<Abs[#2-tdouble]&]//Last;
     echo[{"visA:r0 tAs,tA,tdouble",tAs,tA,tdouble}];
     If[0 < tA && tA < tdouble, Return[False]];
     echo[True]];



(* EDITED 3/15/2024, 3/22/ *)
Clear[Discontinuity];
Discontinuity[psi_, thet_] := 
  Module[{doc = 
     "Main tool for exploration of 3D cell: compute number of \
discontinuities in r, for fixed psi,theta2. On generic 3D cell.  The \
length of the output is the number of discontinuities.  The first \
component gives the value r0 of r at which the discontinuity appears. \
 The second component is the number of consecutive least roots of \
chiA, when r is at least r0 (up to the next critical value).  If \
#[[2]]==0, then first switching time is tswB1.  If positive, then the \
first switching time is tswA1. Output consists of triples \
{r,type,next}, where r0 is the critical point, type is dA,dB,rAB \
depending on the type of the critical point, and next is the relevant \
switching function for r>r0 ", u, switchType, chiA0, chiB1, res, 
    dataA0, dataB1, dataB2, discA0, discB1, rAB, rdiscA0, rdiscB1, rs,
        echo = EchoOff}, 
	 u = If[thet > 0, zeta, Conjugate[zeta]];
	 echo[{u, psi, thet}];
   dataA0 = DataGeneric[u, 1, 0, r, psi, thet];
   dataB1 = DataGeneric[u, Conjugate[u], 1, r, psi, thet];
   dataB2 = DataGeneric[u, Conjugate[u], 2, r, psi, thet];
   switchType[r0_] := 
    Module[{doc2 = "consecutive least chiA1 roots. A or B switching fn", 
	    tA0, tB1},
	   tB1 = Apply[switchTime, dataB1 /. r -> r0];
	   If[tB1==0,Return["A"]];
	   tA0 = Apply[switchTimes, dataA0 /. r -> r0];
	   (* Use AnyTrue *)
     tA0 = Select[tA0, (# > 0 && # < tB1) &];
     If[Length[tA0] > 0, "A", "B"]];
   chiA0 = Apply[switchFn, dataA0];
   chiB1 = Apply[switchFn, dataB1];
   res = Resultant[chiA0, chiB1, t];
   rAB = NSolve[res == 0 && r > 0 && r < 1, r, Reals];
   rAB = echo[Select[rAB, visibleResultant[(chiA0 /.#),(chiB1/.#)]&]];
   discA0 = echo[Discriminant[chiA0, t]];
   discB1 = Discriminant[chiB1, t];
   rdiscA0 = echo[NSolve[discA0 == 0 && r > 0 && r < 1, r, Reals]];
   rdiscA0 = echo[Select[rdiscA0, visibleA[(chiA0/.#),(chiB1/.#)]&]];
   rdiscB1 = NSolve[discB1 == 0 && r > 0 && r < 1, r, Reals];
   rdiscB1 = echo[Select[rdiscB1, visibleB[(chiA0/.#),(chiB1/.#)]&]];
   echo[{"rAB", rAB, "rdiscA0", rdiscA0, "rdiscB1", rdiscB1}];
   rs = 
     Union[Join[Map[{r /. #, "rAB"} &, rAB], 
       Map[{r /. #, "dA"} &, rdiscA0], 
       Map[{r /. #, "dB"} &, rdiscB1]]];
   rs = echo[Join[{{0, "START"}}, rs,{{1, "END"}}] // Sort];
   Table[
     Join[rs[[i]], {switchType[(rs[[i, 1]] + rs[[i + 1, 1]])/2]}], {i, 1, 
      Length[rs] - 1}]
   ];

(*Discontinuity[3.0,0.2] Discontinuity[3.1,0.4]*)

(*generate random points and plot discontinuities.Useful for \
exploration.*)

test:= Discontinuity[Pi/2, -1.0];

(* Discontinuity[2.95,3.0];
Discontinuity[2.95,0.4];
Discontinuity[3.1,0.129]; *)
(* Discontinuity[3.1,0.13] *)

test:=Discontinuity[3.07, 0.2]
test:=Discontinuity[3.08, 0.2]

(* Discontinuity[3.0,0.2]
Discontinuity[3.1,0.4] *)

(* generate random points and plot discontinuities. Useful for exploration. *)

(* EDITED 3/15/2024 *)
discontinuityListPlot[{psimin_, psimax_}, {theta2min_, theta2max_}, 
   num_] := 
  Module[{tab, eps = 0.01}, 
   tab = Table[{RandomReal[{psimin + eps, psimax - eps}], 
      RandomReal[{theta2min + eps, theta2max - eps}]}, {i, 1, num}];
   tab = Map[{#[[1]], #[[2]], Discontinuity[#[[1]], #[[2]]]} &, tab];
   Echo[Take[tab, Min[10, num]]];
   (*Echo[Map[Map[Last,#]&,Map[Last,tab]]];*)
   tab = GatherBy[tab, Map[(Drop[#, 1] &), Last[#]] &];
   Echo[Length[tab]];
   Echo[Map[Take[#, Min[3, Length[#]]] &, tab]];
   tab = Table[Map[Take[#, 2] &, tab[[i]]], {i, 1, Length[tab]}];
   ListPlot[tab, 
    PlotLabel -> 
     ToString[{"discontinuityListPlot", {psimin, psimax}, {theta2min, 
        theta2max}, num, "num colors", Length[tab]}, InputForm]]];

test := discontinuityListPlot[{0, Pi}, {-Pi/3, 0}, 100];
test := discontinuityListPlot[{2.92, Pi}, {0, 0.4}, 500];
test := discontinuityListPlot[{0, Pi}, {-Pi, -Pi/3}, 100];
test := discontinuityListPlot[{2.5, Pi}, {0, 1}, 500];
test:= discontinuityListPlot[{2.92, Pi}, {0, 0.4}, 1000];

Clear[rDiscA0];
Echo["F814"];

rDiscA0[psi_, theta2_] := 
	Module[{doc="Precursor to Discontinuity. \
   Find r s.t. DiscA0[r,psi,theta2]==0",dataA0, discA0, eps = 0.00001, rsub,u},
	u=If[theta2>0,zeta,Conjugate[zeta]];
  dataA0 = DataGeneric[u, 1, 0, r, psi, theta2];
  discA0 = EchoOff[Apply[Disc, dataA0]];
  rsub = EchoOff[NSolve[discA0 == 0, r, Reals]];
  (* Plot[discA0/.r\[Rule]r0,{r0,eps,1-eps}] *)
  If[rsub=={},{},
     Select[r /. rsub, # > 0 && # <= 1 &]]
  ];

test:={"test rDiscA0",rDiscA0[Pi/2, -0.1]};



test := Module[{doc = "disc0 contour surface upper, SAVE"}, 
  ContourPlot[
   Max[rDiscA0[psi, theta0]], {psi, 0, 
    Pi}, {theta0, -Pi/3 + 0.001, -0.001}, ContourLabels -> True]]

test := Module[{doc = "disc0 contour surface lower, SAVE"}, 
   ContourPlot[
    Min[rDiscA0[psi, theta0]], {psi, 0, 
     Pi}, {theta0, -Pi/3 + 0.001, -0.001}, ContourLabels -> True]];

aborted := 
  Module[{doc = 
     "Disc=0 doubled contour surface lower, too slow aborted"}, 
   RegionPlot[
    Length[rDiscA0[psi, theta0]] == 2, {psi, 0, 
     Pi}, {theta0, -Pi/3 + 0.001, -0.001}]];

test:={"test NumberForm",NumberForm[rDiscA0[3.1, -0.01], 30]};

Echo["rDiscA0"];

(* 3/2024 *)

(* started by looking at slices, but then realized that Plot3D could
handle the full 3D situation in surfaceDiscAPlot3D *)

sliceListPlot[{psimin_, psimax_}, {theta2min_, theta2max_}, num_] := 
  Module[{tab, r0 = 0.4, eps = 0.01, type}, 
   tab = Table[{RandomReal[{psimin + eps, psimax - eps}], 
      RandomReal[{theta2min + eps, theta2max - eps}]}, {i, 1, num}];
   type[{psi_, th_}] := Module[{ds},
     ds = Discontinuity[psi, th];
     EchoOff[Last[Select[ds, #[[1]] < r0 &]]]
     ];
   tab = Map[{#[[1]], #[[2]], Last[type[#]]} &, tab];
   (*Echo[Map[Map[Last,#]&,Map[Last,tab]]];*)tab = GatherBy[tab, Last];
   Echo[Length[tab]];
   tab = Table[Map[Take[#, 2] &, tab[[i]]], {i, 1, Length[tab]}];
   ListPlot[tab, 
    PlotLabel -> 
     ToString[{"sliceListPlot", {psimin, psimax}, {theta2min, theta2max},
        num, "num colors", Length[tab]}, InputForm]]];


sliceRegion[{psimin_, psimax_}, {theta2min_, theta2max_}] := 
	Module[{doc="r0-slice, showing where Disc(chiA0)<0",
		tab, r0 = 0.4, eps = 0.01, chiA0, delA, skip,eps2=0.0001},
   chiA0 = 
    Apply[switchFn, 
     DataGeneric[Conjugate[zeta], 1, 0, r0, 
      Pi - psi0, -Pi - thet20]];
   delA = Discriminant[chiA0, t];
   skip := 
    ContourPlot[(delA /. {psi0 -> psi, thet20 -> th}), {psi, psimin, 
      psimax}, {th, theta2min, theta2max}, ContourLabels -> True];
   RegionPlot[(delA /. {psi0 -> psi, thet20 -> th}) < eps2, {psi, 
     psimin, psimax}, {th, theta2min, 
     theta2max}, {PlotStyle -> Directive[LightGray], 
     PlotStyle -> Opacity[1.0]}]
  ];

sliceR04RegionPlot := sliceRegion[{0, Pi}, {-Pi, 0}]
test := sliceListPlot[{0.8, 1.1}, {-0.08, 0}, 500]

(* wonderful illustration of the tswA vs tswB regions, when theta2 (-Pi/3,0) *)

surfaceDiscAPlot3D := Module[{tab, eps = 0.01, chiA0, delA, skip},
   chiA0 = 
    Apply[switchFn, 
     DataGeneric[Conjugate[zeta], 1, 0, r0, psi0, thet20]];
   delA = Discriminant[chiA0, t];
   RegionPlot3D[(delA /. {r0 -> r, psi0 -> psi, thet20 -> th}) < 
     0, {r, 0, 1}, {psi, 0, Pi}, {th, -Pi/3, 
     0}, {PlotStyle -> Directive[LightGray], 
     PlotStyle -> Opacity[1.0], PlotLabel -> "surfaceDiscAPlot3D"}]
   ];

(* criticalImageY2 is experimental 3/2024,
to explore image of 3D critical surfaces in 2D cells *)

criticalImageY2[psi_, theta2_] := 
  Module[{doc="Experimental",r, ds, z, Fz, eps = 10^-6, Fr, Fth, Fpsi},
   ds = EchoOff[Discontinuity[psi, theta2]];
   EchoOff[ds];
   r = Last[ds] // First;
   r = If[r + 2*eps >= 1, (r + 1)/2, r + eps];
   EchoOff[r];
   z = DataZ[r, psi, theta2];
   EchoOff[z];
   Fz = EchoOff[rotateFuller[FullerPoincare[z]]];
   {Fr, Fpsi,Fth} = EchoOff[cords[Fz]];
   {Fr, Fpsi}
  ];

test:= criticalImageY2[1.5, -0.5];
test := Module[{p1, p2, p3, p4, skip}, 
  p1 = ParametricPlot[criticalImageY2[psi, -1.04], {psi, 0.1, 3.14}, 
    PlotRange -> {{0, 1}, {0, Pi}}];
  p2 = ParametricPlot[criticalImageY2[3.14, thet2], {thet2, -1.04, -0.01}, 
    PlotRange -> {{0, 1}, {0, Pi}}];
  p3 = ParametricPlot[criticalImageY2[psi, -0.01], {psi, 1.1, 3.14}, 
    PlotRange -> {{0, 1}, {0, Pi}}];
  p4 = ParametricPlot[
    Apply[criticalImageY2, {0, -Pi/3} + l1 {0.8, Pi/3}], {l1, 0.1, 1 - 0.1}, 
    PlotRange -> {{0, 1}, {0, Pi}}];
  Show[{p1, p2, p3, p4}]]




test45Obsolete := 
  Module[{doc = "boundary chiA,chiB via image of x3=0", 
    eps = 0.001, u = zeta, uc = Conjugate[zeta], plot4, plot5, psi, 
    thmin, thmax, funYC, skip}, 
   funYCObsolete[sub_, u_] := 
    Module[{docYC = "x3=0", z0}, 
     z0 = {x1 + I y1, x2 + I y2, 0} /. polarsub /. sub;
     rotateFuller[tauSymmetry[FullerPoincareU[z0, u]]]];
   {thmin, thmax} = Echo[{Pi/3 + eps, 2 Pi/3 - eps}];
   plot4 = 
    ParametricPlot3D[{cords[
       funYC[{r1 -> 1 - r, r2 -> r, theta1 -> theta - Pi, 
         theta2 -> theta}, u]], 
      cords[funYC[{r1 -> 1 - r, r2 -> r, theta1 -> theta, 
         theta2 -> theta}, u]]}, {r, eps, 1 - eps}, {theta, thmin, 
      thmax}, PlotRange -> {{0, 1}, {-Pi, Pi}, {0, Pi}}, 
     PlotStyle -> Directive[Red]];
   {thmin, thmax} = {4 Pi/3 + eps, 5 Pi/-eps};
   skip := 
    plot5 = ParametricPlot3D[{(*cords[funYC[{r1\[Rule]1-r,r2\[Rule]r,
       theta1\[Rule]theta-Pi,theta2\[Rule]theta},uc]],*)
       cords[funYC[{r1 -> 1 - r, r2 -> r, theta1 -> theta, 
          theta2 -> theta}, uc]]}, {r, eps, 1 - eps}, {theta, thmin, 
       thmax}, PlotRange -> {{0, 1}, {-Pi, Pi}, {0, Pi}}, 
			     PlotStyle -> Directive[Red]]; Show[{plot4}]];

surfaceResultantPlot3DObsolete := 
  Module[{doc = "boundary chiA,chiB via image of x3=0, replaces test45, save. Replaed with surfaceResultantPlot...", 
    eps = 0.001, plot4, psi, thmin, thmax, fun, skip}, 
   fun[s1_, theta2_] := 
    Module[{docYC = "x3=0", z0, u}, z0 = DataSZ[s1, theta2];
     u = If[theta2 > 0, zeta, Conjugate[zeta]];
     cords[rotateFuller[tauSymmetry[FullerPoincareU[z0, u]]]]];
   {thmin, thmax} = Echo[{Pi/3 + eps, Pi - eps}];
   plot4 = 
    ParametricPlot3D[
     fun[s1, theta2], {s1, -1 + eps, 1 - eps}, {theta2, thmin, thmax},
      PlotRange -> {{0, 1}, {0, Pi}, {-0.1, Pi}}, 
     PlotStyle -> Directive[Red]];
   Show[{plot4}]];

surfaceResultantPlot3DAlt := 
  Module[{doc = 
     "boundary chiA,chiB via image of x3=0, replaces test45, save", 
    eps = 10^-3, plot4, plot4A, plot5, psi, thmin, thmax, fun, fun2, 
    skip}, fun[s1_, theta2_] := 
    Module[{docYC = "x3=0", z0, u}, z0 = DataSZ[s1, theta2];
     u = If[theta2 > 0, zeta, Conjugate[zeta]];
     cords[rotateFuller[tauSymmetry[FullerPoincareU[z0, u]]]]];
   {thmin, thmax} = Echo[{Pi/3 + eps, Pi - eps}];
   plot4 = 
    ParametricPlot3D[
     fun[s1, theta2], {s1, -1 + eps, 1 - eps}, {theta2, thmin, thmax},
      PlotRange -> {{0, 1}, {0, Pi}, {-0.1, Pi}}, 
     PlotStyle -> {LightRed, Opacity[0.4]}];
   plot4A = 
    ParametricPlot3D[fun[-1 + eps, theta2], {theta2, thmin, thmax}, 
     PlotStyle -> {Black, Thick}];
   fun2[r_, psi_] := Module[{doc2 = "", z0, u},
     z0 = DataZ[r, psi, Pi - eps];
     u = zeta;
     cords[rotateFuller[tauSymmetry[FullerPoincareU[z0, u]]]]
     ];
   plot5 = 
    ParametricPlot3D[
     fun2[r, psi], {r, eps, 1 - eps}, {psi, eps, Pi - eps}, 
     PlotStyle -> Directive[Yellow]];
   Show[{plot4, plot4A, plot5}]];

surfaceSZResultantPlot3D := 
 Module[{doc = 
    "compute active switching function, exploration of 2D cells, \
     x3=0, image in 3D generic cell.\
     Composite case is what is most relevant. Other stuff is experimental\
     Longer experimental version of surfaceResultantPlot3D.",
	 eps, epspsi, psi, u, tswB1, tswA1, 
   res, thmin, thmax, skip, discA1, discB1, p1p1, p1m1, m1p1, m1m1A, 
   m1m1B, beps = 0.02, plotrange = {{0, 1}, {-0.1, Pi}, {0, Pi}}},
  
  tswA1[r_, thet_, u_, psi_] := 
   Apply[switchTime, DataGeneric[u, 1, 1, r, psi, thet]];
  tswB1[r_, thet_, u_, psi_] := 
   Apply[switchTime, DataGeneric[u, Conjugate[u], 1, r, psi, thet]];
  res[r_, thet_, u_, psi_] := 
   Resultant[
    Apply[switchFn, DataGeneric[u, Conjugate[u], 1, r, psi, thet]], 
    Apply[switchFn, DataGeneric[u, 1, 1, r, psi, thet]], t];
  discA1[r_, thet_, u_, psi_] :=
   
   Discriminant[Apply[switchFn, DataGeneric[u, 1, 1, r, psi, thet]], 
    t];
  discB1[r_, thet_, u_, psi_] := 
   Discriminant[
    Apply[switchFn, DataGeneric[u, Conjugate[u], 1, r, psi, thet]], t];
  
  (* new case +1 +1 *)
  {eps, epspsi, psi, thmin, thmax, u} = {1, 1, 
    0, Pi/3, 2 Pi/3, u = zeta};
  Echo[{"case (eps,epspsi,psi,thmin,thmax)=", eps, epspsi, psi, thmin,
     thmax}];
  Echo[tswA1[0.1, 1.4, u, psi]];
  Echo[tswB1[0.1, 1.4, u, psi]];
  skip := 
   Echo[ContourPlot[
     res[r0, thet0, u, psi], {r0, 0, 1}, {thet0, thmin, thmax}, 
     ContourLabels -> True]];
  skip := 
   Echo[ContourPlot[
     tswA1[r0, thet0, u, psi] - 0*tswB1[r0, thet0, u, psi], {r0, 0, 
      1}, {thet0, thmin, thmax}, ContourLabels -> True]];
  p1p1 := 
   Echo[ParametricPlot3D[
     cordTauFull[DataGeneric[u, 1, 1, r, psi, thet]], {r, beps, 
      1 - beps}, {thet, thmin + beps, thmax - beps}, 
     PlotRange -> plotrange]];
  
  
  {eps, epspsi, psi, thmin, thmax, u} = {1, -1, Pi, Pi/3, 2 Pi/3, 
    zeta};
  Echo[{"case (eps,epspsi,psi,thmin,thmax)=", eps, epspsi, psi, thmin,
     thmax}];
  Echo[tswA1[0.1, 1.6, u, psi]];
  Echo[tswB1[0.1, 1.6, u, psi]];
  skip := 
   Echo[ContourPlot[
     res[r0, thet0, u, psi], {r0, 0, 1}, {thet0, thmin, thmax}, 
     ContourLabels -> True]];
  skip := 
   Echo[ContourPlot[
     tswA1[r0, thet0, u, psi], {r0, 0, 1}, {thet0, thmin, thmax}, 
     ContourLabels -> True]];
  p1m1 := 
   Echo[ParametricPlot3D[
     cordTauFull[DataGeneric[u, 1, 1, r, psi, thet]], {r, beps, 
      1 - beps}, {thet, thmin + beps, thmax - beps}, 
     PlotRange -> plotrange]];
  
  
  (* new case *)
  {eps, epspsi, psi, thmin, thmax, u} = {-1, 1, 0, 
    4 Pi/3, 5 Pi/3, Conjugate[zeta]};
  Echo[{"case (eps,epspsi,psi,thmin,thmax)=", eps, epspsi, psi, thmin,
     thmax}];
  Echo[tswA1[0.4, 3 Pi/2, u, psi]];
  Echo[tswB1[0.4, 3 Pi/2, u, psi]];
  skip := 
   Echo[ContourPlot[
     res[r0, thet0, u, psi], {r0, 0, 1}, {thet0, thmin, thmax}, 
     ContourLabels -> True]];
  skip := 
   Echo[ContourPlot[
     tswA1[r0, thet0, u, psi] - tswB1[r0, thet0, u, psi], {r0, 0, 
      1}, {thet0, thmin, thmax}, ContourLabels -> True]];
  m1p1 := 
   Echo[ParametricPlot3D[
     cordTauFull[DataGeneric[u, Conjugate[u], 1, r, psi, thet]], {r, beps, 
      1 - beps}, {thet, thmin + beps, thmax - beps}, 
     PlotRange -> plotrange]];
  
  (* new case *)
  {eps, epspsi, psi, thmin, thmax, u} = {-1, -1, Pi, 
    4 Pi/3, 5 Pi/3, Conjugate[zeta]};
  Echo[{"case (eps,epspsi,psi,thmin,thmax)=", eps, epspsi, psi, thmin,
     thmax}];
  Echo[tswA1[0.4, 3 Pi/2, u, psi]];
  Echo[tswB1[0.4, 3 Pi/2, u, psi]];
  skip := 
   Echo[ContourPlot[
     discA1[r0, thet0, u, psi], {r0, 0, 1}, {thet0, thmin, thmax}, 
     ContourLabels -> True]];
  skip := 
   Echo[ContourPlot[
     res[r0, thet0, u, psi], {r0, 0, 1}, {thet0, thmin, thmax}, 
     ContourLabels -> True]];
  skip := 
   Echo[ContourPlot[
     tswA1[r0, thet0, u, psi] - tswB1[r0, thet0, u, psi], {r0, 0, 
      1}, {thet0, thmin, thmax}, ContourLabels -> True]];
  m1m1B := (* incomplete *)
   Echo[ParametricPlot3D[
     cordTauFull[DataGeneric[u, Conjugate[u], 1, r, psi, thet]], {r, 0.33, 
      1 - beps}, {thet, thmin + beps, thmax - beps}, 
     PlotRange -> plotrange]];
  m1m1A := (* incomplete *)
   Echo[ParametricPlot3D[
     cordTauFull[DataGeneric[u, 1, 1, r, psi, thet]], {r, 0, 0.2}, {thet, 
      thmin + beps, 4.65}, PlotRange -> plotrange]];
  skip := Show[{p1p1, p1m1, m1p1, m1m1A, m1m1B}];
  
  Echo[{"composite case"}];
  {thmin, thmax, u} = {Pi/3, Pi, zeta};
  res[s_, thet_] := 
   Resultant[
	   Apply[switchFn, {DataSZ[s, thet],u, Conjugate[u], 1}], 
	   Apply[switchFn, {DataSZ[s, thet],u, 1, 1}], t];
  tswA1[s_, thet_] := 
	Apply[switchTime, {DataSZ[s, thet],u, 1, 1}];
  tswB1[s_, thet_] := 
	Apply[switchTime, {DataSZ[s, thet],u, Conjugate[u], 1}];
  discB1[s_, thet_] := 
   Discriminant[
	   Apply[switchFn, {DataSZ[s, thet],u, Conjugate[u], 1}], t];
  discA1[s_, thet_] := 
	Discriminant[Apply[switchFn, {DataSZ[s, thet],u, 1, 1}], t];
  Echo[discB1[s, theta] // Simplify];
  Echo[Collect[
    4 Sqrt[3] Apply[switchFn, 
		    {DataSZ[s, thet],u, Conjugate[u], 1}] // Simplify, t]];
  Echo[tswB1[0.9, 1.5]];
  Echo[{"B1", tswB1[-0.9, 1.5]}];
  Echo[{"A1", tswA1[-0.9, 1.5]}];
  skip := 
   Echo[ContourPlot[res[s, thet], {s, -1, 1}, {thet, thmin, thmax}, 
     ContourLabels -> True]];
  skip := 
   Echo[ContourPlot[discA1[s, thet], {s, -1, 1}, {thet, thmin, thmax},
      ContourLabels -> True]];
  skip := 
   Echo[ContourPlot[
     tswB1[s, thet] - tswA1[s, thet], {s, -1, 1}, {thet, thmin, 
      thmax}, ContourLabels -> True]];
  globalResultantSurface = 
   Echo[ParametricPlot3D[
	   cordTauFull[{DataSZ[s, thet],u, 1, 1}], {s, -1 + beps, 
      1 - beps}, {thet, thmin + beps, thmax - beps}, 
     PlotRange -> plotrange]];
  Echo[Collect[
    4 Sqrt[3] Apply[switchFn, 
		    {DataSZ[s, Pi/3 + alpha],u, 1, 1}] // Simplify, t]];
  beps = 0.001; 
  Echo["boundary"];
  Show[{ParametricPlot3D[{cordTauFull[
	  {DataSZ[s, Pi/3 + beps],u, 1, 1}], 
      cordTauFull[DataSZ[u, 1, 1, s, Pi - beps]]}, {s, -1 + beps, 
      1 - beps}, PlotRange -> plotrange, PlotStyle -> {Blue, Yellow}],
	ParametricPlot3D[{cordTauFull[{DataSZ[ -1 + beps, thet],u, 1, 1}],
			  cordTauFull[{DataSZ[ 1 - beps, thet],u, 1, 1}]}, {thet, 
      thmin + beps, thmax - beps}, PlotRange -> plotrange, 
     PlotStyle -> {Red, Orange}]}]
  ];

incompleteSZ := 
 Module[{doc = "asymptotics x3=0", data, chi, ode, ts, z},
	data = {DataSZ[ -1 + x, Pi/3 + eps],zeta, 1, 1};
  chi = Apply[switchFn, data];
  ts = EchoOff[Solve[chi == 0, t]];
  Echo[Simplify[Normal[Series[t /. ts[[1]], {x, 0, 1}]], 
    Sin[eps] > 0]];
  ode = solveCubicODE[zeta, data[[1]]] /. ts[[1]];
  ode = Normal[
    Series[zeta solveCubicODE[zeta, data[[1]]] /. ts[[1]], {x, 0, 1}]];
  z = Simplify[
    ode, {x > 0, -1 + d1 x < 0, d2 > 0, Sin[eps] > 0, -1 + x < 0} ];
  z
 ];

testGenericFace := 
 Module[{doc = 
    "generic face analysis, incomplete, it is still messy, mixing \
different switching behavior march 9, 2024", zz, fn, data, chi, thet2,
    u, skip, beps = 0.01, plotrange = {{0, 1}, {-Pi, Pi}, {0, Pi}}, 
   p1, p2, p3, p4},
  zz[r_, psi_, theta2_] := First[DataGeneric[1, 1, 0, r, psi, theta2]];
  fn[z_] := cords[tauSymmetry[rFullerPoincare[z]]];
  Echo[zz[0.1, 0.2, 0.5]];
  (* case *)
  {thet2, u} = {Pi - beps, zeta};
  Echo[{"case thet2=", thet2}];
  skip := 
   p1 = ParametricPlot3D[
     fn[zz[r0, psi0, thet2]], {r0, beps, 1 - beps}, {psi0, beps, 
      Pi - beps}, PlotRange -> plotrange, PlotStyle -> Blue];
  (* case *)
  {thet2, u} = {beps, zeta};
  Echo[{"case thet2=", thet2}];
  skip := 
   p2 = ParametricPlot3D[
     fn[zz[r0, psi0, thet2]], {r0, beps, 1 - beps}, {psi0, beps, 
      Pi - beps}, PlotRange -> plotrange, PlotStyle -> Blue];
  
  (* case *)
  {thet2, u} = {-beps, zeta};
  Echo[{"case thet2=", thet2}];
  p3 := ParametricPlot3D[
    fn[zz[r0, psi0, thet2]], {r0, beps, 1 - beps}, {psi0, beps, 
     Pi - beps}, PlotRange -> plotrange, PlotStyle -> Blue];
  
  (* case *)
  {thet2, u} = {-Pi + beps, zeta};
  Echo[{"case thet2=", thet2}];
  skip := 
   p4 = ParametricPlot3D[
     fn[zz[r0, psi0, thet2]], {r0, beps, 1 - beps}, {psi0, beps, 
      Pi - beps}, PlotRange -> plotrange, PlotStyle -> Blue];
  Show[{p3}]
 ];

(* Analysis of y2=0 cases *)

surfaceDiscAListPointPlot3D := 
  Module[{doc = 
     "y2=0 analysis, take image in 3D generic, very useful, march \
2024", data, chi, thet2, u, skip, beps = 0.01, 
    plotrange = {{0, 1}, {-Pi, Pi}, {0, Pi}}, p1, p2, p3, p3A, pl, 
    pl2, pl3, pb, tab, del},
   
   
   (* case *)
   {thet2, u} = {Pi, zeta};
   Echo[{"case A0 switch, thet2=", thet2}];
   data = DataY20[u, 1, 0, r, psi, thet2];
   chi = Apply[switchFn, data];
   EchoOff[(chi /. t -> 0) // Factor];
   EchoOff[(D[chi, {t, 2}] /. t -> 0) // Factor];
   EchoOff[D[chi, {t, 3}]];
   skip := 
    ContourPlot[Apply[switchTime, data], {r, 0, 1}, {psi, 0, Pi}, 
     ContourLabels -> True];
   p1 = ParametricPlot3D[
     cordTauFull[data /. {r -> r0, psi -> psi0}], {r0, beps, 
      1 - beps}, {psi, beps, Pi - beps}, PlotRange -> plotrange, 
     PlotStyle -> Blue];
   
   (* case *)
   {thet2, u} = {0, Conjugate[zeta]};
   Echo[{"case A0 switch, thet2=", thet2}];
   data = DataY20[u, 1, 0, r, psi, thet2];
   chi = Apply[switchFn, data];
   EchoOff[(chi /. t -> 0) // Factor];
   EchoOff[(D[chi, {t, 2}] /. t -> 0) // Factor];
   EchoOff[D[chi, {t, 3}]];
   Echo[ContourPlot[
     Apply[Disc, 
       DataY20[Conjugate[zeta], 1, 0, r, psi, thet2]] /. {r -> r0, 
       psi -> psi0}, {r0, beps, 1 - beps}, {psi0, beps, Pi - beps}, 
     ContourLabels -> True]];
   Echo[Apply[Disc, 
      DataY20[Conjugate[zeta], 1, 0, r, psi, thet2]] // Simplify];
   Echo["incomplete A0"]; 
   p2 = Echo[
     ParametricPlot3D[
      cordTauFull[data /. {r -> r0, psi -> psi0}], {r0, 0.7, 
       1 - beps}, {psi0, beps, Pi - beps}, PlotRange -> plotrange, 
      PlotStyle -> Red]];
   tab = Table[{RandomReal[{beps, 1 - beps}], 
      RandomReal[{beps, Pi - beps}]}, {i, 10000}];
   Echo[{"tab", tab[[3]]}];
   del[{r_, psi_}] := 
    Apply[Disc, DataY20[Conjugate[zeta], 1, 0, r, psi, thet2]];
   tab = Select[tab, del[#] > 0 &];
   Echo[{"length", Length[tab]}];
   pl = Echo[
     ListPointPlot3D[
      Map[cordTauFull[data /. {r -> #[[1]], psi -> #[[2]]}] &, tab], 
      PlotRange -> plotrange]];
   tab = Table[{RandomReal[{0.5, 0.7}], RandomReal[{1.5, 2.2}]}, {i, 
      10000}];
   Echo[{"tab", tab[[3]]}];
   tab = Select[tab, del[#] > 0 &];
   Echo[{"length", Length[tab]}];
   pl2 = Echo[
     ListPointPlot3D[
      Map[cordTauFull[data /. {r -> #[[1]], psi -> #[[2]]}] &, tab], 
      PlotRange -> plotrange]];
   tab = Table[{RandomReal[{beps, 0.5}], RandomReal[{0.7, 0.9}]}, {i, 
      10000}];
   Echo[{"tab", tab[[3]]}];
   tab = Select[tab, del[#] > 0 &];
   Echo[{"length", Length[tab]}];
   pl3 = Echo[
     ListPointPlot3D[
      Map[cordTauFull[data /. {r -> #[[1]], psi -> #[[2]]}] &, tab], 
      PlotRange -> plotrange]];
   pb = Echo[
     Show[{ParametricPlot3D[{cordTauFull[
          data /. {r -> 1 - beps, psi -> psi0}]}, {psi0, beps, Pi}, 
        PlotRange -> plotrange, PlotStyle -> {Blue}],
       ParametricPlot3D[{cordTauFull[
          data /. {r -> beps, psi -> psi0}]}, {psi0, beps, 0.85}, 
        PlotRange -> plotrange, PlotStyle -> {Yellow}],
       ParametricPlot3D[{cordTauFull[data /. {r -> r0, psi -> beps}], 
         cordTauFull[data /. {r -> r0, psi -> Pi - beps}]}, {r0, 0.1, 
         1 - beps}, PlotRange -> plotrange, 
        PlotStyle -> {Red, Orange}]}]];
   Echo["incomplete B2"];
   data = DataY20[u, Conjugate[u], 2, r, psi, thet2];
   skip := 
    p3 = ParametricPlot3D[
      cordTauFull[data /. {r -> r0, psi -> psi0}], {r0, beps, 0.55}, {psi0,
        1.5, 2.5}, PlotRange -> plotrange, PlotStyle -> Red];
   skip := Echo[Show[{p1, p3}]];
   skip := 
    p3A = ParametricPlot3D[
      cordTauFull[data /. {r -> r0, psi -> psi0}], {r0, beps, 0.55}, {psi0,
        1.5, 2.5}, PlotRange -> {{0, 0.5}, {0, 1}, {2.7, Pi}}, 
      PlotStyle -> Red];
   Echo[Show[{p2, pl, pl2, pl3, pb}]];
   skip := Echo[Show[{p3A, p1}]];
   skip := 
    Echo[Show[{p1, p2, pl, pl2, pl3, pb, p3, globalResultantSurface}]];
   
  ];

(* March 11, 2024 *)

test:=Module[{doc = "experimental digression: test of masking out unwanted region", p1, p2},
 p1 = ContourPlot[Sin[x] Sin[y], {x, 0, 10}, {y, 0, 10}];
 p2 = RegionPlot[
   x + y >= 5 && x + y <= 15, {x, 0, 10}, {y, 0, 
    10}, {PlotStyle -> Directive[LightGray], 
    PlotStyle -> Opacity[1.0]}];
 Show[{p1, p2}]];


(* Useful plot the switching functions, for given parameters *)

(*
chiA0B1Obsolete[r_, psi_, theta2_] := 
  Module[{z, u, dataA0, dataB1, chiA0, chiB1}, 
   z = DataZ[r, psi, theta2]; u = FirstControl[z]; 
   dataA0 = {z, u, 1, 0}; dataB1 = {z, u, Conjugate[u], 1}; 
   chiA0 = Apply[switchFn, dataA0]; chiB1 = Apply[switchFn, dataB1];
   {chiA0, chiB1}
   ];
 *)

chiA0B1U[r_, psi_, theta2_, u_] := 
  Module[{z, dataA0, dataB1, chiA0, chiB1}, 
   z = DataZ[r, psi, theta2];
   dataA0 = {z, u, 1, 0};
   dataB1 = {z, u, Conjugate[u], 1};
   chiA0 = Apply[switchFn, dataA0]; chiB1 = Apply[switchFn, dataB1];
   {chiA0, chiB1}];

chiA0B1[r_, psi_, theta2_] := 
	chiA0B1U[r, psi, theta2, FirstControl[DataZ[r, psi, theta2]]];

switchPlot[r_, psi_, theta2_] := 
  Module[{z, u, dataA0, dataB1, switchA0, switchB1}, 
   z = DataZ[r, psi, theta2];
   Echo[z];
   u = FirstControl[z];
   Echo[u];
   dataA0 = {z, u, 1, 0};
   dataB1 = {z, u, Conjugate[u], 1};
   switchA0 = Apply[switchFn, dataA0];
   switchB1 = Apply[switchFn, dataB1];
   Echo[{switchA0, Discriminant[switchA0, t], switchB1, 
     Discriminant[switchB1, t], "res", 
     Resultant[switchA0, switchB1, t]}];
   Echo[{"tswA0", Apply[switchTime, dataA0], "tswB1", 
     Apply[switchTime, dataB1]}];
   Echo[Plot[{switchA0, switchB1}, {t, -5, 5}]];];



test:={"test switchPlot",switchPlot[0.1, Pi/2, -0.1] }

Echo["F1300"];

(* LOAD TO HERE *)

(* Tested loading to here and main graphics, March 12, 2024 *)

(* Noteworthy Plots:

ListPlot: discontinuityListPlot[{2.92, Pi}, {0, 0.4}, 100] was discontinuityPlot
RegionPlot: sliceR04RegionPlot
hanging: beautifulHeightPlot was beautiful
switchPlot[0.1, Pi/2, -0.1] was plotSwitch

3D:
surfaceDiscAPlot3D was RegionPlotA
surfaceDiscAListPointPlot3D was testY20,surfaceY20Plot3D (includes ContourPlot in Y2=0 cell) (old and slow, replaced with surfaceDiscAPlot3D)
surfaceSZResultantPlot3D was test2DActiveSwitch, surfaceResultantPlot3D (includes boundary)
surfaceResultantPlot3D was test45 (almost identical to surfaceSZResultantPlot3D)

 *)





(* OLD STUFF, MOSTLY OBSOLETE *)

(*switchPlot[0.132,3.1,-0.01]
switchPlot[0.133,3.1,-0.01] *)

imageFn[r_, psi_, theta2_] := 
  Module[{data, z, u, dataA0, dataB1, tswA0, tswB1, tsw},
   z = DataZ[r, psi, theta2];
   u = FirstControl[z];
   dataA0 = {z, u, 1, 0};
   dataB1 = {z, u, Conjugate[u], 1};
   tswA0 = Apply[switchTime, dataA0];
   tswB1 = Apply[switchTime, dataB1];
   tsw = Min[Select[{tswA0, tswB1}, # > 0 &]];
   cords[rotateFuller[solveCubicODE[u, z] /. {t -> tsw}]]];

{"test imageFn",
 imageFn[0.132829912650515, 3.1, -0.01],
 imageFn[0.132829912650516, 3.1, -0.01]};

(* Feb 2024 stuff. Mostly superseded. *)

deltaAm[r_, psi_, theta2_] := 
  Apply[Disc, DataY20[Conjugate[zeta], 1, 0, r, psi, theta2]];

negdelta := RegionPlot[deltaAm[r, psi, 0] < 0, {r, 0, 1}, {psi, 0, Pi}]

(*Exclusions\[Rule]{deltaAm[r,psi,0]\[GreaterEqual]-0.01},\
ExclusionsStyle\[Rule]Red;*)

Echo["F1400"];
(* to do, rewrite these *)

contourA0 := 
  Module[{doc = "y0=0, switch time level sets for time A,Pi case ", 
    data, chi,thet2=Pi},
   data = DataY20[zeta, 1, 0, r, psi, thet2];
   chi = Apply[switchFn, data];
   EchoOff[(chi /. t -> 0) // Factor];
   EchoOff[(D[chi, {t, 2}] /. t -> 0) // Factor];
   EchoOff[D[chi, {t, 3}]];
   ContourPlot[Apply[switchTime, data], {r, 0, 1}, {psi, 0, Pi}, 
	       ContourLabels -> True]];

contourB2 := 
  Module[{doc = "y2=0, switch time level sets for time B", data, 
    tswB2,level=2,theta2=0},
   data = DataY20[Conjugate[zeta], zeta, level, r, psi, theta2]; 
   tswB2 = t /. First[Solve[Apply[switchFn, data] == 0, t]];
   ContourPlot[tswB2, {r, 0, 1}, {psi, 0, Pi},
	       (*	       RegionFunction->Function[{r,psi},deltaAm[r,psi,theta2]<0], *)
	       ContourLabels -> True]];
contourAm := 
  Module[{doc = "y0=0, switch time level sets for time A,0 case ", 
    data, chi,thet2=0},
   data = DataY20[Conjugate[zeta], 1, 0, r, psi, thet2];
   ContourPlot[Apply[switchTime, data], {r, 0, 1}, {psi, 0, Pi}, 
    ContourLabels -> True]];

contourDeltaAm := Module[{data,thet2=0},
   data = DataY20[Conjugate[zeta], 1, 0, r, psi, thet2];
   ContourPlot[Apply[Disc, data], {r, 0, 1}, {psi, 0, Pi}, 
    ContourLabels -> True]
		  ];
show := Show[{contourB2,negdelta}]



Echo["F1400"];

(* February Chaff, work in progress *)

plot[fn_, color_] := 
  Module[{eps = 0.001, plotrange, plotrangeopt}, 
   plotrange = {{0, 1}, {-Pi, Pi}, {0, Pi}};
   plotrangeopt = {{0, 0.3}, {0, 1}, {2.5, Pi}};
   ParametricPlot3D[
    fn[r, psi], {r, eps, 1 - eps}, {psi, eps, Pi - eps}, 
    PlotRange -> plotrange, PlotStyle -> {color}]];

test := Module[{doc="image y2=0 in generic",fnA0, plotA0, fnB2, plotB2, fnAm, plotAm, show}, 
   fnA0[r_, psi_] := 
    Module[{doc2 = "map y0=0 into generic, using chiA0"}, 
     cordTauFull[DataY20[zeta, 1, 0, r, psi, Pi]]];
   fnB2[r_, psi_] := 
    Module[{doc2 = "map y0=0 into generic, using chiB2"}, 
     cordTauFull[DataY20[Conjugate[zeta], zeta, 2, r, psi, 0]]];
   fnAm[r_, psi_] := 
    Module[{doc2 = "map y0=0 into generic, using chiA0"}, 
     cordTauFull[DataY20[Conjugate[zeta], 1, 0, r, psi, 0]]];
   plotA0 = plot[fnA0, Red];
   plotB2 = plot[fnB2, Blue];
   plotAm = plot[fnAm, Yellow];
   show = Echo[Show[{plotA0}]];
   fnA0[0.2, 0.2]];

test := Module[{doc = 
    "multiplicity discontinuity, interesting transition range theta2 \
in [0.89,0.92]", r = 0.1, theta2 = 0.92, dataA0, dataB1, tswA0, tswB1,
    swA0}, dataA0 = DataGeneric[zeta, 1, 0, r, psi, theta2];
  dataB1 = DataGeneric[zeta, zeta2, 1, r, psi, theta2];
  tswA0 = Apply[switchTime, dataA0 /. psi -> 0.6];
  tswB1 = Apply[switchTime, dataB1];
  EchoOff[Apply[switchTime, dataA0 /. psi -> 0.1]];
  swA0 = Echo[Apply[switchFn, dataA0]];
  Echo[Plot[swA0 /. psi -> 2., {t, -5, 5}]];
  Echo[Plot[{Apply[switchTime, dataA0 /. psi -> psi0], 
     Apply[switchTime, dataB1 /. psi -> psi0]}, {psi0, 2, Pi}, 
    PlotRange -> All, Exclusions -> "Discontinuities", 
    ExclusionsStyle -> Red]];
  Echo[t /. NSolve[(swA0 /. psi -> 3.13) == 0, Reals]];
  EchoOff[
   Plot[Min[{t} /. NSolve[(swA0 /. psi -> psi0) == 0, Reals]], {psi0, 
     3.13, Pi}, PlotRange -> All]];
  Echo[NSolve[Discriminant[swA0, t] == 0, psi]];
  Plot[Discriminant[swA0, t] /. psi -> psi0, {psi0, 2., Pi}, 
   PlotRange -> All]]

(* February chaff, continued *)

(* March 9, 2024 *)

doubleDisc[u_] := 
 Module[{doc = "experimental, too complicated to help, march 9, 2024, discriminant in t, secondary discriminant in r",
    dataA0, discA0, disc2},
  dataA0 = DataGeneric[u, 1, 0, r, psi0, theta2];
  discA0 = Apply[Disc, dataA0];
  disc2 = Discriminant[discA0, r]; 
  (* NSolve[disc2\[Equal]0,theta2] *)
  Collect[discA0/r, r];
  disc2
 ];

(* dDisc = doubleDisc[Conjugate[zeta]]; *)

(* Plot[(dDisc /. psi0 -> Pi/2), {theta2, -0.26, -0.24}] *)

Echo["F1500"];

(* END OF JUNK MATERIAL *)


(* March 23 Boundary Analysis *)


test:=Module[{doc = "boundary analysis", u, data, chiA0, chiB1, tswB1s, 
  tswB1},
 doc = "C3(zeta2)";
 u = Conjugate[zeta];
 data = DataZ[r, theta2 - theta1, theta2];
 chiA0 = switchFn[data, u, 1, 0];
 chiB1 = Echo[switchFn[data, u, Conjugate[u], 1]];
 tswB1s = t /. Solve[chiB1 == 0, t];
 Echo[Series[Discriminant[chiB1, t], {r, 0, 1}]];
 Echo[Simplify[Normal[Series[tswB1s, {r, 0, 1}]], Sin[theta1] < 0]]];

AnalysisZinFixedPoint:=Module[{doc = "zin is extremely near the separating surfaces DeltaA0=0,etc.\
 There are several nearby events.\
 At r0 = 0.267756... DeltaB1=0.\
 At r0 = 0.267905... DeltaA0=0.\
 At r0 = 0.267948... DeltaA0=0 again.\
 At r0 = 0.267949... Value of zin fixed point.
 At fixed point DeltaA0<0, DeltaB1<0, resAB >0.", chiAin, zin, rin, psin,
    thetain, z, discin, num, dA,surpriseroot},
  zin = {z10in, z20in, z30in};
  chiAin = (chiA /. {e -> 1, x1 -> zoutExact[[1, 1]], 
        y1 -> zoutExact[[1, 2]], x2 -> zoutExact[[2, 1]], 
        y2 -> zoutExact[[2, 2]], x3 -> zoutExact[[3, 1]]}) // 
     ComplexExpand // Simplify;
  Echo[rphiFullerPoincare[FullerPoincare[zin]] - zin // Chop];
  {rin, psin, thetain} = Echo[cords[{z10in, z20in, z30in}]];
  z = DataZ[r, psin, thetain];
  chiAin = Apply[switchFn, {z, zeta, 1, 0}];
  dA = Discriminant[chiAin, t];
  surpriseroot=Echo[NSolve[dA == 0 && r > 0 && r < 1, r, Reals]];
  Echo[Discontinuity[psin, thetain]];
  switchPlot[0.267949, psin, thetain]];

Echo["F1550"];



faceAnalysis9003854ContourPlotRevised := 
  Module[{doc = "nearly along face. Analysis of 3D cubes.", f, 
    eps = 0.001, fixed, skip, fn}, f = switchTimeFirst3;
   fixed = 10^-6;
   Echo[{doc = 
      "Case[psi=0]:tends to zero near theta2=0 edge and near (r=1 and \
theta2<=Pi/3), theta2>=Pi/3:", 
     ContourPlot[
      f[r, 0, theta2], {r, eps, 1 - eps}, {theta2, Pi/3 + eps, 
       Pi - eps}, PlotLegends -> Automatic], doc = "theta2<=Pi/3:", 
     ContourPlot[
      f[r, fixed, theta2], {r, eps, 1 - eps}, {theta2, eps, 
       Pi/3 - eps}, PlotLegends -> Automatic],
     "along theta2=Pi/3:", 
     Plot[f[r, fixed, Pi/3 - fixed], {r, eps, 1 - eps}, 
      PlotRange -> Automatic], "forward map", 
     forward3[0.5, fixed, 0.5] - {0.5, fixed, 0.5}}];
   skip := {doc = 
      "Case[psi=Pi]:tends 0, near r=0 and near theta2=0, and near \
(r=1,theta2<=Pi/3)", doc = "theta2>=Pi/3",
     ContourPlot[
      f[r, Pi - fixed, theta2], {r, eps, 1 - eps}, {theta2, 
       Pi/3 + eps, Pi - eps}, PlotLegends -> Automatic],
     doc = "theta2<=Pi/3:",
     ContourPlot[
      f[r, Pi - fixed, theta2], {r, eps, 1 - eps}, {theta2, eps, 
       Pi/3 - eps}, PlotLegends -> Automatic], doc = "Zoom", 
     ContourPlot[
      f[r, Pi - fixed, theta2], {r, 0.8, 1 - eps}, {theta2, eps, 
       Pi/3 - eps}, PlotLegends -> Automatic], doc = "Zoom", 
     ContourPlot[
      f[r, Pi - fixed, theta2], {r, eps, 0.2}, {theta2, eps, 
       Pi - eps}, PlotLegends -> Automatic], doc = "Zoom", 
     ContourPlot[
      f[r, Pi - fixed, theta2], {r, eps, 1 - eps}, {theta2, eps, 
       0.02}, PlotLegends -> Automatic], 
     "forward map theta2+= 2Pi/3:", 
     forward3[0.5, Pi - fixed, 0.5] - {0.5, Pi - fixed, 0.5}};
   skip := {doc = 
      "Case[theta2=0]: seems to go to 0 everywhere pointwise, but not \
uniformly on edges", 
     ContourPlot[
      f[r, psi, fixed], {r, eps, 1 - eps}, {psi, eps, Pi - eps}, 
      PlotLegends -> Automatic], "forward map negates theta2", 
     forward3[0.5, 1.5, fixed] - {0.5, 1.5, 0}};
   skip := 
    Echo[{doc = 
       "Case[theta2=Pi]:0 only at corner (r,psi)=(0,Pi). Equals y2=0 \
2D piece, u=zeta", eps = 0.0001, 
      ContourPlot[
       f[r, psi, Pi - fixed], {r, eps, 1 - eps}, {psi, eps, Pi - eps},
        PlotLegends -> Automatic], "Zoom",
      ContourPlot[
       f[r, psi, Pi - fixed], {r, eps, 0.001}, {psi, 2, Pi - eps}, 
       PlotLegends -> Automatic],
      Plot[f[fixed, psi, Pi - fixed], {psi, 2 Pi/3 + eps, Pi - eps}], 
      "near psi=Pi:",
      Plot[f[r, Pi - fixed, Pi - fixed], {r, eps, 1 - eps}]}];
   skip := 
    Echo[{doc = "Case[r=0]:seems to depend only on theta2-psi=theta1",
       Echo[ContourPlot[
        f[fixed, psi, theta2], {psi, eps, Pi - eps}, {theta2, eps, 
         Pi - eps}, PlotLegends -> Automatic]], 
      Plot[f[fixed, Pi/2 - theta1/2, 
        Pi/2 + theta1/2], {theta1, -Pi + eps, Pi - eps}], "zoom",
      Plot[
       f[fixed, Pi/2 - theta1/2, Pi/2 + theta1/2], {theta1, 0, 
        Pi/3 - eps}]}];
   skip := 
    Echo[{doc = 
       "Case[r=1]:Along theta2=Pi/2, Piecewise behavior, zero when \
(theta2<=psi) theta1<=0, positive when theta1>0.",
      doc = "seems to depend only on theta2", fixed = 0.00001, 
      ContourPlot[
       f[1 - fixed, psi, theta2], {psi, eps, Pi - eps}, {theta2, eps, 
        Pi - eps}, PlotLegends -> Automatic],
      doc = 
       "Along psi=Pi/2. Piecewise behavior. Zero when theta2<=Pi/3, \
positive when theta2>Pi/3", 
      Plot[f[1 - fixed, Pi/2, theta2], {theta2, eps, Pi - eps}]}];
   doc = "how does the mapping behave near t=0";
   fn = forward3;
   skip := {doc = 
      "fn shifts boundary r=1,theta2[0,Pi/3] maps to \
theta2[2Pi/3,Pi]", 
     Echo[ParametricPlot3D[
       fn[1 - fixed, psi, theta2], {psi, eps, Pi - eps}, {theta2, eps,
         Pi/3 - eps}, PlotRange -> {{0, 1}, {0, Pi}, {-Pi, Pi}}]]};
   skip := {doc = 
      "fn shifts boundary theta2=0+, maps to 3 sides of a box", 
     fixed = 0.01, eps = 0.01, 
     Echo[ParametricPlot3D[
       fn[r, psi, fixed], {r, eps, 1 - eps}, {psi, eps, Pi - eps}, 
       PlotRange -> {{0, 1}, {0, Pi}, {-Pi, Pi}}]]};
   doc = "look at how theta2=0+ is mapped";
   skip := 
    Module[{p1, p2, p3}, 
     p1 = ParametricPlot3D[
       fn[r, psi, fixed], {r, eps, 1 - eps}, {psi, eps, Pi/3 - eps}, 
       PlotRange -> {{0, 1}, {0, Pi}, {-Pi, Pi}}, PlotStyle -> Red];
     p2 = 
      ParametricPlot3D[
       fn[r, psi, fixed], {r, eps, 1 - eps}, {psi, Pi/3 + eps, 
        2 Pi/3 - eps}, PlotRange -> {{0, 1}, {0, Pi}, {-Pi, Pi}}, 
       PlotStyle -> Yellow];
     p3 = 
      ParametricPlot3D[
       fn[r, psi, fixed], {r, eps, 1 - eps}, {psi, 2 Pi/3 + eps, 
        Pi - eps}, PlotRange -> {{0, 1}, {0, Pi}, {-Pi, Pi}}, 
       PlotStyle -> Blue];
     Echo[Show[{p1, p2, p3}]];
     p1 = 
      ParametricPlot3D[{r, psi, fixed}, {r, eps, 1 - eps}, {psi, eps, 
        Pi/3 - eps}, PlotRange -> {{0, 1}, {0, Pi}, {-Pi, Pi}}, 
       PlotStyle -> Red];
     p2 = 
      ParametricPlot3D[{r, psi, fixed}, {r, eps, 1 - eps}, {psi, 
        Pi/3 + eps, 2 Pi/3 - eps}, 
       PlotRange -> {{0, 1}, {0, Pi}, {-Pi, Pi}}, PlotStyle -> Yellow];
     p3 = 
      ParametricPlot3D[{r, psi, fixed}, {r, eps, 1 - eps}, {psi, 
        2 Pi/3 + eps, Pi - eps}, 
       PlotRange -> {{0, 1}, {0, Pi}, {-Pi, Pi}}, PlotStyle -> Blue];
     Echo[Show[{p1, p2, p3}]];];
   skip := 
    Echo[{fn[0.5, 0.2, fixed], fn[0.5, Pi/2, fixed], 
      fn[0.5, 3, fixed]}];
   skip := {doc = "look at how r=0+, psi>= theta2 is mapped", 
     fixed = 0.001, eps = 0.001, 
     Echo[ParametricPlot3D[
       fn[fixed, psi, theta2], {theta2, eps, Pi - eps}, {psi, 
        theta2 + eps, Pi - eps}, 
       PlotRange -> {{0, 1}, {0, Pi}, {-Pi, Pi}}, 
       PlotStyle -> Blue]]};];


Echo["F1600"];


(* Added April 12, 2024 *)

forward3[r_, psi_, theta2_] := 
  Module[{doc = "forward map in local coordinates assuming theta2!=0",
     z0, u}, z0 = DataZ[r, psi, theta2];
   u = If[theta2 > 0, zeta, Conjugate[zeta]];
   cords[rotateFuller[FullerPoincareU[z0, u]]]];

backward3[r_, psi_, theta2_] := 
  Module[{doc = "backward map, assuming theta2!=0", z0, u},
   z0 = tauSymmetry[DataZ[r, psi, theta2]];
   u = If[theta2 > 0, zeta, Conjugate[zeta]];
   cords[tauSymmetry[rotateFuller[FullerPoincareU[z0, u]]]]
  ];

textNearBoundary:=Module[{doc = "near boundary tsw=0 MCA:3962148"},
 forward3[0.5, 1.5, 10^-4] // Echo;
 forward3[0.5, 1.5, -Pi + 10^-4] // Echo;
 forward3[0.5, 10^-4, 0.6] - {0, 0, 2 Pi/3} // Echo;
 forward3[0.5, Pi - 10^-4, 0.6] - {0, 0, 2 Pi/3} // Echo;
 forward3[0.5, 10^-4, -0.6] + {0, 0, 2 Pi/3} // Echo;
 forward3[0.5, Pi - 10^-4, -0.6] + {0, 0, 2 Pi/3} // Echo;
 ]

tau3[r_, psi_, theta2_] := 
  {r, Pi - psi, If[theta2 >= 0, Pi - theta2, -Pi - theta2]};
iforward3[r_, psi_, theta2_] := Apply[tau3, forward3[r, psi, theta2]];

switchTimeFirst3[r_, psi_, theta2_] :=
  Module[{chiA0, chiB1},
   {chiA0, chiB1} = chiA0B1[r, psi, theta2];
   switchTimeFirst[chiA0, chiB1]];


curveNearBoundary:=
	Module[{doc = "take curves approaching boundary of cube", skip, psi, 
   chiA, chiB, s},
  skip := Module[{},
    {chiA, chiB} = 
     chiA0B1U[1/2, psi, Pi/3 - 10^-8, zeta] // Chop // Echo;
    Series[
      t /. NSolve[(chiA /. psi -> 10^-50) == 0, t, 
        WorkingPrecision -> 100], {psi, 0, 1}] // Echo;
    Series[
     N[t /. Solve[Normal[Series[chiA, {psi, 0, 1}]] == 0, t], 
      100], {psi, 0, 1}]];
  skip := Module[{},
    {chiA, chiB} = chiA0B1U[s, s, Pi/6, zeta];
    t /. NSolve[(chiA /. s -> 10^-50) == 0, t, 
       WorkingPrecision -> 100] // Echo;
    ];
  skip := Module[{},
    {chiA, chiB} = chiA0B1U[s, 5 Pi/6, Pi, zeta] // Chop // Echo;
    t /. NSolve[(chiA /. s -> 10^-6) == 0, t, 
       WorkingPrecision -> 100] // Echo;
	  ]];

SwitchTime7514654ContourPlot := 
 Module[{doc = 
    "nearly along face. Analysis of 3D cubes. First control zeta^2",
   eps = 0.0001, fixed = 0.0001, skip, f, forward},
  f = switchTimeFirst3;
  skip := {doc = "psi small",
    ContourPlot[
     f[r, fixed, theta2], {r, eps, 
      1 - eps}, {theta2, -Pi/3 + eps, -eps}, PlotLegends -> Automatic],
    doc = "theta2 zoom",
    ContourPlot[
     f[r, fixed, theta2], {r, eps, 1 - eps}, {theta2, -0.1, -eps}, 
     PlotLegends -> Automatic],
    doc = "r[1] zoom",
    ContourPlot[
     f[r, fixed, theta2], {r, 0.99, 
      1 - eps}, {theta2, -Pi/3 + eps, -eps}, 
     PlotLegends -> Automatic]};
  skip := {doc = "psi near Pi",
    ContourPlot[
     f[r, Pi - fixed, theta2], {r, eps, 
      1 - eps}, {theta2, -Pi/3 + eps, -eps}, 
     PlotLegends -> Automatic]};
  skip := {doc = "theta2 near 0",
    ContourPlot[
     f[r, psi, -fixed], {r, eps, 1 - eps}, {psi, eps, Pi - eps}, 
     PlotLegends -> Automatic],
    doc = "psi[0] Zoom", 
    ContourPlot[f[r, psi, -fixed], {r, eps, 1 - eps}, {psi, eps, 0.5},
      PlotLegends -> Automatic],
    doc = "r[1] Zoom",
    ContourPlot[
     f[r, psi, -fixed], {r, 0.99, 1 - eps}, {psi, eps, Pi - eps}, 
     PlotLegends -> Automatic],
    doc = "psi[Pi] Zoom", 
    ContourPlot[
     f[r, psi, -fixed], {r, eps, 1 - eps}, {psi, Pi - 0.01, Pi - eps},
      PlotLegends -> Automatic]};
  skip := {doc = "r near 0",
    ContourPlot[
     f[fixed, psi, theta2], {psi, eps, 
      Pi - eps}, {theta2, -Pi + eps, -eps}, 
     PlotLegends -> Automatic],
    "along diag",
    fixed = 10^-6,
    Plot[f[fixed, psi, -psi], {psi, eps, Pi}, PlotRange -> {0, Pi}],
    Plot[f[fixed, psi, -psi], {psi, eps, 0.52}, 
     PlotRange -> Automatic],
    Plot[f[fixed, psi, -psi], {psi, 1.5, Pi - eps}, 
     PlotRange -> Automatic],
    Echo[f[fixed, 3, -3]]
    };
  skip := {doc = "r near 1", fixed = 10^-6, 
    ContourPlot[
     f[1 - fixed, psi, theta2], {psi, eps, 
      Pi - eps}, {theta2, -Pi + eps, -eps}, 
     PlotLegends -> Automatic],
    "along psi fixed",
    Plot[f[1 - fixed, Pi/2, theta2], {theta2, -Pi + eps, -eps}, 
     PlotRange -> Automatic]};
  skip := {doc = "theta2 near -Pi", fixed = 10^-6,
    ContourPlot[
     f[r, psi, -Pi + eps], {r, eps, 1 - eps}, {psi, eps, Pi - eps}, 
     PlotLegends -> Automatic]};
  skip := {doc = "psi=0, lower theta2, nonzero except theta2[-Pi]",
    ContourPlot[
     f[r, 0, theta2], {r, eps, 
      1 - eps}, {theta2, -Pi + eps, -Pi/3 - eps}, 
     PlotLegends -> Automatic]};
  skip := {doc = "psi=Pi, lower theta2",
    ContourPlot[
     f[r, Pi, theta2], {r, eps, 
      1 - eps}, {theta2, -Pi + eps, -Pi/3 - eps}, 
     PlotLegends -> Automatic]}; 
  skip := forward3[0.1, 3.0, -Pi + fixed];
  skip := forward3[0.5, fixed, -0.5] + {0, 0, 2 Pi/3};
  forward3[0.5, Pi - fixed, -0.5] + {0, 0, 2 Pi/3}
 ];

boundaryMapping := Module[{MCA="MCA:9003854",doc="analysis of boundaries between parts",r, psi, theta2},
  {"fixed point zout", cords[{z10out, z20out, z30out}]} // Echo;
  {"fixed point zin", {r, psi, theta2} = 
     cords[{z10in, z20in, z30in}]} // Echo;
  {"disc in, zin is barely above the pod", 
    Discontinuity[psi, theta2]} // Echo;
  {"P1 resultant region", {2.9, 0.1}} // Echo;
  Discontinuity[2.9, 0.1] // FullForm // Echo;
  {{r, psi, theta2} = forward3[0.00001, 2.9, 0.1], "Ftheta1", 
    psi - theta2} // Echo;
  {"rAB-", "Fpsi=Pi-, Ftheta2-negated", forward3[0.34022, 2.9, 0.1]} //
    Echo;
  {"rAB+", "Fpsi=Pi-, Ftheta2+= 2Pi/3", forward3[0.34023, 2.9, 0.1]} //
    Echo;
  {"P2, column over pod", {3.0, 0.2}} // Echo;
  Discontinuity[3.0, 0.2] // FullForm // Echo;
  {"r=0+", {r, psi, theta2} = forward3[0.001, 3.0, 0.2], "Ftheta1", 
    psi - theta2} // Echo;
  {"dB-", 
    "Ftheta2= -Pi", {r, psi, theta2} = 
     forward3[0.24285, 3.0, 0.2], {Pi - psi, -Pi - theta2}, 
    Discontinuity[Pi - psi, -Pi - theta2]} // Echo;
  {"dB+", 
    "F near zout", {r, psi, theta2} = forward3[0.242856, 3.0, 0.2], 
    "r-lands to tau-dA-discontinuity", 
    Discontinuity[Pi - psi, Pi - theta2]} // Echo;
  {"dA-", 
    "F near zout", {r, psi, theta2} = forward3[0.256333, 3.0, 0.2], 
    "Fr on tau-dB-discontinuity", 
    Discontinuity[Pi - psi, Pi - theta2]} // Echo;
  {"dA+", "Ftheta2 0+", forward3[0.2563339, 3.0, 0.2]} // Echo;
  {"P3, dA region", {3.1, 0.3}} // Echo;
  Discontinuity[3.1, 0.3] // FullForm // Echo;
  {"r=0+", "Fr=0+", {r, psi, theta2} = forward3[0.001, 3.1, 0.3], 
    "Ftheta1", psi - theta2} // Echo;
  {"r=dA-", {r, psi, theta2} = forward3[0.140989615, 3.1, 0.3],
    "r lands on tau-discontinuity", 
    Discontinuity[Pi - psi, -Pi - theta2]} // Echo;
  {"r=dA+", "Fr=0+", forward3[0.14098961512, 3.1, 0.3]} // Echo;
  {"P4", {2.5, -0.5}} // Echo;
  Discontinuity[2.5, -0.5] // FullForm // Echo;
  {"left face", forward3[0.001, 2.5, -0.5]} // Echo;
  {"inner cone dA-", {r, psi, theta2} = forward3[0.748126, 2.5, -0.5],
     "F to tau-dA-discontinuity", {Pi - psi, Pi - theta2}, 
    Discontinuity[Pi - psi, Pi - theta2]} // Echo;
  {"outer cone dA+", 
    "Ftheta2=-Pi", {r, psi, theta2} = 
     forward3[0.7481261, 2.5, -0.5], {Pi - psi, -Pi - theta2}, 
    Discontinuity[Pi - psi, -Pi - theta2]} // Echo;
		   ];

test:=
	Module[{r, psi, theta2, f, p1, p2, p3, q1, q2, q3, tout},
 {psi, theta2} = {3, 0.2};
 tout = cords[{z10out, z20out, z30out}];
 f[r_] := {r, forward3[r, psi, theta2]};
 Echo[{f[0.242], f[0.243], f[0.255], f[0.257]}];
 
 p1 = ParametricPlot3D[Last[f[r]], {r, 0.001, 0.242}, 
   PlotStyle -> LightBlue, 
   PlotRange -> {{0, 1}, {0, Pi}, {-Pi, Pi}}];
 p2 = ParametricPlot3D[Last[f[r]], {r, 0.243, 0.256}, 
   PlotStyle -> Blue];
 p3 = ParametricPlot3D[Last[f[r]], {r, 0.257, 0.99}, 
   PlotStyle -> Black];
 {psi, theta2} = {3.1, 0.1};
 q1 = ParametricPlot3D[Last[f[r]], {r, 0.001, 0.11}, 
   PlotRange -> {{0, 1}, {0, Pi}, {-Pi, Pi}}, PlotStyle -> Red];
 q2 = ParametricPlot3D[Last[f[r]], {r, 0.117, 0.126}, 
   PlotStyle -> {Red, Thick}];
 q3 = ParametricPlot3D[Last[f[r]], {r, 0.127, 0.99}, PlotStyle -> Red];
 Echo[f[0.12]];
 Show[{p1, p2, p3, q1, q2, q3, 
       ListPointPlot3D[{tout}, PlotStyle -> Orange]}]];

test:= Module[{r, psi, theta2},
 {r, psi, theta2} = cords[{z10out, z20out, z30out}];
 Discontinuity[psi, theta2] // Echo;
 {{r, psi, theta2}, forward3[r, psi, theta2]}];

newBasinHeightContour3D := 
 Module[{doc = "new Basin Height contour", eps = 10^-3, f, time, p, 
   pl, r, psi, theta2},
  f[r_?NumericQ, psi_?NumericQ, theta2_?NumericQ] := 
   newBasinHeight[DataZ[r, psi, theta2]];
  {time, p} = 
   Timing[ContourPlot3D[
     f[r, psi, theta2], {r, eps, 1 - eps}, {psi, eps, 
      Pi - eps}, {theta2, -Pi + eps, Pi - eps}, Contours -> 5, 
     MaxRecursion -> 0, PlotPoints -> 15, PlotLegends -> Automatic, 
     PlotLabel -> "newBasinHeight"]];
  {r, psi, theta2} = cords[{z10out, z20out, z30out}];
  pl = ListPointPlot3D[{{r, psi, theta2}, {r, Pi - psi, Pi - theta2}},
     PlotStyle -> {Red, Thick}];
  Echo[time];
  Echo[Show[{p, pl}]];
  {time, p} = 
   Timing[ContourPlot3D[
     f[r, psi, theta2], {r, eps, 0.4}, {psi, eps, Pi/3}, {theta2, 
      2 Pi/3, Pi - eps}, Contours -> 5, MaxRecursion -> 0, 
     PlotPoints -> 15, PlotLegends -> Automatic, 
     PlotLabel -> "newBasinHeight"]];
  {r, psi, theta2} = cords[{z10out, z20out, z30out}];
  pl = ListPointPlot3D[{{r, psi, theta2}, {r, Pi - psi, Pi - theta2}},
     PlotStyle -> {Red, Thick}];
  Echo[time];
  Echo[Show[{p, pl}]]
 ];

rectangleMap[{{rmin_, rmax_}, {psimin_, psimax_}, {theta2min_, 
     theta2max_}}] := 
  Module[{doc = "mappings of cubes", Frmin, Frmax, Fpsimin, Fpsimax, 
    Ftheta2min, Ftheta2max},
   Frmin = 
    ParametricPlot3D[
     forward3[rmin, psi, theta2], {psi, psimin, psimax}, {theta2, 
      theta2min, theta2max}];
   Frmax = 
    ParametricPlot3D[
     forward3[rmin, psi, theta2], {psi, psimin, psimax}, {theta2, 
      theta2min, theta2max}];
   Fpsimin = 
    ParametricPlot3D[
     forward3[r, psimin, theta2], {r, rmin, rmax}, {theta2, theta2min,
       theta2max}];
   Fpsimax = 
    ParametricPlot3D[
     forward3[r, psimax, theta2], {r, rmin, rmax}, {theta2, theta2min,
       theta2max}];
   Ftheta2min = 
    ParametricPlot3D[
     forward3[r, psi, theta2min], {r, rmin, rmax}, {psi, psimin, 
      psimax}];
   Ftheta2max = 
    ParametricPlot3D[
     forward3[r, psi, theta2max], {r, rmin, rmax}, {psi, psimin, 
      psimax}];
   Show[{Frmin, Frmax, Fpsimin, Fpsimax, Ftheta2min, Ftheta2max}, 
    PlotRange -> {{0, 1}, {0, Pi}, {-Pi, Pi}}]
   ];
fastrectangleMap[rr_] := 
  Module[{tab0, tab, tabA, tabB, mesh0, meshA, meshB, r, psi, theta2, 
    pl},
   tab0 = 
    Flatten[Table[{rr[[1, i]], rr[[2, j]], rr[[3, k]]}, {i, 1, 2}, {j,
        1, 2}, {k, 1, 2}], 2];
   tab = Flatten[
     Table[forward3[rr[[1, i]], rr[[2, j]], rr[[3, k]]], {i, 1, 
       2}, {j, 1, 2}, {k, 1, 2}], 2];
   mesh0 = ConvexHullMesh[tab0];
   tabA = Select[tab, #[[3]] >= 0 &];
   tabB = Select[tab, #[[3]] <= 0 &];
   meshA = If[Length[tabA] > 0, ConvexHullMesh[tabA], {}];
   meshB = If[Length[tabB] > 0, ConvexHullMesh[tabB], {}];
   {r, psi, theta2} = cords[{z10out, z20out, z30out}];
   pl = ListPointPlot3D[{{r, psi, theta2}, {r, Pi - psi, 
       Pi - theta2}}, PlotStyle -> {Red, Thick}];
   Show[{Graphics3D[{Yellow, mesh0, Blue, meshA, meshB}, 
      PlotRange -> {{0, 1}, {0, Pi}, {-Pi, Pi}}, Axes -> Automatic], 
	 pl}]];

Echo["1900"];

frm := Module[{r, r2, w = 0.2, eps = 10^-3},
   r = {RandomReal[{eps, 1 - w - eps}], 
     RandomReal[{eps, Pi - w - eps}], 
     RandomReal[{-Pi + eps, Pi - w - eps}]};
   r2 = Transpose[{r, r + {w, w, w}}];
   fastrectangleMap[r2]];
skip := Show[Table[frm, {10}]]
skip := Module[{r, r2, w = 0.2, z},
   r = cords[{z10in, z20in, z30in}];
   r2 = Transpose[{r - {w, w, w}/2, r + {w, w, w}/2}];
   fastrectangleMap[r2]];

zeroswitch1556775Plot3D := 
 Module[{doc = "zero switching time faces, included in paper", 
   eps = 0.01, p1, p2, p3, p4, p5, p6, op = 0.3, d1, d2},
  p1 = ParametricPlot3D[{{r, 0, theta2}}, {r, 0, 1}, {theta2, 0, 
     Pi/3}, PlotRange -> {{-eps, 1 + eps}, {-eps, Pi + eps}, {-eps, 
       Pi + eps}}, PlotStyle -> {Red, Opacity[op]}];
  p2 = ParametricPlot3D[{{r, Pi, theta2}}, {r, 0, 1}, {theta2, 0, 
     Pi/3}, PlotRange -> {{-eps, 1 + eps}, {-eps, Pi + eps}, {-eps, 
       Pi + eps}}, PlotStyle -> {Red, Opacity[op]}];
  p3 = ParametricPlot3D[{{1, psi, theta2}}, {psi, 0, Pi}, {theta2, 0, 
     Pi/3}, PlotRange -> {{-eps, 1 + eps}, {-eps, Pi + eps}, {-eps, 
       Pi + eps}}, PlotStyle -> {Red, Opacity[op]}];
  p4 = ParametricPlot3D[{{r, psi, 0}}, {r, 0, 1}, {psi, 0, Pi}, 
    PlotRange -> {{-eps, 1 + eps}, {-eps, Pi + eps}, {-eps, 
       Pi + eps}}, PlotStyle -> {Red, Opacity[op]}];
  p5 = ParametricPlot3D[{{0, psi, theta2}}, {psi, 0, Pi}, {theta2, 0, 
     Min[Pi, psi + Pi/3]}, 
    PlotRange -> {{-eps, 1 + eps}, {-eps, Pi + eps}, {-eps, 
       Pi + eps}}, PlotStyle -> {Red, Opacity[op]}];
  d1 = Show[{p1, p2, p3, p4, p5}];
  p1 = ParametricPlot3D[{{r, 0, theta2}}, {r, 0, 1}, {theta2, -Pi/3, 
     0}, PlotRange -> {{-eps, 1 + eps}, {-eps, Pi + eps}, {-eps - Pi, 
       0 + eps}}, PlotStyle -> {Red, Opacity[op]}];
  p2 = ParametricPlot3D[{{r, Pi, theta2}}, {r, 0, 1}, {theta2, -Pi/3, 
     0}, PlotRange -> {{-eps, 1 + eps}, {-eps, Pi + eps}, {-eps - Pi, 
       0 + eps}}, PlotStyle -> {Red, Opacity[op]}];
  p3 = ParametricPlot3D[{{1, psi, theta2}}, {psi, 0, 
     Pi}, {theta2, -Pi/3, 0}, 
    PlotRange -> {{-eps, 1 + eps}, {-eps, Pi + eps}, {-eps, 
       Pi + eps}}, PlotStyle -> {Red, Opacity[op]}];
  p4 = ParametricPlot3D[{{r, psi, -Pi}}, {r, 0, 1}, {psi, 0, Pi}, 
    PlotRange -> {{-eps, 1 + eps}, {-eps, Pi + eps}, {-eps, 
       Pi + eps}}, PlotStyle -> {Red, Opacity[op]}];
  p5 = ParametricPlot3D[{{0, psi, theta2}}, {psi, 0, 
     Pi}, {theta2, -Pi, psi - Pi}, 
    PlotRange -> {{-eps, 1 + eps}, {-eps, Pi + eps}, {-eps, 
       Pi + eps}}, PlotStyle -> {Red, Opacity[op]}];
  p6 = ParametricPlot3D[{{0, psi, theta2}}, {psi, 0, 
     Pi/3}, {theta2, -Pi/3 + psi, 0}, 
    PlotRange -> {{-eps, 1 + eps}, {-eps, Pi + eps}, {-eps, 
       Pi + eps}}, PlotStyle -> {Red, Opacity[op]}];
  d2 = Show[{p1, p2, p3, p4, p5, p6}];
  GraphicsRow[{d1, d2}]
  ]

fixedPlot := Module[{r0, psi0, theta20},
   {r0, psi0, theta20} = cords[{z10out, z20out, z30out}];
   Echo[{r0, psi0, theta20}];
   ListPointPlot3D[{{r0, psi0, theta20}, {r0, Pi - psi0, 
      Pi - theta20}}, PlotStyle -> {Red, Thick}]];

Clear[forwardArrow];

forwardPlot[r_, psi_, theta2_] := Module[{},
   Show[{Graphics3D[{Arrow[{{r, psi, theta2}, 
         forward3[r, psi, theta2]}]}, 
      PlotRange -> {{0, 1}, {0, Pi}, {-Pi, Pi}}, Axes -> Automatic], 
     fixedPlot}]];

showStuff[X_] := 
  Show[{Graphics3D[{Arrowheads[0.01], X}, 
     PlotRange -> {{0, 1}, {0, Pi}, {-Pi, Pi}}, Axes -> Automatic], 
    fixedPlot}];

P1forwardArrow[pt_] := Module[{p1},
   p1 = Apply[forward3, pt];
   If[p1[[3]] > 0, Arrow[{pt, p1}], {}]];

skip := Module[{doc = "P1,P5 behavior", rr, a},
   rr := {RandomReal[{0.25, 0.28}], RandomReal[{2.95, 3}], 
     RandomReal[{0.2, 0.25}]};
   a = Table[P1forwardArrow[rr], {500}];
   showStuff[a]];

cubeDecomposition:= Module[{doc = "MCA:SAVE:cube decomposition of P1", ranges, parts, rr, frr, tab,
   tab2, f1, ipsi = 2, ith = 0, eps = 10^-4, rmax = 1, inside, skip},
 ranges = {{eps, rmax - eps}, Pi/3 {ipsi + eps, ipsi + 1 - eps}, 
   Pi/3 {ith + eps, ith + 1 - eps}};
 rr := {RandomReal[ranges[[1]]], RandomReal[ranges[[2]]], 
   RandomReal[ranges[[3]]]};
 f1 := Module[{r1, pos, v},
   r1 = rr;
   pos = RandomInteger[{1, 3}];
   v = RandomInteger[{1, 2}];
   If[RandomInteger[{0, 1}] == 0, r1[[pos]] = ranges[[pos, v]]];
   r1
   ];
 inside[f_] := Module[{ff},
   ff = Apply[forward3, f];
   ff[[3]] > 0];
 doc = "forward map";
 skip := tab = 
   Table[(frr = Apply[forward3, f1]; 
     If[frr[[3]] > 0, frr, Nothing]), {1000}];
 doc = "backwards map";
 tab = Table[(frr = f1; 
    If[Apply[forward3, frr][[3]] > 0, Nothing, 
     Apply[backward3, frr]]), {5000}];
 tab2 = Select[tab, Not[inside[#]] &];
 Echo[{Length[tab], Length[tab2]}];
 ConvexHullMesh[Map[Drop[#, 1] &, tab], Axes -> Automatic, 
  PlotRange -> {{0, Pi}, {0, Pi}}]
 ];

Echo["F2100"];

(* April 13-14, 2024 *)

(* BEGIN HERE April 13 2024 *)
secondBigCellParition6828854Plot3D := 
 Module[{doc = "Draw Geometric Partition, MCA:6828854", eps = 10^-3, chiA0, delA, 
   D2, D3, D2top, D3top, skip},
  doc = "second big cell";
  chiA0 = 
   Apply[switchFn, 
    DataGeneric[Conjugate[zeta], 1, 0, r0, psi0, thet20]]; 
  delA = Discriminant[chiA0, t];
  D2top = Module[{d},
    d = delA /. thet20 -> -eps; 
    RegionPlot[d >=  0, {r0, eps, 1 - eps}, {psi0, eps, Pi - eps}, 
     MaxRecursion -> Automatic, PlotPoints -> Automatic, 
     PlotStyle -> Opacity[0.5], Mesh -> None, 
     PlotRange -> {{0, 1}, {0, Pi}}]];
  D3top = Module[{d},
    d = delA /. thet20 -> -eps; 
    RegionPlot[d <=   0, {r0, eps, 1 - eps}, {psi0, eps, Pi - eps}, 
     MaxRecursion -> Automatic, PlotPoints -> Automatic, 
     PlotStyle -> Opacity[0.5], Mesh -> None, 
     PlotRange -> {{0, 1}, {0, Pi}}]];
  D2 = RegionPlot3D[
    delA >=  0, {r0, eps, 1 - eps}, {psi0, eps, 
     Pi - eps}, {thet20, -Pi/3 + eps, 0 - eps}, 
    MaxRecursion -> Automatic, PlotPoints -> Automatic, 
    PlotStyle -> Opacity[0.5], Mesh -> None, 
    PlotRange -> {{0, 1}, {0, Pi}, {-Pi, 0}}];
  D3 = RegionPlot3D[
    Or[delA <= 0, thet20 <= -Pi/3], {r0, eps, 1 - eps}, {psi0, eps, 
     Pi - eps}, {thet20, -Pi + eps, 0 - eps}, 
    MaxRecursion -> Automatic, PlotPoints -> Automatic, 
    PlotStyle -> Opacity[0.5], Mesh -> None, 
    PlotRange -> {{0, 1}, {0, Pi}, {-Pi, 0}}];
  GraphicsGrid[{{D2top, D3top}, {D2, D3}}]
 ];

surfaceResultantPlot3DAltRevised := 
  Module[{doc = 
     "boundary chiA,chiB via image of x3=0, replaces test45, save", 
    eps = 10^-3, plot4, plot4A, plot5, psi, thmin, thmax, fun, fun2, 
    skip, b1}, 
   fun[s1_, theta2_] := 
    Module[{docYC = "x3=0", z0, u}, z0 = DataSZ[s1, theta2];
     u = If[theta2 > 0, zeta, Conjugate[zeta]];
     cords[rotateFuller[tauSymmetry[FullerPoincareU[z0, u]]]]];
   {thmin, thmax} = Echo[{Pi/3 + eps, Pi - eps}];
   plot4 = 
    ParametricPlot3D[
     fun[s1, theta2], {s1, -1 + eps, 1 - eps}, {theta2, thmin, thmax},
      PlotRange -> {{0, 1}, {0, Pi}, {-0.1, Pi}}, 
     PlotStyle -> {Red, Opacity[1]}];
   plot4A = 
    ParametricPlot3D[fun[-1 + eps, theta2], {theta2, thmin, thmax}, 
     PlotStyle -> {Black, Thick}];
   b1 = {ParametricPlot3D[{0, t, t}, {t, 0, Pi}],
     ParametricPlot3D[{1, t, 0}, {t, 0, Pi}],
     ParametricPlot3D[{t, 0, 0}, {t, 0, 1}],
     ParametricPlot3D[{t, Pi, 0}, {t, 0, 1}],
     ParametricPlot3D[{0, Pi, t}, {t, 0, Pi}]};
   fun2[r_, psi_] := 
    Module[{doc2 = "", z0, u}, z0 = DataZ[r, psi, Pi - eps];
     u = zeta;
     cords[rotateFuller[tauSymmetry[FullerPoincareU[z0, u]]]]];
   plot5 = 
    ParametricPlot3D[
     fun2[r, psi], {r, eps, 1 - eps}, {psi, eps, Pi - eps}, 
     PlotStyle -> Directive[Yellow]];
   Show[{plot4, b1, plot5}(* ViewPoint\[Rule]{-2,-2,1.5} *)]];

surfaceResultantPlot3D := 
 Module[{doc = "two views, MCA use in paper", plot},
  plot = surfaceResultantPlot3DAltRevised;
  GraphicsRow[{plot, 
    Show[plot, ViewVertical -> {-1, 0, 0}, 
	 ViewPoint -> {-2, -2, 1.5}]}]];

forwardSamplePart5049419Plot3D := 
 Module[{doc = "MCA:5049419, forward3 map on part D21 D1", f, as, bs, 
   eps = 10^-3, psimin, psimax, theta2min, theta2max, plotrange, p1, 
   p2, p3, p4, p5, p6, q, u = zeta, chiA0, chiB1, res, case = {2, 1}, 
   i, j,skip},
  as = {0, Pi/3, 2 Pi/3, Pi};
  bs = {Pi, Pi - 1.1, 1.1, 0};
  {chiA0, chiB1} = chiA0B1U[rx, psi, theta2, u];
  res = Resultant[chiA0, chiB1, t];
  f[r0_, psi0_, theta20_] := Module[{rAB, rr, res1, r1},
    rr = forward3[r0, psi0, theta20];
    If[Last[rr] > 0, Return[rr]];
    res1 = res /. {theta2 -> theta20, psi -> psi0};
    rAB = NSolve[res1 == 0 && rx > 0 && rx < 1, rx, Reals];
    If[rAB == {}, (Echo[{"BAD INPUT:", r0, psi0, theta20}]; 
      Return[{0, 0, 0}])];
    r1 = Min[rx /. rAB] + eps;
    forward3[r1, psi0, theta20]
    ];
  {i, j} = case;
  skip:={i, j} = {0, 1};
  {psimin, psimax} = {as[[i + 1]] + eps, as[[i + 2]] - eps};
  {theta2min, theta2max} = {bs[[j + 2]] + eps, bs[[j + 1]] - eps};
  plotrange = {{0, 1}, {0, Pi}, {0, Pi}};
  doc = "Don't need r=0,r=1 faces, because those faces degenerate";
  p1 = ParametricPlot3D[
     f[r, psi, theta2min], {r, eps, 1 - eps}, {psi, psimin, psimax}, 
     PlotRange -> plotrange, Axes -> Automatic] // Echo;
  p2 = ParametricPlot3D[
     f[r, psi, theta2max], {r, eps, 1 - eps}, {psi, psimin, psimax}, 
     PlotRange -> plotrange, Axes -> Automatic] // Echo;
  p3 = ParametricPlot3D[
     f[r, psimin, theta2], {r, eps, 1 - eps}, {theta2, theta2min, 
      theta2max}, PlotRange -> plotrange, Axes -> Automatic] // Echo;
  p4 = ParametricPlot3D[
     f[r, psimax, theta2], {r, eps, 1 - eps}, {theta2, theta2min, 
      theta2max}, PlotRange -> plotrange, Axes -> Automatic] // Echo;
  Show[{p1, p2, p3, p4}]];

forwardDout := 
 Module[{doc = "MCA:2082214, forward3 map on part Dout", f, a0, a1, 
   a2, a3, b3, b2, b1, b0, eps = 10^-4, psimin, psimax, theta2min, 
   theta2max, plotrange, p1, p2, p3, p4, p5, p6, q},
  {a0, a1, a2, a3} = {0, Pi/3, 2 Pi/3, Pi};
  {b0, b1, b2, b3} = {Pi, Pi - 1.1, 1.1, 0};
  f[r_, psi_, theta2_] := forward3[r, psi, theta2];
  {psimin, psimax} = {a0 + eps, a1 - eps};
  {theta2min, theta2max} = {b1 + eps, b0 - eps};
  plotrange = {{0, 1}, {a0, a1}, {b1, b0}};
  p1 = ParametricPlot3D[
    f[r, psi, theta2min], {r, eps, 1 - eps}, {psi, psimin, psimax}, 
    PlotRange -> plotrange, Axes -> Automatic];
  p2 = ParametricPlot3D[
    f[r, psi, theta2max], {r, eps, 1 - eps}, {psi, psimin, psimax}, 
    PlotRange -> plotrange, Axes -> Automatic];
  p3 = ParametricPlot3D[
    f[r, psimin, theta2], {r, eps, 1 - eps}, {theta2, theta2min, 
     theta2max}, PlotRange -> plotrange, Axes -> Automatic];
  p4 = ParametricPlot3D[
    f[r, psimax, theta2], {r, eps, 1 - eps}, {theta2, theta2min, 
     theta2max}, PlotRange -> plotrange, Axes -> Automatic];
  p5 = ParametricPlot3D[
    f[eps, psi, theta2], {psi, psimin, psimax}, {theta2, theta2min, 
     theta2max}, PlotRange -> plotrange, Axes -> Automatic];
  p6 = ParametricPlot3D[
    f[1 - eps, psi, theta2], {psi, psimin, psimax}, {theta2, 
     theta2min, theta2max}, PlotRange -> plotrange, Axes -> Automatic];
  Show[{{p1, p2, p3, p4, p5, p6}, 
    ListPointPlot3D[{cords[{z10out, z20out, z30out}] -> 
       "fixed point"}, ColorFunction -> "Rainbow"]}]
  ];

skip := Module[{doc = "forwardDout"}, 
  Show[{forwardDout, 
    ListPointPlot3D[{cords[{z10out, z20out, z30out}] -> 
						      "fixed point"}, ColorFunction -> "Rainbow"]}]];

Clear[cubes];
cubes[i_, j_, num_] :=
  
  Module[{doc = "", ranges, parts, rr, frr, tab, tab2, f1, ipsi = 2, 
    ith = 0, eps = 10^-4, rmax = 1, insideD0D1, skip, as, bs, 
    case = {i, j}},
   as = {0, Pi/3, 2 Pi/3, Pi};
   bs = {Pi, Pi - 1.1, 1.1, 0};
   Echo[case];
   ranges = {{eps, rmax - eps}, {as[[i + 1]] + eps, 
      as[[i + 2]] - eps}, {bs[[j + 2]] + eps, bs[[j + 1]] - eps}};
   rr := {RandomReal[ranges[[1]]], RandomReal[ranges[[2]]], 
     RandomReal[ranges[[3]]]};
   f1 := Module[{r1, pos, v}, r1 = rr;
     pos = RandomInteger[{1, 3}];
     v = RandomInteger[{1, 2}];
     If[RandomInteger[{0, 1}] == 0, r1[[pos]] = ranges[[pos, v]]];
     r1];
   insideD0D1[f_] := Module[{ff}, ff = Apply[forward3, f];
     ff[[3]] > 0];
   doc = "forward map";
   tab = Table[(frr = Apply[forward3, f1];
      If[frr[[3]] > 0, frr, Nothing]), {num}];
   tab2 = Select[tab, Not[insideD0D1[#]] &];
   Echo[{Length[tab], Length[tab2]}];
   ConvexHullMesh[Map[Drop[#, 1] &, tab], Axes -> Automatic, 
		  PlotRange -> {{0, Pi}, {0, Pi}}]];

cubeDomain2381734Plot := 
 Module[{doc = 
    "MCA:2381734, Compute images of various rectangles in domain D1.",
    cube01, cube02, cube10, cube11, cube12, cube20, cube21, frame, as,
    bs, lesserA, lesserB, num = 10},
  cube01 = cubes[0, 1, num];
  cube02 = cubes[0, 2, num];
  cube10 = cubes[1, 0, num];
  cube11 = cubes[1, 1, num];
  cube12 = cubes[1, 2, num];
  cube20 = cubes[2, 0, num];
  cube21 = cubes[2, 1, num];
  as = {0, Pi/3, 2 Pi/3, Pi};
  bs = {Pi, Pi - 1.1, 1.1, 0};
  lesserA[{i_, j_}] := {{0, as[[i + 1]]}, {0, Pi}};
  lesserB[{i_, j_}] := Module[{},
    "j>0";
    {{as[[i + 1]], as[[i + 2]]}, {bs[[j + 1]], Pi}}
    ];
  frame[c_, {i_, j_}] := Module[{l},
    Show[{c, 
      ParametricPlot[{Pi/3, t}, {t, 0, Pi}, PlotStyle -> Gray],
      ParametricPlot[{2 Pi/3, t}, {t, 0, Pi}, PlotStyle -> Gray],
      ParametricPlot[{t, 1.1}, {t, 0, Pi}, PlotStyle -> Gray],
      ParametricPlot[{t, Pi - 1.1}, {t, 0, Pi}, PlotStyle -> Gray],
      ParametricPlot[{s, t}, {s, as[[i + 1]], as[[i + 2]]}, {t, 
        bs[[j + 2]], bs[[j + 1]]}, 
       PlotStyle -> {Gray, Opacity[0.2]}],
      ListPlot[{Labeled[{as[[i + 1]], bs[[j + 2]]}, 
         ToString[{i, j}]]}, PlotStyle -> {Gray, Opacity[0.0]}],
      If[i > 0, (l = lesserA[{i, j}]; 
        ParametricPlot[{s, t}, {s, l[[1, 1]], l[[1, 2]]}, {t, 
          l[[2, 1]], l[[2, 2]]}, 
         PlotStyle -> {Yellow, Opacity[0.1]}]), Nothing],
      If[j > 0, (l = lesserB[{i, j}]; 
        ParametricPlot[{s, t}, {s, l[[1, 1]], l[[1, 2]]}, {t, 
          l[[2, 1]], l[[2, 2]]}, 
         PlotStyle -> {Yellow, Opacity[0.1]}]), Nothing]}]];
  GraphicsGrid[{{"", frame[cube10, {1, 0}], frame[cube20, {2, 0}]},
    {frame[cube01, {0, 1}], frame[cube11, {1, 1}], 
     frame[cube21, {2, 1}]},
		{frame[cube02, {0, 2}], frame[cube12, {1, 2}], ""}}]];

inclusion1350181Plot := 
 Module[{doc = 
    "MCA:1350181 F^-1(D4) is in Din <=> F^2(D3) is in Dout", ranges, 
   parts, rr, frr, tab, tab2, f1, ipsi = 2, ith = 0, eps = 10^-4, 
   rmax = 1, insideD0D1, skip, as, bs, case = {0, 1}, i, j},
  ranges = {{eps, 1 - eps}, {eps, Pi - eps}, {-Pi + eps, -eps}};
  rr := {RandomReal[ranges[[1]]], RandomReal[ranges[[2]]], 
    RandomReal[ranges[[3]]]};
  f1 := Module[{r1, pos, v}, r1 = rr;
    pos = RandomInteger[{1, 3}];
    v = RandomInteger[{1, 2}];
    If[RandomInteger[{0, 1}] == 0, r1[[pos]] = ranges[[pos, v]]];
    r1];
  doc = "forward-squared map";
  tab = Table[(frr = Apply[forward3, f1];
     If[frr[[3]] > 0, Apply[forward3, frr], Nothing]), {10000}];
  Echo[Length[tab]];
  Show[{ConvexHullMesh[Map[Drop[#, 1] &, tab], Axes -> Automatic, 
     PlotRange -> {{0, Pi}, {0, Pi}}], 
    ParametricPlot[{Pi/3, Pi - t}, {t, 0, 1.1}, PlotStyle -> Black],
	ParametricPlot[{t, Pi - 1.1}, {t, 0, Pi/3}, PlotStyle -> Black]}]];

Echo["F2300"];
