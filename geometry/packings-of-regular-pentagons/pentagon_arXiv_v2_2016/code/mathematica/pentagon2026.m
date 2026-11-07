(* ::Package:: *)

(* Mathematica for "Packings of Regular Pentagons in the Plane "*)
(* Uses pentca.m. Run that package first *)
(* Section 1. Introduction *)
Clear[NPrec];
Claim[x_, msg_] := If[Not[TrueQ[x]], Echo[{x, msg}]];
NZero[x_, d_] := Abs[x] < 0.5*10^-d;

kappa = Cos[Pi/5];
sigma = Sin[Pi/5];
aK = Echo[FullSimplify[(1 + kappa) (3 kappa sigma)/2]] // N;
aK2 = (3/16) Sqrt[(5 (5 + 2 Sqrt[5]))];
amin = 1.237;
densityK = (5 - Sqrt[5])/3 // N;
pentarea = 5 kappa sigma;
Claim[NZero[aK2 - aK, 5], "radicals aK"];
Claim[NZero[densityK - 0.921311, 6], "iceray density"];
Claim[NZero[kappa - 0.809, 3], "N[kappa]"];
Claim[NZero[sigma - 0.5878, 4], "N[sigma]"];
Claim[NZero[aK - 1.29036, 5], "N[aK]"];
Claim[NZero[(1/2) (pentarea)/aK - densityK, 14], 
  "common area of every ice-ray Delaunay"];
Claim[NZero[kappa Sqrt[8] - 2.288, 3], "kappa sqrt8. Lemma 28"];
Claim[NZero[Sqrt[(2 kappa)^2 + sigma^2] - 1.72149, 5], 
  "Lemma 34, lemma:mid-172"];
Claim[area[1.72,1.8,1.8]> (2 aK - amin),"Lemma 40"]


Module[{v0, v1, v2, cis, x, y, d1, d2, iceraytri},
 "Check the area of an iceray Delaunay Triangle";
 "vertices v0,v1,v2";
 cis[theta_] := {Cos[theta], Sin[theta], 1};
 "pentagon 0 at the origin, pointing upward";
 v0 = {0, 0, 1};
 "pentagon 1 stacked above, pointing upward";
 v1 = {0, 1 + kappa, 1};
 "pentagon 2 in next column, pointing downward";
 v2 = {x, y, 1};
 "collinearity of the edges of v1 and v2";
 d1 = Det[{v2 + cis[-Pi/2 + 6 Pi/5], v1 + cis[Pi/2 - 2 Pi/5], 
     v1 + cis[Pi/2 - 4 Pi/5]}] // Simplify;
 d2 = Det[{v2 + cis[-Pi/2 + 8 Pi/5], v0 + cis[Pi/2], 
     v0 + cis[Pi/2 - 2 Pi/5]}] // Simplify;
 v2 = v2 /. First[Solve[{d1 == 0, d2 == 0}, {x, y}]] // FullSimplify;
 iceraytri = Det[{v1, v0, v2}]/2 // FullSimplify;
 Claim[NZero[iceraytri - aK, 14], "iceray Delaunay area"]
 ]


(* Section 2. Clusters of Delaunay Triangles *)
amin = 1.237;
epsN = aK - amin;
Claim[NZero[epsN - 0.05336, 5], "epsN"];
epsM = 0.008;

