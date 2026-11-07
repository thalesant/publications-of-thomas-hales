(* Definition-only Wolfram drawing helpers. Angles in radians; circumradius 1.
   Based on the original pentgraphics.m constructions. These are illustrations,
   not interval proof code. Existing paper figures are preserved exactly as TikZ. *)
BeginPackage["PentagonFigures`"];
PentagonVertices::usage="PentagonVertices[{x,y},theta] returns five unit-circumradius vertices.";
DrawPentagons::usage="DrawPentagons[{{x,y,theta},...}] draws pentagons and centers.";
GammaDimer::usage="GammaDimer[t] draws the fixed-orientation translational ice-ray shear.";
Begin["`Private`"];
PentagonVertices[c:{_,_},theta_] := Table[c+{Cos[theta+2 Pi j/5],Sin[theta+2 Pi j/5]},{j,0,4}];
Options[DrawPentagons]={ImageSize->600};
DrawPentagons[data_List,OptionsPattern[]] := Graphics[{
 {EdgeForm[Directive[Red,Thickness[.002]]],FaceForm[Opacity[.12,Red]],
  Polygon[PentagonVertices[Take[#,2],#[[3]]]]& /@ data},
 {Blue,PointSize[.012],Point[Take[#,2]]& /@ data}},ImageSize->OptionValue[ImageSize],PlotRange->All];
GammaDimer[t_] := Module[{k=Cos[Pi/5],s=Sin[Pi/5],a,b,c,d,shapes},
 a={0,0};c={1+k,t};b={(6 k-1)/4-s t,3 k s+k t};d={(6 k-1)/4+s t,-3 k s+k t};
 shapes=DrawPentagons[{Append[a,0],Append[b,Pi],Append[c,0],Append[d,Pi]}];
 Show[shapes,Graphics[{Blue,Line[{a,b,c,d,a}],Dashed,Line[{a,c}],Line[{b,d}]}]]];
End[];EndPackage[];
