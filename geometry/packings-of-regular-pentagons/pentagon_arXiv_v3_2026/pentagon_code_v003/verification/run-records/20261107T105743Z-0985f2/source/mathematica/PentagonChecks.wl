(* Supplementary paper checks for pentagon_v005.tex. Definitions only on Get.
   Each check is explained in checks_catalog.json and docs/WOLFRAM_CHECKS.md.
   Exact paper assertions, supporting identities, implementation fixtures, and
   numerical diagnostics are explicitly distinguished in the report. *)
BeginPackage["PentagonChecks`"];
RunChecks::usage = "RunChecks[\"Sections\"->All,\"NumericalDiagnostics\"->True] returns a structured report. No kernel exit is performed.";
$LastReport::usage = "The most recent structured check report.";
ExportReport::usage = "ExportReport[file, report] writes a source-identified JSON record without exiting the kernel.";
DescribeChecks::usage = "DescribeChecks[] returns the mathematical descriptions and paper references of the checks.";
AvailableSections::usage = "AvailableSections[] lists the selectable paper-check groups.";
TriangleArea::usage = "TriangleArea[a,b,c] is the exact Heron area on valid positive triangle sides.";
CircleArea::usage = "CircleArea[a,b,r] is the area for the obtuse branch whose short sides are a,b and circumradius r; validity assumptions are documented.";
GammaArea::usage = "GammaArea[t] = 2 acrit + sigma t^2; t is the centered slide parameter.";
Begin["`Private`"];
packageDirectory = DirectoryName[$InputFileName];
packageRoot = DirectoryName[packageDirectory];
checkCatalog = Import[FileNameJoin[{packageDirectory,"checks_catalog.json"}],"RawJSON"];
expectedCatalog = Import[FileNameJoin[{packageDirectory,"expected_checks.json"}],"RawJSON"];
If[!AssociationQ[checkCatalog] || !AssociationQ[expectedCatalog],
 Print["Missing or invalid check metadata next to PentagonChecks.wl."]; Abort[]];
DescribeChecks[] := checkCatalog;
DescribeChecks[section_String] := Select[checkCatalog, Lookup[#, "section", ""] === section &];
sourceRelativePaths = {"mathematica/PentagonChecks.wl","mathematica/run_checks.wls",
 "mathematica/checks_catalog.json","mathematica/expected_checks.json",
 "paper/pentagon_v005.tex","paper/label-map.json"};
sourceIdentity[] := Association[(# -> IntegerString[FileHash[FileNameJoin[Prepend[StringSplit[#,"/"],packageRoot]],"SHA256"],16,64])& /@ sourceRelativePaths];
loadedSourceIdentity = sourceIdentity[];
ExportReport[file_String,report_Association] := Module[{out=ExpandFileName[file], result},
 If[!TrueQ[Lookup[report,"SourceSHA256",<||>]===sourceIdentity[]],
   Return[Failure["SourceIdentity",<|"Message"->"Sources changed after evaluation; run the checks again."|>]]];
 If[!DirectoryQ[DirectoryName[out]],CreateDirectory[DirectoryName[out],CreateIntermediateDirectories->True]];
 result=Quiet[Check[Export[out,report,"RawJSON"],$Failed]];
 If[result===$Failed,Failure["Export",<|"Path"->out|>],Print["Report: ",out];out]
];
k=Cos[Pi/5]; s=Sin[Pi/5]; aK=3 s k (1+k)/2;
amin=1237/1000; epsN=aK-amin; epsM=1/125;
triangleArea[a_,b_,c_] := Sqrt[2 (a^2 b^2+b^2 c^2+c^2 a^2)-a^4-b^4-c^4]/4;
circleArea[a_,b_,r_] := a b (a Sqrt[1-b^2/(4 r^2)]+b Sqrt[1-a^2/(4 r^2)])/(4 r);
TriangleArea[a_,b_,c_] := triangleArea[a,b,c];
CircleArea[a_,b_,r_] := circleArea[a,b,r];
GammaArea[t_] := 2 aK+s t^2;
arc[a_,b_,c_] := ArcCos[(a^2+b^2-c^2)/(2 a b)];
loc[a_,b_,theta_] := Sqrt[a^2+b^2-2 a b Cos[theta]];
ellx[x_,alpha_] := Sqrt[1+(s-x)^2+k^2-2 (s-x) Cos[alpha+3 Pi/10]+2 k Sin[alpha+3 Pi/10]];
angleArea[a_,b_,c_] := a b Sin[arc[a,b,c]]/2;
exactZero[x_] := TrueQ[FullSimplify[x==0]];
positive[x_] := TrueQ[RootReduce[x]>0];
rounded[x_,decimal_,places_Integer] := TrueQ[RootReduce[Abs[x-decimal]-1/(2 10^places)]<0];
$LastReport=<|"Status"->"NOT_RUN"|>;
$sectionNames={"constants","triangle-bounds","obtuse-endpoints","gamma","contact-identities","diagnostics"};
AvailableSections[] := $sectionNames;
SetAttributes[record,HoldAll];
record[id_,kind_,claim_,condition_] := Module[{value,seconds,ok,info},
 info=Lookup[checkCatalog,id,Missing["UndocumentedCheck"]];
 {seconds,value}=AbsoluteTiming[TimeConstrained[Quiet[Check[condition,$Failed]],checkTimeLimit,$TimedOut]];
 ok=TrueQ[value] && AssociationQ[info];
 AppendTo[checks,<|"ID"->id,"Kind"->kind,"PaperLabel"->claim,"Passed"->ok,
 "PaperReference"->If[AssociationQ[info],info["paper_reference"],"Undocumented"],
 "Role"->If[AssociationQ[info],info["role"],"Undocumented"],
 "Description"->If[AssociationQ[info],info["title"],"Undocumented"],
 "Assertion"->If[AssociationQ[info],info["assertion"],"Undocumented"],
 "Why"->If[AssociationQ[info],info["why"],"Undocumented"],
 "Seconds"->seconds,"Detail"->If[ok,"",ToString[value,InputForm]]|>];
 Print["  [",If[ok,"PASS","FAIL"],"] [",kind,"] ",id,
   If[AssociationQ[info]," — "<>info["title"]<>" ("<>info["paper_reference"]<>")",""]];
 If[AssociationQ[info],Print["      ",info["role"],": ",info["assertion"]]];
 ok];
runConstants[] := (
 record["constants.kappa-radical","EXACT","sec:intro",exactZero[k-(1+Sqrt[5])/4]];
 record["constants.sigma-radical","EXACT","sec:intro",exactZero[s-Sqrt[10-2 Sqrt[5]]/4]];
 record["constants.acrit-radical","EXACT","sec:intro",exactZero[aK-3 Sqrt[5 (5+2 Sqrt[5])]/16]];
 record["constants.density","EXACT","sec:intro",exactZero[5 k s/(2 aK)-(5-Sqrt[5])/3]];
 record["constants.pentagon-area","EXACT","sec:intro",exactZero[5 k s-5 Sin[2 Pi/5]/2]];
 record["constants.pythagorean","EXACT","sec:intro",exactZero[k^2+s^2-1]];
 record["constants.golden-ratio","EXACT","sec:intro",exactZero[4 k^2-2 k-1]];
 record["rounding.density","EXACT","sec:intro",rounded[(5-Sqrt[5])/3,921311/10^6,6]];
 record["rounding.kappa","EXACT","sec:intro",rounded[k,809/1000,3]];
 record["rounding.sigma","EXACT","sec:intro",rounded[s,5878/10000,4]];
 record["rounding.acrit","EXACT","sec:intro",rounded[aK,129036/100000,5]];
 record["rounding.epsilonN","EXACT","eqn:epsN",rounded[epsN,5336/100000,5]];
 record["constants.corrections-ordered","EXACT","eqn:epsM",positive[epsN-epsM]&&positive[epsM]];
 record["constants.midpointer-rounded","EXACT","lemma:mid-172",rounded[Sqrt[4 k^2+s^2],172149/100000,5]];
 record["constants.sqrt8-kappa-rounded","EXACT","lemma:right",rounded[Sqrt[8] k,2288/1000,3]];
 record["constants.rational-inputs","EXACT","eqn:epsM",Head[amin]===Rational&&Head[epsM]===Rational];
);
runTriangleBounds[] := (
 record["bound.lemma21","EXACT","lemma:21",positive[triangleArea[21/10,2 k,2 k]-aK]];
 record["bound.right-gap","EXACT","lemma:right",positive[k Sqrt[8]-21/10]];
 record["bound.midpointer","EXACT","lemma:mid-172",positive[Sqrt[4 k^2+s^2]-43/25]];
 record["bound.pseudo3","EXACT","calc:pseudo3",positive[triangleArea[43/25,9/5,9/5]-(aK+epsN)]];
 record["bound.pseudo-table-111","EXACT","lemma:pd-nra-dimer",positive[triangleArea[9/5,9/5,9/5]-(aK+112/1000)]];
 record["bound.pseudo-table-110","EXACT","lemma:pd-nra-dimer",positive[triangleArea[9/5,9/5,43/25]-(aK+69/1000)]];
 record["bound.pseudo-table-100","EXACT","lemma:pd-nra-dimer",positive[triangleArea[9/5,43/25,43/25]-(aK+3 epsM)]];
 record["bound.pseudo-table-11min","EXACT","lemma:pd-nra-dimer",positive[triangleArea[9/5,9/5,2 k]-(aK+epsM)]];
 record["bound.obtuse-neighbor","EXACT","lemma:Nb",positive[triangleArea[k Sqrt[8],2 k,43/25]-(aK+epsN)]];
 record["bound.two-nonobtuse","EXACT","sec:obtuse",positive[triangleArea[k Sqrt[8],43/25,43/25]-(aK+2 epsN)]];
 record["bound.two-mcorrections","EXACT","sec:obtuse",positive[triangleArea[k Sqrt[8],43/25,2 k]-(aK+2 epsM)]];
 record["bound.three-m","EXACT","sec:obtuse",positive[triangleArea[9/5,9/5,9/5]-(aK+3 epsM+epsN)]];
 record["bound.obtuse-adjacent","EXACT","sec:obtuse",positive[circleArea[2 k,k Sqrt[8],2]-(aK+2 epsN)]];
 record["bound.obtuse-case1-circle","EXACT","sec:obtuse",positive[(2 k)^3 (1-(2 k)^2/16)^(3/2)-(2 aK+4 epsN)]];
 record["bound.obtuse-case1-right-boundary","EXACT","sec:obtuse",positive[k^2 Sqrt[8]+circleArea[2 k,2 k,2]-(2 aK+4 epsN)]];
 record["bound.obtuse-case1-shared-chord","EXACT","sec:obtuse",positive[4 k Sqrt[1-k^2/4]-(43/25) Sqrt[2]]];
 record["bound.case2-central","EXACT","sec:obtuse",positive[triangleArea[2 k,k Sqrt[8],k Sqrt[8]]-173/100]];
 record["bound.case2-central-charged","EXACT","sec:obtuse",positive[triangleArea[43/25,k Sqrt[8],k Sqrt[8]]-(173/100+epsN)]];
 record["bound.case2-small-radius","EXACT","sec:obtuse",positive[circleArea[2 k,2 k,17/10]-108/100]];
 record["bound.case2-small-radius-charged","EXACT","sec:obtuse",positive[circleArea[2 k,43/25,17/10]-(108/100+2 epsN)]];
 record["bound.case2-total-small","EXACT","sec:obtuse",positive[173/100+2 (108/100)-3 aK]];
 record["bound.obtuse-minimum","EXACT","sec:obtuse",positive[circleArea[2 k,2 k,2]-968/1000]];
 record["bound.case2-large-radius-central","EXACT","sec:obtuse",positive[k Sqrt[4 (17/10)^2-4 k^2]-241/100]];
 record["bound.case2-total-large","EXACT","sec:obtuse",positive[2 (968/1000)+241/100-(3 aK+5 epsN)]];
 record["bound.case3-equilateral","EXACT","sec:obtuse",positive[triangleArea[k Sqrt[8],k Sqrt[8],k Sqrt[8]]-22668/10000]];
 record["bound.case3-large-radius-central","EXACT","sec:obtuse",positive[Sqrt[8] k/2 Sqrt[4 (17/10)^2-8 k^2]-26/10]];
 record["bound.case3-total-small","EXACT","sec:obtuse",positive[22668/10000+3 (108/100)-(4 aK+6 epsN)]];
 record["bound.case3-total-large","EXACT","sec:obtuse",positive[26/10+3 (968/1000)-(4 aK+6 epsN)]];
 record["bound.case5-center","EXACT","sec:obtuse",positive[circleArea[k Sqrt[8],k Sqrt[8],2]-245/100]];
 record["bound.case5-total","EXACT","sec:obtuse",positive[245/100+2 (968/1000)-(3 aK+5 epsN)]];
 record["bound.nonobtuse-two","EXACT","sec:nonobtuse",positive[amin+triangleArea[9/5,9/5,43/25]-2 epsM-2 aK]];
 record["bound.pseudo-area3-right","EXACT","sec:pseudo-area3",positive[2 amin+(9/5) k-(3 aK+epsM)]];
 record["bound.pseudo1-preparation","EXACT","sec:pseudo1",positive[amin+triangleArea[9/5,9/5,43/25]-2 aK]];
 record["bound.large-right-exclusion","EXACT","sec:large",positive[amin+(43/25) k-(2 aK+epsM)]];
 record["bound.squeeze-side-cut","EXACT","lemma:squeeze-area",positive[k Sqrt[(58/25)^2-(2 k)^2]-(aK+epsN)]];
 record["bound.pent3-unshared-cut","EXACT","calc:pent3",positive[triangleArea[43/25,43/25,101/50]-(aK+2 epsN+epsM)]];
 record["bound.C013-cap-below-epsN","EXACT","calc:pseudo-area3",positive[epsN-2 epsM]];
 record["bound.BXZBPJW-stronger-cut","EXACT","calc:pseudo-area",positive[(2 aK-7/1000)-(2 aK-epsM)]];
 Do[With[{aa=z[[1]],bb=z[[2]],cc=z[[3]],ar=z[[4]]},
   record["triangle.pythagorean."<>ToString[z[[1]]],"EXACT","sec:area",exactZero[triangleArea[aa,bb,cc]-ar]]],
   {z,{{3,4,5,6},{5,12,13,30},{8,15,17,60},{7,24,25,84}}}];
 record["triangle.nonobtuse-equilateral","EXACT","sec:area",exactZero[triangleArea[2,2,2]-Sqrt[3]]];
 record["triangle.area-permutations","EXACT","sec:area",And@@(exactZero[(triangleArea@@#)-triangleArea[2,3,4]]& /@ Permutations[{2,3,4}])];
 record["triangle.radius345","EXACT","sec:obtuse",exactZero[3 4 5/(4 triangleArea[3,4,5])-5/2]];
);
runObtuseEndpoints[] := Module[{d0=2 k,d1=43/25,target,cyclic,right,perms,legs,other,total,lo,hi,grid,lb,aa,bb,tt},
 Do[target=2 aK+j epsN;
   With[{sides=Join[ConstantArray[d1,j],ConstantArray[d0,4-j]],jj=j},
     cyclic=With[{p=Total[sides]/2},Sqrt[Times@@(p-sides)]];
     record["quadrilateral.cyclic."<>ToString[jj],"EXACT","sec:obtuse",positive[cyclic-target]];
     perms=DeleteDuplicates[Permutations[sides]];
     right=Select[perms,TrueQ[RootReduce[#[[1]]^2+#[[2]]^2-#[[3]]^2-#[[4]]^2]<=0]&];
     record["quadrilateral.right-nonempty."<>ToString[jj],"EXACT","sec:obtuse",Length[right]>0];
     Do[legs=Take[right[[n]],2];other=Drop[right[[n]],2];
       total=(Times@@legs)/2+triangleArea[other[[1]],other[[2]],Sqrt[Total[legs^2]]];
       record["quadrilateral.right."<>ToString[jj]<>"."<>ToString[n],"EXACT","sec:obtuse",positive[total-target]],{n,Length[right]}]
   ],{j,0,4}];
 (* On this interval Heron(2k,2k,x) decreases and CircleArea(2k,x,2)
    increases. Each of four exact endpoint differences is a uniform lower
    bound on its cell, not just a sampled check at that cell's center. *)
 lo=k Sqrt[8];hi=4 k Sqrt[1-k^2/4];grid=Table[lo+(hi-lo) i/4,{i,0,4}];
 Do[lb=triangleArea[2 k,2 k,grid[[i+1]]]+circleArea[2 k,grid[[i]],2];
  record["case4.cell-lower-bound."<>ToString[i],"EXACT","sec:obtuse",positive[lb-(2 aK+4 epsN)]],{i,1,4}];
 record["trapezoid.second-derivative","EXACT","sec:obtuse",
  TrueQ[FullSimplify[D[(bb+tt) Sqrt[aa^2-tt^2],{tt,2}]+(bb aa^2+3 aa^2 tt-2 tt^3)/(aa^2-tt^2)^(3/2)==0,Assumptions->aa>0&&-aa<tt<aa]]];
 record["trapezoid.radius-derivative","EXACT","sec:obtuse",
  TrueQ[FullSimplify[D[aa^2(aa^2+bb^2+2 bb tt)/(4(aa^2-tt^2)),tt]-aa^2(bb+tt)(aa^2+bb tt)/(2(aa^2-tt^2)^2)==0]]];
];
runGamma[] := Module[{t,x,u,v,bpoly,sides,heron,centers,ar1,ar2},
 u={1+k,t}; v={-2 s t,6 k s};
 record["Gamma.diagonal-determinant","EXACT","sec:gamma",exactZero[Det[{u,v}]/2-GammaArea[t]]];
 centers={{0,0},{(6 k-1)/4-s t,3 k s+k t},{1+k,t},{(6 k-1)/4+s t,-3 k s+k t}};
 ar1=Det[{centers[[3]],centers[[2]]}]/2;ar2=-Det[{centers[[3]],centers[[4]]}]/2;
 record["Gamma.first-triangle","EXACT","sec:gamma",exactZero[ar1-(aK+t/4+s t^2/2)]];
 record["Gamma.second-triangle","EXACT","sec:gamma",exactZero[ar2-(aK-t/4+s t^2/2)]];
 record["Gamma.sum","EXACT","sec:gamma",exactZero[ar1+ar2-GammaArea[t]]];
 record["Gamma.stationary","EXACT","sec:gamma",exactZero[D[GammaArea[t],t]/.t->0]];
 record["Gamma.second-derivative","EXACT","sec:gamma",exactZero[D[GammaArea[t],{t,2}]-2 s]];
 record["Gamma.strict-convexity","EXACT","sec:gamma",positive[2 s]];
 record["Gamma.symmetry","EXACT","sec:gamma",exactZero[GammaArea[t]-GammaArea[-t]]];
 sides={4 k^2+x^2,4 k^2+x^2/(4 k^2),(1+k)^2+(s-x)^2};
 bpoly=s x^2+(k-1)x+s(4 k+1);
 heron=2(sides[[1]] sides[[2]]+sides[[2]] sides[[3]]+sides[[3]] sides[[1]])-Total[sides^2];
 record["pinwheel.slice-stationary-parameter","EXACT","lemma:a0",exactZero[D[bpoly,x]/.x->(1-k)/(2 s)]];
 record["pinwheel.parameter-rounding","EXACT","lemma:a0",TrueQ[FullSimplify[Abs[(1-k)/(2 s)-16246/100000]<1/200000]]];
 record["pinwheel.slice-area-rounding","EXACT","lemma:a0",TrueQ[FullSimplify[Abs[(bpoly/.x->(1-k)/(2 s))/2-123719/100000]<1/200000]]];
 record["Gamma.Heron-factor","EXACT","sec:gamma",exactZero[heron-4 bpoly^2]];
 record["Gamma.positive-root-discriminant","EXACT","sec:gamma",exactZero[Discriminant[bpoly,x]+(13+15 Sqrt[5])/8]];
 record["Gamma.raw-centered-identity","EXACT","sec:shared",exactZero[(bpoly+(bpoly/.x->2 s-x))/2-GammaArea[x-s]]];
 Do[With[{tt=i/1000},record["Gamma.unique-minimum."<>ToString[i],"EXACT","sec:gamma",If[i==0,exactZero[GammaArea[tt]-2 aK],positive[GammaArea[tt]-2 aK]]]],{i,-10,10}];
];
runContactIdentities[] := Module[{x,alpha,aa,bb,cc},
 record["contact.slider-length","EXACT","sec:coords",exactZero[ellx[x,0]^2-(4 k^2+x^2)]];
 record["contact.midpointer-length","EXACT","sec:coords",exactZero[ellx[x,Pi/5]^2-((1+k)^2+(s-x)^2)]];
 record["contact.reflection","EXACT","sec:coords",exactZero[ellx[x,alpha]^2-ellx[2 s-x,2 Pi/5-alpha]^2]];
 record["contact.midpoint-value","EXACT","lemma:mid-172",exactZero[ellx[s,0]-Sqrt[4 k^2+s^2]]];
 record["contact.iceray-short-edge","EXACT","sec:gamma",exactZero[4 k^2+(s/(2 k))^2-11/4]];
 record["contact.iceray-unequal-boundary-edges","EXACT","cor:equal",positive[Sqrt[4 k^2+s^2]-Sqrt[11]/2]];
 record["area.squared-sides-Heron","EXACT","sec:coords",TrueQ[Expand[(16 triangleArea[aa,bb,cc]^2)-(aa+bb+cc)(-aa+bb+cc)(aa-bb+cc)(aa+bb-cc)]===0]];
 record["area.determinant345","EXACT","sec:coords",Det[{{3,0},{0,4}}]/2==triangleArea[3,4,5]];
];
runDiagnostics[] := Module[{pts,n,sides,ar,ref,angle,rot,translated,original},
 BlockRandom[SeedRandom[20261103];
  Do[pts=RandomReal[{-2,2},{3,2},WorkingPrecision->diagnosticPrecision];
    sides={Norm[pts[[2]]-pts[[1]]],Norm[pts[[3]]-pts[[2]]],Norm[pts[[1]]-pts[[3]]]};
    ar=N[triangleArea@@sides,diagnosticPrecision];ref=Abs[Det[{pts[[2]]-pts[[1]],pts[[3]]-pts[[1]]}]]/2;
    record["diagnostic.area-determinant."<>ToString[n],"NUMERIC","sec:coords",NumericQ[ar]&&Abs[ar-ref]<10^-40],{n,1,20}];
  Do[angle=RandomReal[{-Pi,Pi},WorkingPrecision->diagnosticPrecision];rot=RotationMatrix[angle];
    pts=RandomReal[{-2,2},{3,2},WorkingPrecision->diagnosticPrecision];
    translated=(rot.# + {3/7,-5/11})& /@ pts;
    original=Det[{pts[[2]]-pts[[1]],pts[[3]]-pts[[1]]}];
    ref=Det[{translated[[2]]-translated[[1]],translated[[3]]-translated[[1]]}];
    record["diagnostic.rigid-area."<>ToString[n],"NUMERIC","sec:coords",Abs[original-ref]<10^-40],{n,1,10}];
 ];
];
Options[RunChecks]={"Sections"->All,"NumericalDiagnostics"->True,"TimeLimit"->120,"WorkingPrecision"->80};
RunChecks[OptionsPattern[]] := Module[{selected,started,expected,failures,sectionsRun={},allIDs,inputIdentity,expectedIDs},
 If[loadedSourceIdentity=!=sourceIdentity[], Return[Failure["SourceIdentity",<|"Message"->"Files changed since Get; reload the package in a fresh kernel."|>]]];
 selected=OptionValue["Sections"];If[selected===All,selected=$sectionNames];
 If[!ListQ[selected]||selected==={}||!(And@@(MemberQ[$sectionNames,#]& /@ selected))||!DuplicateFreeQ[selected],Return[Failure["Selection",<|"Message"->"Use a nonempty list of available sections."|>]]];
 checkTimeLimit=OptionValue["TimeLimit"];diagnosticPrecision=OptionValue["WorkingPrecision"];
 If[!NumericQ[checkTimeLimit]||checkTimeLimit<=0||!IntegerQ[diagnosticPrecision]||diagnosticPrecision<60,Return[Failure["Options",<|"Message"->"Use a positive TimeLimit and at least 60 digits."|>]]];
 checks={};started=AbsoluteTime[];inputIdentity=sourceIdentity[];
 Print["Pentagon paper checks — manuscript pentagon_v005.tex"];
 Do[If[section==="diagnostics"&&!TrueQ[OptionValue["NumericalDiagnostics"]],
   Print["[NOT RUN] numerical diagnostics disabled"],
   Print["\n",StringRepeat["=",65],"\n",section];AppendTo[sectionsRun,section];
   Switch[section,"constants",runConstants[],"triangle-bounds",runTriangleBounds[],
     "obtuse-endpoints",runObtuseEndpoints[],"gamma",runGamma[],
     "contact-identities",runContactIdentities[],"diagnostics",runDiagnostics[]]],{section,selected}];
 allIDs=Lookup[checks,"ID",{}];expectedIDs=Flatten[Lookup[expectedCatalog["by_section"],sectionsRun,{}]];failures=Select[checks,!TrueQ[#["Passed"]]&];
 $LastReport=<|"Version"->"pentagon_code_v003","Manuscript"->"pentagon_v005.tex",
   "SourceSHA256"->inputIdentity,
   "KernelVersion"->$Version,"SectionsRequested"->selected,"SectionsRun"->sectionsRun,
   "SectionsNotRun"->Complement[$sectionNames,sectionsRun],"Checks"->checks,
   "Total"->Length[checks],"Failed"->Length[failures],"ElapsedSeconds"->(AbsoluteTime[]-started),
   "AllRequestedChecksPassed"->(Length[checks]>0&&failures==={}&&DuplicateFreeQ[allIDs]&&
     Sort[allIDs]===Sort[expectedIDs]&&inputIdentity===sourceIdentity[]),
   "Scope"->"Supplementary exact identities and diagnostics; not a substitute for interval proof jobs."|>;
 Print["\nChecks: ",Length[checks],"; failures: ",Length[failures],"; passed: ",$LastReport["AllRequestedChecksPassed"]];
 If[failures=!={},Print["Failed IDs: ",Lookup[failures,"ID"]]];
 $LastReport
];
End[];EndPackage[];
