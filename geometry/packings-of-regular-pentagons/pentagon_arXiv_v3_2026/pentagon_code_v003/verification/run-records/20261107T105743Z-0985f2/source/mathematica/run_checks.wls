(* Wolfram command-line runner. This file locates its companion package from
   its own saved pathname, not from the shell's working directory.
   Example (shell, package root):
     wolframscript -file mathematica/run_checks.wls --output paper-checks.json
   --section NAME may be repeated; omit it for the complete suite. *)
scriptDirectory=DirectoryName[$InputFileName];
loaded=Check[Get[FileNameJoin[{scriptDirectory,"PentagonChecks.wl"}]],$Failed];
If[loaded===$Failed,Print["Could not load PentagonChecks.wl beside this script."];Exit[2]];
args=$ScriptCommandLine;
values[flag_] := Module[{positions=Flatten[Position[args,flag]],answer={}},
 Do[If[p>=Length[args]||StringStartsQ[args[[p+1]],"--"],
   Print["Missing value after ",flag];Exit[2]];AppendTo[answer,args[[p+1]]],{p,positions}];answer];
outputs=values["--output"];sections=values["--section"];
If[Length[outputs]>1,Print["Use --output once."];Exit[2]];
out=If[outputs==={},FileNameJoin[{DirectoryName[scriptDirectory],"verification","paper-checks.json"}],First[outputs]];
report=Check[PentagonChecks`RunChecks["Sections"->If[sections==={},All,sections]],$Failed];
If[!AssociationQ[report],Print["The check suite did not return a report: ",report];Exit[1]];
exported=PentagonChecks`ExportReport[out,report];
If[!StringQ[exported],Print["Could not save the report: ",exported];Exit[1]];
Exit[If[TrueQ[report["AllRequestedChecksPassed"]],0,1]];
