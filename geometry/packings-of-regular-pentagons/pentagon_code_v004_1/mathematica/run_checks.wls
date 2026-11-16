(* Standalone command-line entry point. The four companion files may live
   anywhere. --output is required: no parent-project path is assumed.
   Bash: wolframscript -file /path/to/mathematica/run_checks.wls --output /path/to/report.json
   --section NAME may be repeated. No sections means the entire suite. *)
scriptDirectory=DirectoryName[ExpandFileName[$InputFileName]];
args=$ScriptCommandLine;
values[flag_] := Module[{positions=Flatten[Position[args,flag]],answer={}},
 Do[If[p>=Length[args]||StringStartsQ[args[[p+1]],"--"],
   Print["Missing value after ",flag];Exit[2]];AppendTo[answer,args[[p+1]]],{p,positions}];answer];
If[MemberQ[args,"--help"],Print["Usage: wolframscript -file run_checks.wls --output REPORT.json [--section NAME ...]"];Exit[0]];
unknown=Complement[Select[args,StringQ[#]&&StringStartsQ[#,"--"]&],{"--output","--section"}];
If[unknown=!={},Print["Unknown options: ",unknown];Exit[2]];
outputs=values["--output"];sections=values["--section"];
If[Length[outputs]=!=1,Print["Supply exactly one --output REPORT.json. No report destination is assumed."];Exit[2]];
out=ExpandFileName[First[outputs]];
If[FileExistsQ[out],Print["Refusing to overwrite report: ",out];Exit[2]];
loaded=CheckAbort[Check[Get[FileNameJoin[{scriptDirectory,"PentagonChecks.wl"}]],$Failed],$Failed];
If[loaded===$Failed,Print["Could not load the standalone PentagonChecks component."];Exit[2]];
report=Check[PentagonChecks`RunChecks["Sections"->If[sections==={},All,sections]],$Failed];
If[!AssociationQ[report],Print["The check suite did not return a report: ",report];Exit[1]];
exported=PentagonChecks`ExportReport[out,report];
If[!StringQ[exported],Print["Could not save the report: ",exported];Exit[1]];
Exit[If[TrueQ[report["AllRequestedChecksPassed"]],0,1]];
