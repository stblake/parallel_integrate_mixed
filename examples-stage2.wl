(* ::Package:: *)

(* examples-stage2.wl -- exercises the stage-2 mechanisms of ParallelMixed.wl:
   norm search with all solutions, vanishing orders, deep residues (n = 1),
   elliptic torsion (division polynomials, Miller functions) and the residue
   at the hypertangent place at infinity.  Cases that need units or the
   certificates of stage 3 are listed with the outcome stage 2 must report.

     wolframscript -file examples-stage2.wl                                    *)

Get[FileNameJoin[{DirectoryName[$InputFileName], "ParallelMixed.wl"}]];
Needs["ParallelMixed`"];

ClearAll[x, t];
results = {};

checkIntegral[I0_, surface_, subs_, var_] := Module[{Is = I0 /. subs},
  AllTrue[{3/2, 2, 7/3}, Abs[N[(D[Is, var] - surface) /. var -> #, 30]] < 10^-20 &]];

run[label_, f_, T_, expect_, OptionsPattern[{"Surface" -> None, "Subs" -> {}, "Var" -> x, "Verbose" -> False}]] :=
  Module[{r, ok, t0 = AbsoluteTime[], dt},
    Print["\n### ", label];
    r = ParallelIntegrateMixed[f, T, "Verbose" -> OptionValue["Verbose"]];
    dt = AbsoluteTime[] - t0;
    If[expect === "integral",
      ok = ! ListQ[r];
      If[ok && OptionValue["Surface"] =!= None,
        ok = checkIntegral[r, OptionValue["Surface"], OptionValue["Subs"], OptionValue["Var"]]];
      Print[r],
      ok = ListQ[r] && StringStartsQ[ToString[r[[1]]], expect];
      Print[r]];
    AppendTo[results, {label, expect, ok, dt}];
    Print["--> ", If[ok, "PASS", "FAIL"], "  (", NumberForm[dt, {4, 1}], "s)"]];

q = x^2 + 1;

(* norm search: two residue divisors realised by y -+ I Sqrt[3] x and y -+ I x *)
qa = x^4 - x^2 + 1;
run["N1  int (x^2-1) sqrt(x^4-x^2+1)/((x^2+1)(x^4+1))  [norm search, k = 2 and k = 1]",
  {0, (x^2 - 1)/((x^2 + 1) (x^4 + 1))}, Tower[{x}, {{1, 0}}, qa], "integral",
  "Surface" -> (x^2 - 1) Sqrt[qa]/((x^2 + 1) (x^4 + 1)), "Verbose" -> True];

(* torsion: order 3 on y^2 = 1 - x^3 (tutorial Example 6) *)
run["T1  int dx/(x sqrt(1-x^3))  [torsion of order 3, division polynomial psi_3]",
  {0, 1/(x (1 - x^3))}, Tower[{x}, {{1, 0}}, 1 - x^3], "integral",
  "Surface" -> 1/(x Sqrt[1 - x^3]), "Verbose" -> True];

(* torsion: order 6 on the CM curve y^2 = x^3 - 1 (Guenther 1882); slow in SymPy *)
run["T2  Guenther: int x dx/((x^3+8) sqrt(x^3-1))  [six order-6 classes]",
  {0, x/((x^3 + 8) (x^3 - 1))}, Tower[{x}, {{1, 0}}, x^3 - 1], "integral",
  "Surface" -> x/((x^3 + 8) Sqrt[x^3 - 1]), "Verbose" -> True];

(* v_oo residue of a hypertangent top: certified non-elementary *)
run["V1  int tan(sqrt(x^2+1)) dx: not elementary (residue -y/x at v_oo)", {t, 0},
  Tower[{x, t}, {{1, 0}, {0, x (1 + t^2)/q}}, q], "not elementary", "Verbose" -> True];

(* deep residues + norm search + a unit: Chebyshev needs the unit of stage 3 *)
q4 = x^4 + 4 x^3 + 2 x^2 + 1;
N4 = 2 x^6 + 4 x^5 + 7 x^4 - 3 x^3 - x^2 - 8 x - 8;
run["C1  Chebyshev (with stage 3 loaded: computed)", {0, N4/((2 x^2 - 1)^2 q4)},
  Tower[{x}, {{1, 0}}, q4], "integral", "Surface" -> N4/((2 x^2 - 1)^2 Sqrt[q4]), "Verbose" -> True];

(* torsion realised, then a holomorphic remainder: the certificate is stage 3 *)
run["H1  int dx/((x-2) sqrt(x^3+1)): torsion realised, certified not elementary (stage 3)",
  {0, 1/((x - 2) (x^3 + 1))}, Tower[{x}, {{1, 0}}, x^3 + 1], "not elementary", "Verbose" -> True];

Print["\n", StringRepeat["=", 78]];
Do[Print[PaddedForm[r[[1]], 70], "  ", r[[2]], "  ", If[r[[3]], "PASS", "FAIL"], "  ", NumberForm[r[[4]], {5, 1}], "s"], {r, results}];
Print[StringRepeat["=", 78]];
Print[Count[results, {_, _, True, _}], "/", Length[results], " passed"];
