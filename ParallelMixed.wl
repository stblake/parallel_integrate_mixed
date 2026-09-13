(* ::Package:: *)

(* ParallelMixed.wl -- stage 1 of the Wolfram Language port of parallel_mixed.py

   Parallel (Risch-Norman) integration over a simple radical y^2 = q sitting
   anywhere in a tower of transcendental generators, after

     S. Blake, Parallel Integration over Simple Radical Extensions II: Mixed Towers.

   Elements of L = K(y) are pairs {a, b} = a + b y.  The tower is
     Tower[gens, derivs, q]   with derivs[[i]] = D(gens[[i]]) as a pair,
   q = None for m = 1 (no radical).

   Stage 1 covers: pair arithmetic, the derivation, valuations and the
   classification (normal/special, delta_P), Hermite denominators, exact-order
   residues on every sheet with the exact constancy certificate, the quadratic
   y-split, tower specials, the ansatz and the linear system, and verification.
   Stage 2 adds the norm search, vanishing orders, deep residues (n = 1),
   elliptic torsion (division polynomials, Miller functions) and the v_oo
   residue.  Units and the certificates of stage 3 still return "failed".

   The function names are the Python names in CamelCase; the verbose trace
   lines are the same, so sessions can be compared between the two.          *)

BeginPackage["ParallelMixed`"];

Tower::usage = "Tower[gens, derivs, q] builds the differential tower L = F(gens)(y), y^2 = q, over which ParallelIntegrateMixed works.
  gens   -- list of generator symbols {t1, ..., tn}; t1 = x is the base variable and must satisfy D(x) = 1.
  derivs -- list of pairs {a, b}, one per generator, giving D(ti) = a + b y with a, b rational functions of the generators. The pair for x is {1, 0}. Generators above the radical may have b != 0 (their derivatives involve y): this is the 'mixed' setting.
  q      -- the radicand, a squarefree polynomial in the generators (usually in x alone); omit it, or pass None, for m = 1 (a purely transcendental tower, e.g. after a pure root has been flattened into the basis).
The result is an Association with keys \"gens\", \"derivs\", \"q\" and, when q is present, \"Dy\" = D(y) as a pair, computed from Dq = Q0 + Q1 y as Dy = Dq/(2y) = Q1/2 + (Q0/(2q)) y.";

TowerD::usage = "TowerD[T, u] is the derivation of the tower T applied to the pair u = {a, b} = a + b y, returned as a pair. It is the sum of D applied coefficientwise to a and b (through every generator, using the chain rule with T[\"derivs\"]) and of b D(y), with y^2 = q used to keep the result on the basis {1, y}.";

ClassifyPrime::usage = "ClassifyPrime[T, p] classifies the height-one primes of the working ring lying over the irreducible polynomial p (Definition 4.3 of the paper) and returns {branch, eta, delta, special}:
  branch  -- True if p divides the radicand q (the primes over p are ramified, e_P = 2);
  eta     -- the order of the denominator divisor of D at P: eta = max(0, -v_P(D t_i), -v_P(D y));
  delta   -- the pole order of the derivation, delta = 1 + eta, so that v_P(D g) = v_P(g) - delta for v_P(g) != 0 at a normal prime (the valuation lemma);
  special -- True if P is special (v_P(D pi) > -eta for the uniformiser pi = p, or pi = y at a branch prime), False if P is normal. Special primes are carried as candidate logands and may appear in the denominator of the integral with a guessed exponent; normal primes obey the valuation lemma and carry residues.";

CertifyNonconstant::usage = "CertifyNonconstant[tau, gens] decides exactly whether a residue tau -- an element of the residue field kappa(P), given as an expression in the generators, algebraic numbers and at most one algebraic function Sqrt[A] -- lies outside the constant field Fbar. It returns
  True      -- tau is certified NOT to be a constant (this is the residue certificate of non-elementarity, Proposition 9.2(a));
  False     -- tau is a constant, possibly in disguise (e.g. (x + Sqrt[x^2+1]) (x - Sqrt[x^2+1]));
  Undecided -- the expression contains more than one algebraic function, or a non-square-root algebraic function, and no verdict is issued.
The decision reduces tau to the canonical form (a + b Sqrt[A]) / D0 with a, b, D0 rational in the generators; tau is constant iff b = 0 and a/D0 is free of the generators. A constant-in-disguise must never be mistaken for an obstruction, so a syntactic free-variable test is not used.";

ParallelIntegrateMixed::usage = "ParallelIntegrateMixed[integrand, x, opts] integrates an expression in x built from rational operations, one square root of a polynomial (the radical y^2 = q), pure roots that flatten (Lemma 3.2: a root whose base is linear in a generator with a constant coefficient, such as Sqrt[x], Sqrt[x + Log[x]], (x + Exp[x])^(1/3), Sqrt[Log[x]]), and logarithms, exponentials and tangents of expressions in the field generated so far. The tower is constructed automatically (BuildTower), the integral computed by the pair form below, and the result returned in terms of x. Option \"Verify\" -> True additionally checks D[result, x] against the integrand numerically at three points.
ParallelIntegrateMixed[{f0, f1}, T, opts] integrates f = f0 + f1 y over the tower T by the parallel (Risch-Norman) method of the paper (Algorithm 4), with y = Sqrt[q]. It returns one of
  an expression in the generators and Sqrt[q]   -- the integral, verified inside the routine by re-differentiation;
  {\"not elementary\", p, tau}                    -- certified: the residue tau at a normal prime over p is not a constant (Proposition 9.2(a));
  {\"failed\", reason, ...}                       -- no verdict: the reason names the guessed input in play (in stage 1 also the mechanisms not yet ported: norm search, torsion, deep residues, units, the place at infinity, the holomorphic-remainder certificate).
Options: \"SplitSpecials\" -> Automatic (default) retries a failed system with every special prime split into its linear factors over the algebraic closure, each with its own coefficient (needed e.g. for Sqrt[Tan[x]]); True always splits, False never; \"Bounds\" -> {b1, ..., bn} fixes the degree bounds of the numerator of the rational part in each generator (default: maximal degree occurring + 2); \"Verbose\" -> True prints the classification of every prime, the residues on every sheet, the candidate logands and the special primes, in the same format as the SymPy implementation so sessions can be compared.
Steps (Algorithm 4): factor the denominator of f; for each prime, ClassifyPrime; specials become candidate logands and denominator factors; normal primes with a pole deeper than delta contribute Hermite factors to the denominator; normal primes with a pole of order exactly delta carry residues, computed on every sheet, certified constant or not, and realised as logands (equal residues -> the polynomial p; residues split by the curve -> the quadratic y-split); then the tower specials are added, the residual f - Sum c_i D u_i / u_i is formed, and the linear system for the rational part and the unknown logand coefficients is solved.";

BuildTower::usage = "BuildTower[integrand, x] constructs the differential tower for a surface expression. Returns {T, {f0, f1}, back, Y}: the Tower T, the integrand as a pair f0 + f1 y on T, the list of back-substitution rules mapping the generator symbols (and flattened roots) to their surface expressions in x, and the symbol Y used for y during the conversion. Processing is innermost-first: Log[a] -> new generator t with D t = D a / a; Exp[a] -> t with D t = t D a; Tan[a] -> t with D t = (1 + t^2) D a; a root base^(k/m) whose base is c g + r with g a generator, c a constant and r free of g is flattened, g -> (u^m - r)/c, D u = D(base)/(m u^(m-1)); any other root base^(k/m) with polynomial base and m = 2 becomes the radical y^2 = base. Fails with a message if two distinct unflattenable radicals occur, if a root has m > 2, or if a radicand is not a squarefree polynomial.";
BuildTower::radicals = "More than one unflattenable radical (`1` and `2`); the implementation handles one simple radical.";
BuildTower::degree = "The root `1` has degree `2` > 2 and does not flatten; the implementation handles m <= 2.";
BuildTower::radicand = "The radicand `1` is not a squarefree polynomial in the generators.";
BuildTower::residual = "Could not reduce the integrand to a rational function of the generators and y: `1`.";
Undecided;

Begin["`Private`"];

(* ------------------------------------------------------------ pair arithmetic *)
(* Can[e]
   Canonical form of a rational function with algebraic-number coefficients:
   Together followed by Cancel with Extension -> Automatic, so that common
   factors are removed exactly even when the coefficients involve I, Sqrt[3],
   Root objects, etc.  Every pair operation runs its results through Can; it
   is the counterpart of SymPy's cancel(..., extension=True), the step that
   made the algebraic-number-heavy examples (Guenther) tractable.            *)
Can[e_] := Cancel[Together[e], Extension -> Automatic];
(* Padd[u, v], Pscale[s, u], Pmul[u, v, q], Pdiv[u, v, q]
   Arithmetic in L = K(y), y^2 = q, on pairs {a, b} = a + b y.
     Padd     componentwise sum;
     Pscale   multiplication by a scalar s of K;
     Pmul     (a0 + a1 y)(b0 + b1 y) = (a0 b0 + a1 b1 q) + (a0 b1 + a1 b0) y;
     Pdiv     u / v = u * conj(v) / N(v) with conj(v) = v0 - v1 y and the norm
              N(v) = v0^2 - q v1^2 in K (so the quotient is again a pair).
   For m = 1 (q = None) the second component is identically 0 and only Padd
   and Pscale are used.                                                      *)
Padd[u_, v_] := Can /@ (u + v);
Pscale[s_, u_] := Can /@ (s u);
Pmul[u_, v_, q_] := {Can[u[[1]] v[[1]] + u[[2]] v[[2]] q], Can[u[[1]] v[[2]] + u[[2]] v[[1]]]};
Pdiv[u_, v_, q_] := Module[{nrm = Can[v[[1]]^2 - q v[[2]]^2], w},
  w = Pmul[u, {v[[1]], -v[[2]]}, q];
  {Can[w[[1]]/nrm], Can[w[[2]]/nrm]}];

(* ------------------------------------------------------------ the tower *)
(* Tower[gens, derivs, q]  -- see the usage message.
   Internally: the derivative pairs are normalised with Can, and when q is
   present the pair Dy is stored so that TowerD can differentiate y without
   recomputing Dq each time.                                                 *)
Tower[gens_List, derivs_List, q_: None] := Module[{T, Q},
  T = <|"gens" -> gens, "derivs" -> (Can /@ # & /@ derivs), "q" -> q|>;
  If[q =!= None,
    Q = Dhat[T, q];                           (* Dq = Q0 + Q1 y *)
    T = Append[T, "Dy" -> {Can[Q[[2]]/2], Can[Q[[1]]/(2 q)]}]  (* Dy = Dq/(2y) = Q1/2 + Q0 y/(2q) *)
  ];
  T];

(* Dhat[T, c]
   The derivation applied to a scalar c of K (a rational function of the
   generators, no y): D c = Sum_i (d c / d t_i) D(t_i), a pair since the
   D(t_i) are pairs.  This is the chain rule over the tower; the result can
   have a y-component when some generator above the radical differentiates
   through y.                                                                *)
Dhat[T_, c_] := Module[{out = {0, 0}},
  Do[out = Padd[out, Pscale[D[c, T["gens"][[i]]], T["derivs"][[i]]]], {i, Length[T["gens"]]}];
  out];

(* TowerD[T, u]  -- see the usage message.
   D(a + b y) = D a + (D b) y + b D y, assembled with Pmul so that the
   product (D b) y is reduced modulo y^2 = q.                                *)
TowerD[T_, u_] := Module[{out, h1},
  out = Dhat[T, u[[1]]];
  If[T["q"] === None, Return[out]];
  h1 = Dhat[T, u[[2]]];
  out = Padd[out, Pmul[h1, {0, 1}, T["q"]]];
  Padd[out, Pscale[u[[2]], T["Dy"]]]];

(* ------------------------------------------------------------ valuations *)
(* Mult[poly, p, gens]
   Multiplicity of the irreducible polynomial p in the polynomial poly, by
   repeated exact division (PolynomialReduce with the single divisor p, whose
   remainder vanishes iff p divides).  Returns Infinity for poly = 0.       *)
Mult[poly_, p_, gens_] := Module[{m = 0, P = Expand[poly], qr},
  If[P === 0, Return[Infinity]];
  While[True,
    qr = PolynomialReduce[P, {p}, gens];
    If[qr[[2]] =!= 0, Return[m]];
    m++; P = qr[[1, 1]]]];

(* Vp[expr, p, gens]
   The p-adic valuation v_p on K = F(gens): multiplicity of p in the numerator
   minus multiplicity in the denominator of the cancelled expression;
   Infinity for 0.                                                           *)
Vp[expr_, p_, gens_] := Module[{e = Can[expr], n, d},
  If[e === 0, Return[Infinity]];
  {n, d} = {Numerator[e], Denominator[e]};
  Mult[n, p, gens] - Mult[d, p, gens]];

(* VP[u, p, T, branch]
   The valuation at the primes P of the working ring over p of the pair
   u = a + b y (Lemma 4.4 of the paper, m = 2, q squarefree):
     unramified (p does not divide q):  v_P(u) = min(v_p(a), v_p(b));
     branch     (p divides q):          v_P(u) = min(2 v_p(a), 2 v_p(b) + 1),
   since then v_P(p) = 2 and v_P(y) = 1, so a and b y have valuations of
   different parity and cannot cancel.  For m = 1 it is v_p(a).             *)
VP[u_, p_, T_, branch_] := Module[{g = T["gens"]},
  If[T["q"] === None, Return[Vp[u[[1]], p, g]]];
  If[! branch, Min[Vp[u[[1]], p, g], Vp[u[[2]], p, g]],
               Min[2 Vp[u[[1]], p, g], 2 Vp[u[[2]], p, g] + 1]]];

(* Eta[T, p, branch]
   The order at P of the denominator divisor of the derivation:
   eta_P = max(0, -v_P(D t_i) over the generators, -v_P(D y)).  Together with
   the normality test this is Definition 4.3 in computable form; the pole
   order of D at a normal P is delta_P = 1 + eta_P.                          *)
Eta[T_, p_, branch_] := Module[{vals},
  vals = -VP[#, p, T, branch] & /@ T["derivs"];
  If[T["q"] =!= None, AppendTo[vals, -VP[T["Dy"], p, T, branch]]];
  Max[Prepend[Select[vals, NumericQ[#] && # =!= -Infinity &], 0]]];

(* ClassifyPrime[T, p]  -- see the usage message.
   The uniformiser used in the normality test is pi = p at an unramified
   prime and pi = y at a branch prime (where v_P(y) = 1); P is normal iff
   v_P(D pi) = -eta_P, i.e. eta_P + v_P(D pi) = 0, and special iff the sum is
   >= 1 (D pi vanishes to higher order than the denominator divisor allows). *)
ClassifyPrime[T_, p_] := Module[{branch, eta, pi, special},
  branch = T["q"] =!= None && Vp[T["q"], p, T["gens"]] > 0;
  eta = Eta[T, p, branch];
  pi = If[branch, {0, 1}, {p, 0}];            (* uniformiser: y or p *)
  special = eta + VP[TowerD[T, pi], p, T, branch] >= 1;
  {branch, eta, 1 + eta, special}];

(* ------------------------------------------------------------ residues *)
(* places over p: {g, rho, yval} with yval = None for m = 1 *)
(* PointsOver[T, p]
   The places of the curve over the prime p, for the residue computation.
   Looks for a generator g in which p is a polynomial with coefficients free
   of g, solves p = 0 for g (any degree; Solve may return Root objects), and
   for each root rho returns the two sheets {g, rho, +r} and {g, rho, -r}
   with r = Sqrt[q(rho)] simplified by PowerExpand (the sign convention of
   SymPy's positive symbols).  For m = 1 the third entry is None.  Returns
   None if p has no such generator direction.                               *)
PointsOver[T_, p_] := Module[{gens = T["gens"], g, cl, roots, qbar, r, pts},
 Catch[
  Do[g = gens[[i]];
    If[PolynomialQ[p, g] && Exponent[p, g] >= 1 &&
       FreeQ[CoefficientList[p, g], g],
      roots = g /. Solve[p == 0, g];
      pts = {};
      Do[If[T["q"] === None, AppendTo[pts, {g, rho, None}],
          qbar = Can[T["q"] /. g -> rho];
          r = PowerExpand[Sqrt[Factor[qbar]]];
          AppendTo[pts, {g, rho, r}]; AppendTo[pts, {g, rho, -r}]],
        {rho, roots}];
      Throw[pts, "pts"]],
    {i, Length[gens]}];
  None, "pts"]];

(* ReduceAt[expr, pt, Y]
   Evaluates an expression in the generators and the symbol Y (standing for
   y) at the place pt = {g, rho, yval}: substitutes Y -> yval, cancels, then
   substitutes g -> rho and simplifies.  The result is an element of the
   residue field kappa(P), expressed in the remaining generators.           *)
ReduceAt[expr_, pt_, Y_] := Module[{g, rho, yv, e},
  {g, rho, yv} = pt; e = expr;
  If[yv =!= None, e = e /. Y -> yv];
  Simplify[Can[e] /. g -> rho]];

(* ResFmt[v]
   Presentation of a residue: Simplify, and RootReduce when the value is a
   pure algebraic number (RootReduce is not applied to expressions containing
   the generators).                                                          *)
ResFmt[v_] := With[{s = Simplify[v]}, If[NumericQ[s], RootReduce[s], s]];

(* exact decision of tau \[Element] Fbar inside kappa(P): canonical form a + b Sqrt[A] *)
(* CertifyNonconstant[tau, gens]  -- see the usage message.
   Implementation: collect the powers with generator-dependent bases; refuse
   (Undecided) any exponent other than an integer or a half-integer, or more
   than one distinct square-root base A.  With no algebraic function the test
   is on the numerator and denominator of Can[tau].  With one, substitute
   Sqrt[A] -> S, reduce numerator and denominator modulo S^2 - A, multiply by
   the conjugate of the denominator so that D0 is free of S, and read off
   a + b S.  If A is itself a perfect square in F(gens) the expression was
   rational after all and the test recurses on (a + b r)/D0.               *)
CertifyNonconstant[tau0_, gens_] := Module[{tau, G, pows, algs, A, S, e, n, d, red, nn, dd, dbar, NN, D0, a, b, r, isSq},
  G = Alternatives @@ gens;
  tau = Together[tau0];
  If[FreeQ[tau, G], Return[False]];
  pows = Cases[{tau}, Power[base_, ex_] /; ! FreeQ[base, G], Infinity];
  If[AnyTrue[pows, ! (IntegerQ[#[[2]]] || Denominator[#[[2]]] == 2) &], Return[Undecided]];
  algs = DeleteDuplicates[Cases[pows, Power[base_, ex_] /; Denominator[ex] == 2 :> base]];
  If[algs === {},
    e = Can[tau];
    Return[! FreeQ[Numerator[e], G] || ! FreeQ[Denominator[e], G]]];
  If[Length[algs] =!= 1, Return[Undecided]];
  A = First[algs]; S = Unique["S"];
  e = tau /. Sqrt[A] -> S /. Power[A, -1/2] -> 1/S;
  e = Together[e]; {n, d} = {Numerator[e], Denominator[e]};
  red[z_] := PolynomialRemainder[Expand[z], S^2 - A, S];
  {nn, dd} = {red[n], red[d]};
  dbar = dd /. S -> -S;
  NN = red[Expand[nn dbar]]; D0 = red[Expand[dd dbar]];
  If[! FreeQ[D0, S], Return[Undecided]];
  a = NN /. S -> 0; b = Coefficient[Expand[NN], S, 1];
  r = PowerExpand[Sqrt[Factor[A]]];
  isSq = FreeQ[r, Power[base_, ex_] /; Denominator[ex] == 2 && ! FreeQ[base, G]];
  If[isSq, Return[CertifyNonconstant[Cancel[(a + b r)/D0], gens]]];
  If[Can[b/D0] =!= 0, Return[True]];
  CertifyNonconstant[Cancel[a/D0], gens]];

(* ------------------------------------------------------------ the algorithm *)


(* ============================================================ stage 2 ===== *)

(* IsZero[v]
   Exact zero test.  For algebraic constants RootReduce canonicalises
   (Sqrt[-I] - (1 - I)/Sqrt[2] -> 0, which Simplify alone misses); for
   expressions with free symbols Simplify is used.                           *)
IsZero[v_] := With[{w = Together[v]}, If[NumericQ[w], RootReduce[w] === 0, Simplify[w] === 0]];

(* RR[e]
   RootReduce for algebraic numbers, Together otherwise: the canonical form
   used for the coordinates in the group law and the Miller loop.          *)
RR[e_] := If[NumericQ[e], RootReduce[e], Together[e]];

(* NormSearchAll[q, p, g, kmax, dbmax]
   Every u = a + b y with a^2 - q b^2 = c p^k of small degree, b monic of
   degree db <= dbmax, 1 <= k <= kmax (Algorithm 3(c)).  Returns a list of
   {a, b, c, k}.  Different solutions vanish on different subsets of the
   places over p, so the realisation tries them all.                        *)
NormSearchAll[q_, p_, g_, kmax_: 2, dbmax_: 2] := Module[{dq, dp, out = {}, da, ac, bc, c, a, b, eq, sols},
  dq = Exponent[q, g]; dp = Exponent[p, g];
  Do[da = Quotient[Max[dq + 2 db, k dp] + 1, 2];
    ac = Table[na[i], {i, 0, da}]; bc = Table[nb[i], {i, 0, db - 1}]; c = nc;
    a = ac . g^Range[0, da];
    b = If[db == 0, 1, bc . g^Range[0, db - 1] + g^db];
    eq = Expand[a^2 - q b^2 - c p^k];
    sols = Quiet[Solve[Thread[CoefficientList[eq, g] == 0], Join[ac, bc, {c}]]];
    Do[With[{aa = Expand[a /. s], bb = Expand[b /. s], cc = c /. s},
        If[cc =!= 0 && FreeQ[aa, Alternatives @@ Join[ac, bc, {c}]] && NumericQ[cc],
          AppendTo[out, {aa, bb, cc, k}]]],
      {s, sols}],
    {k, 1, kmax}, {db, 0, dbmax}];
  out];

(* SheetSign[T, pt]
   For a place pt = {g, rho, yv} with constant coordinates, the sign eps
   with yv = eps Sqrt[q(rho)], decided exactly; None if neither sign matches.*)
SheetSign[T_, pt_] := Module[{g, rho, yv, r},
  {g, rho, yv} = pt; r = Sqrt[T["q"] /. g -> rho];
  Which[IsZero[yv - r], 1, IsZero[yv + r], -1, True, None]];

(* VanishOrder[T, u, pt, Y]
   Order of vanishing of the pair u = a + b y at a place with constant
   coordinates, by the series of u(rho + e, eps Sqrt[q(rho + e)]) in the
   base generator (1 if the place has non-constant coordinates).           *)
VanishOrder[T_, u_, pt_, Y_] := Module[{g, rho, yv, eps, e, ub, k = 0},
  {g, rho, yv} = pt;
  If[! FreeQ[rho, Alternatives @@ T["gens"]] || ! FreeQ[T["q"], Alternatives @@ DeleteCases[T["gens"], g]], Return[1]];
  eps = SheetSign[T, pt];
  If[eps === None, Return[1]];
  ub = (u[[1]] + u[[2]] eps Sqrt[T["q"] /. g -> rho + e]) /. g -> rho + e;
  While[k < 8 && IsZero[SeriesCoefficient[ub, {e, 0, k}]], k++];
  k];

(* DeepResidues[T, f, p, pts, Y]
   Laurent residues at a delta = 1 normal prime with a pole of order >= 2
   (Proposition 7.6 in the case where D acts trivially on the coefficient
   field: n = 1, D = d/dx).  The coefficient of e^-1 of f(rho + e, eps
   Sqrt[q(rho + e)]) at each place.                                         *)
DeepResidues[T_, f_, p_, pts_, Y_] := Module[{g = T["gens"][[1]], e, out = {}, eps, floc},
  Do[eps = SheetSign[T, pt];
    If[eps === None, AppendTo[out, Undecided]; Continue[]];
    floc = (f[[1]] + f[[2]] eps Sqrt[T["q"] /. g -> pt[[2]] + e]) /. g -> pt[[2]] + e;
    AppendTo[out, ResFmt[SeriesCoefficient[floc, {e, 0, -1}]]],
    {pt, pts}];
  out];

(* EllOps[q, g]
   Chord-and-tangent group law on y^2 = q(g), deg q = 3, after normalising
   to the monic model X = c3 g, Ytil = c3 y: Ytil^2 = X^3 + c2 X^2 + c1 c3 X
   + c0 c3^2.  Returns {toM, add}: toM maps a point (g, y) to the model and
   add is the group law with the identity represented by None.             *)
EllOps[q_, g_] := Module[{c, c3, toM, add},
  c = PadLeft[Reverse[CoefficientList[q, g]], 4];       (* {c3, c2, c1, c0} *)
  c3 = c[[1]];
  toM = Function[P, {RR[c3 P[[1]]], RR[c3 P[[2]]]}];
  add = Function[{P, Q}, Module[{x1, y1, x2, y2, lam, x3},
    If[P === None, Return[Q]]; If[Q === None, Return[P]];
    {x1, y1} = P; {x2, y2} = Q;
    If[IsZero[x1 - x2],
      If[IsZero[y1 + y2], Return[None]];
      lam = RR[(3 x1^2 + 2 c[[2]] x1 + c[[3]] c3)/(2 y1)],
      lam = RR[(y2 - y1)/(x2 - x1)]];
    x3 = RR[lam^2 - c[[2]] - x1 - x2];
    {x3, RR[lam (x1 - x3) - y1]}]];
  {toM, add}];

(* DivisionPolyOrder[A, B, X0, Y0, Nmax]
   Order of the point (X0, Y0) on Ytil^2 = X^3 + A X + B if it is <= Nmax,
   else None: the division polynomials psi_n are built by the standard
   recursion with Ytil^2 reduced, and n P = O iff psi_n(P) = 0.            *)
DivisionPolyOrder[A_, B_, X0_, Y0_, Nmax_: 24] := Module[{X, yv, psi, red, get, n},
  red[e_] := PolynomialRemainder[Expand[e], yv^2 - (X^3 + A X + B), yv];
  psi[0] = 0; psi[1] = 1; psi[2] = 2 yv;
  psi[3] = 3 X^4 + 6 A X^2 + 12 B X - A^2;
  psi[4] = 4 yv (X^6 + 5 A X^4 + 20 B X^3 - 5 A^2 X^2 - 4 A B X - 8 B^2 - A^3);
  get[m_] := get[m] = With[{h = Quotient[m, 2]},
    If[OddQ[m],
      red[get[h + 2] get[h]^3 - get[h - 1] get[h + 1]^3],
      red[Cancel[get[h] (get[h + 2] get[h - 1]^2 - get[h - 2] get[h + 1]^2)/(2 yv)]]]];
  Do[get[k] = psi[k], {k, 0, 4}];
  n = SelectFirst[Range[2, Nmax], IsZero[get[#] /. {X -> X0, yv -> Y0}] &, None];
  n];

(* TorsionRealise[T, p, pts, taus, Y, bound, verbose]
   Realisation of a residue divisor by torsion on an elliptic curve with one
   place at infinity (deg q = 3, constant coordinates), Algorithm 3(d): the
   order mu of [P - oo] is certified by the division polynomials (fallback:
   repeated addition), the Miller function with divisor mu P - mu oo is
   built by the additive loop h_{k+1} = h_k line(kP, P) / vert((k+1)P), and
   the logand is recorded with coefficient tau/mu.  Returns a list of
   {coefficient, pair} or None.                                             *)
TorsionRealise[T_, p_, pts_, taus_, Y_, bound_: 24, verbose_: False] := Catch[Module[
  {g, q, toM, add, c, c3, X0, out = {}, P, m, kP, fnum, fden, x1, y1, lam, line, num, u0, u1, pt, tau},
  g = pts[[1, 1]]; q = T["q"];
  If[Exponent[q, g] =!= 3 || ! FreeQ[q, Alternatives @@ DeleteCases[T["gens"], g]], Throw[None, "tors"]];
  If[AnyTrue[pts, ! FreeQ[{#[[2]], #[[3]]}, Alternatives @@ T["gens"]] &], Throw[None, "tors"]];
  {toM, add} = EllOps[q, g];
  c = PadLeft[Reverse[CoefficientList[q, g]], 4]; c3 = c[[1]];
  X0 = c3 g;
  Do[pt = pts[[i]]; tau = taus[[i]];
    If[tau === 0, Continue[]];
    P = toM[{pt[[2]], pt[[3]]}];
    m = If[c[[2]] === 0, DivisionPolyOrder[c[[3]] c3, c[[4]] c3^2, P[[1]], P[[2]], bound], None];
    If[verbose && m =!= None, Print["      (order ", m, " certified by the division polynomial psi_", m, ")"]];
    If[m === None,
      kP = P;
      Do[kP = add[kP, P]; If[kP === None, m = k; Break[]], {k, 2, bound}]];
    If[m === None, Throw[None, "tors"]];
    fnum = 1; fden = 1; kP = P;
    Do[{x1, y1} = kP;
      Which[
        IsZero[x1 - P[[1]]] && IsZero[y1 - P[[2]]],
          lam = RR[(3 x1^2 + 2 c[[2]] x1 + c[[3]] c3)/(2 y1)];
          line = c3 Y - y1 - lam (X0 - x1); kP = add[kP, P]; fnum *= line;
          If[kP =!= None, fden *= (X0 - kP[[1]])],
        IsZero[x1 - P[[1]]],
          fnum *= (X0 - x1); kP = add[kP, P],
        True,
          lam = RR[(P[[2]] - y1)/(P[[1]] - x1)];
          line = c3 Y - y1 - lam (X0 - x1); kP = add[kP, P]; fnum *= line;
          If[kP =!= None, fden *= (X0 - kP[[1]])]],
      {k, 1, m - 1}];
    num = PolynomialRemainder[Expand[fnum], Y^2 - q, Y];
    u0 = Can[(num + (num /. Y -> -Y))/2/fden];
    u1 = Can[(num - (num /. Y -> -Y))/(2 Y)/fden];
    AppendTo[out, {Simplify[tau/m], {u0, u1}}];
    If[verbose, Print["      torsion: [P - oo] of order ", m, " at (", pt[[2]], ", ", pt[[3]], "); Miller logand with coefficient ", Simplify[tau/m]]],
    {i, Length[pts]}];
  out], "tors"];

(* RealisePoints[T, p, pts, taus, Y, verbose]
   Realisation of the residues taus at the places pts over a prime p that
   neither the polynomial p nor the y-split realises: try every norm-search
   solution u = a +- b y, accept the first whose vanishing set carries a
   constant ratio tau_P / ord_P(u) (the logand coefficient), and otherwise
   fall back to TorsionRealise.  Returns a list of {coefficient, pair} or
   None.                                                                    *)
RealisePoints[T_, p_, pts_, taus_, Y_, verbose_: False] := Catch[Module[{g, out, ok, uu, hits, gammas, a, b, c, k},
  g = pts[[1, 1]];
  Do[{a, b, c, k} = sol; out = {}; ok = True;
    Do[uu = {a, sg b};
      hits = Pick[Transpose[{pts, taus}], IsZero[ReduceAt[uu[[1]] + uu[[2]] Y, #, Y]] & /@ pts, True];
      gammas = Simplify[#[[2]]/VanishOrder[T, uu, #[[1]], Y]] & /@ hits;
      If[gammas === {} || ! AllTrue[gammas, IsZero[# - gammas[[1]]] &], ok = False; Break[]];
      If[gammas[[1]] =!= 0, AppendTo[out, {gammas[[1]], uu}]],
      {sg, {1, -1}}];
    If[ok,
      If[verbose, Do[Print["      norm factor ", o[[2, 1]], " + (", o[[2, 2]], ")*y (N = ", c, "*(", p, ")^", k, "): coefficient ", o[[1]]], {o, out}]];
      Throw[out, "realise"]],
    {sol, NormSearchAll[T["q"], p, g]}];
  TorsionRealise[T, p, pts, taus, Y, 24, verbose]], "realise"];

(* VinftyResidue[T, f, Y]
   Residue at the place v_oo of a hypertangent top generator t with
   D t = eta (1 + t^2) (Lemma 8.1): delta = 1, uniformiser 1/t, and for
   v_oo(f) = -1 the residue is tau = -(lim f/t)/eta, an element of
   kappa(v_oo) = K_{n-1}(y) returned as a pair.  None if the top generator
   is not hypertangent or v_oo(f) != -1 (deeper poles need the reduction of
   Proposition 7.6 with D acting on the coefficients).                      *)
VinftyResidue[T_, f_, Y_] := Module[{t, a, b, ea, eb, vinf, lead, vs, cpair, tau},
  t = Last[T["gens"]]; {a, b} = Last[T["derivs"]];
  ea = Can[a/(1 + t^2)]; eb = Can[b/(1 + t^2)];
  If[! FreeQ[ea, t] || ! FreeQ[eb, t] || (ea === 0 && eb === 0), Return[None]];
  vinf[cc_] := With[{c = Can[cc]}, If[c === 0, None, Exponent[Denominator[c], t] - Exponent[Numerator[c], t]]];
  vs = DeleteCases[{vinf[f[[1]]], vinf[f[[2]]]}, None];
  If[vs === {} || Min[vs] =!= -1, Return[None]];
  lead[cc_] := With[{c = Can[cc]}, If[c === 0 || vinf[c] =!= -1, 0,
    Can[Coefficient[Numerator[c], t, Exponent[Numerator[c], t]]/Coefficient[Denominator[c], t, Exponent[Denominator[c], t]]]]];
  cpair = {lead[f[[1]]], lead[f[[2]]]};
  tau = Pdiv[cpair, {ea, eb}, T["q"]];
  {Can[-tau[[1]]], Can[-tau[[2]]]}];


(* ---------------------------------------------------------- automatic towers *)

(* RadRules[q, Y]
   Rewriting rules sending every half-integral power of the radicand q to the
   basis element Y: q^(k + 1/2) -> q^k Y (so 1/Sqrt[q] -> Y/q).            *)
RadRules[q_, Y_] := {Power[q, r_Rational] /; Denominator[r] == 2 :> q^(r - 1/2) Y};

(* ToPair[expr, Y, q]
   The pair {a, b} = a + b y of an expression rational in the generators and
   Y, Y^2 = q: numerator and denominator are reduced modulo Y^2 - q, the
   denominator is rationalised by its conjugate, and the two coefficients are
   read off.  For q = None the expression must be free of Y and the pair is
   {expr, 0}.                                                                *)
ToPair[expr_, Y_, q_] := Module[{e, n, d, dbar, nn, dd, red},
  If[q === None, Return[{Can[expr], 0}]];
  e = Together[expr];
  red[z_] := PolynomialRemainder[Expand[z], Y^2 - q, Y];
  n = red[Numerator[e]]; d = red[Denominator[e]];
  dbar = d /. Y -> -Y;
  nn = red[Expand[n dbar]]; dd = red[Expand[d dbar]];
  {Can[Coefficient[nn, Y, 0]/dd], Can[Coefficient[nn, Y, 1]/dd]}];

(* RationalQ[a, vars]
   True if a is a rational function of vars (numerator and denominator
   polynomials in vars, with any constant coefficients): the positive test
   for "innermost" subexpressions during the construction.  A negative test
   (free of Log, Tan, ...) would let an unknown function such as ArcTan[x]
   through as an opaque atom, which the linear solver would then treat as a
   constant and return a wrong integral.                                    *)
RationalQ[a_, vars_] := With[{e = Together[a]}, PolynomialQ[Numerator[e], vars] && PolynomialQ[Denominator[e], vars]];

(* Generator kinds handled by BuildTower: each h[a] becomes a generator t
   with the derivative pair listed, D a computed by the tower so far.
     Log      D a / a                    (primitive)
     ArcTan   D a / (1 + a^2)            (primitive)
     ArcTanh  D a / (1 - a^2)            (primitive)
     ArcSin   D a / Sqrt[1 - a^2]        (primitive through the radical y^2 = 1 - a^2)
     ArcCos  -D a / Sqrt[1 - a^2]
     ArcSinh  D a / Sqrt[1 + a^2]
     ArcCosh  D a / Sqrt[a^2 - 1]
     Exp      t D a                      (hyperexponential)
     Tan     (1 + t^2) D a               (hypertangent)
     Cot    -(1 + t^2) D a
     Tanh    (1 - t^2) D a
     Coth    (1 - t^2) D a
   Sin, Cos, Sinh, Cosh, Sec, Csc are not monomials and are rejected: rewrite
   them through Tan or Exp first.                                            *)
GenHeads = {Log, ArcTan, ArcTanh, ArcSin, ArcCos, ArcSinh, ArcCosh, Tan, Cot, Tanh, Coth};
BuildTower::function = "The function `1` is not a supported generator (rewrite Sin, Cos, Sinh, Cosh through Tan or Exp).";
BuildTower::radical2 = "The derivative of `1` needs the radical Sqrt[`2`], but the tower already has y^2 = `3`.";

(* BuildTower[integrand, x]  -- see the usage message. *)
BuildTower[integrand_, x_Symbol] := Module[
  {expr = integrand, gens = {x}, derivs = {{1, 0}}, q = None, Y, back = {}, T, cands, c, kind, arg,
   tnew, ap, Da, base, r, m, g, coef, rest, u, Dbase, pos, k = 0, fpair, rad},
  Y = Unique["Y"];
  T = Tower[gens, derivs, q];
  While[True,
    cands = Cases[{expr}, ((h_[a_] /; MemberQ[GenHeads, h]) | Power[E, a_] | Power[a_, _Rational]) /;
        RationalQ[a /. RadRules[q, Y], Join[gens, {Y}]] && ! FreeQ[a, Alternatives @@ Join[gens, {Y}]], Infinity];
    If[cands === {}, Break[]];
    c = First[SortBy[cands, LeafCount]];
    Switch[c,
      Power[E, _] | (h_[_] /; MemberQ[GenHeads, h]),
        arg = c[[If[Head[c] === Power, 2, 1]]];
        ap = ToPair[arg /. RadRules[q, Y], Y, q];
        Da = TowerD[T, ap];
        k++; tnew = Unique["t"];
        (* primitives through a radical: the radical must be the tower's *)
        If[MemberQ[{ArcSin, ArcCos, ArcSinh, ArcCosh}, Head[c]],
          rad = Expand[Switch[Head[c], ArcSin | ArcCos, 1 - arg^2, ArcSinh, 1 + arg^2, ArcCosh, arg^2 - 1] /. RadRules[q, Y]];
          If[q === None,
            If[! PolynomialQ[rad, gens], Message[BuildTower::radicand, rad]; Throw[$Failed, "build"]];
            q = rad; T = Tower[gens, derivs, q]; Da = TowerD[T, ap]; expr = expr /. RadRules[q, Y],
            If[Expand[rad - q] =!= 0, Message[BuildTower::radical2, c, rad, q]; Throw[$Failed, "build"]]]];
        AppendTo[gens, tnew];
        AppendTo[derivs, Switch[Head[c],
          Log,     Pdiv[Da, ap, q],
          ArcTan,  Pdiv[Da, ToPair[1 + arg^2 /. RadRules[q, Y], Y, q], q],
          ArcTanh, Pdiv[Da, ToPair[1 - arg^2 /. RadRules[q, Y], Y, q], q],
          ArcSin,  Pmul[Da, {0, 1/q}, q],
          ArcCos,  Pmul[Da, {0, -1/q}, q],
          ArcSinh, Pmul[Da, {0, 1/q}, q],
          ArcCosh, Pmul[Da, {0, 1/q}, q],
          Tan,     Pscale[1 + tnew^2, Da],
          Cot,     Pscale[-(1 + tnew^2), Da],
          Tanh,    Pscale[1 - tnew^2, Da],
          Coth,    Pscale[1 - tnew^2, Da],
          Power,   Pscale[tnew, Da]]];
        AppendTo[back, tnew -> c];
        expr = expr /. c -> tnew,
      Power[_, _Rational],
        {base, r} = List @@ c; m = Denominator[r];
        (* flattenable root: base = coef g + rest, coef constant, rest free of g  (Lemma 3.2) *)
        g = SelectFirst[gens, PolynomialQ[base, #] && Exponent[base, #] == 1 &&
                              FreeQ[Coefficient[base, #, 1], Alternatives @@ gens] &, None];
        If[g =!= None,
          coef = Coefficient[base, g, 1]; rest = base /. g -> 0;
          u = Unique["u"];
          Dbase = TowerD[T, ToPair[base /. RadRules[q, Y], Y, q]];
          pos = Position[gens, g][[1, 1]];
          gens = ReplacePart[gens, pos -> u];
          derivs = ReplacePart[derivs, pos -> Pscale[1/(m u^(m - 1)), Dbase]];
          derivs = derivs /. g -> (u^m - rest)/coef;
          If[q =!= None, q = Expand[q /. g -> (u^m - rest)/coef]];
          AppendTo[back, u -> base^(1/m)];
          expr = expr /. Power[base, rr_Rational] :> u^(m rr);   (* the root itself, before g is eliminated *)
          expr = expr /. g -> (u^m - rest)/coef,
          (* otherwise: the simple radical *)
          If[m > 2, Message[BuildTower::degree, c, m]; Throw[$Failed, "build"]];
          If[q =!= None && Expand[base - q] =!= 0, Message[BuildTower::radicals, q, base]; Throw[$Failed, "build"]];
          If[! (PolynomialQ[base, gens] && FreeQ[Exponent[PolynomialGCD[base, D[base, First[gens]]], First[gens]], _?(# > 0 &)]),
            Message[BuildTower::radicand, base]; Throw[$Failed, "build"]];
          q = base;
          expr = expr /. RadRules[q, Y]]];
    T = Tower[gens, derivs, q]];
  expr = expr /. RadRules[q, Y];
  If[! RationalQ[expr, Join[gens, {Y}]] || (q === None && ! FreeQ[expr, Y]),
    With[{fs = Cases[{expr}, h_[args___] /; ! MemberQ[{Plus, Times, Power, Rational, Complex, List}, h] && ! FreeQ[{args}, Alternatives @@ gens] :> h, Infinity]},
      If[fs =!= {}, Message[BuildTower::function, First[fs]], Message[BuildTower::residual, expr]]];
    Throw[$Failed, "build"]];
  fpair = ToPair[expr, Y, q];
  If[q =!= None, AppendTo[back, Y -> Sqrt[q]]];
  {T, fpair, back, Y}];

(* ParallelIntegrateMixed[integrand, x, opts]  -- the surface entry point.
   Builds the tower with BuildTower, runs the pair form, and maps the result
   back to x with ReplaceRepeated over the back rules (generator symbols to
   their defining expressions, flattened roots to base^(1/m), Y to Sqrt[q]).
   A certificate or failure tuple is returned as is, with the same
   back-substitution applied so the prime and residue read in surface terms.
   With "Verify" -> True the surface result is differentiated and compared
   with the integrand numerically at three points; a mismatch prints a
   warning and still returns the result.                                     *)
ParallelIntegrateMixed[integrand_, x_Symbol, opts : OptionsPattern[]] := Module[{bt, T, fpair, back, Y, res, surf, ok},
  bt = Catch[BuildTower[integrand, x], "build"];
  If[bt === $Failed, Return[$Failed]];
  {T, fpair, back, Y} = bt;
  If[OptionValue["Verbose"],
    Print["  tower: generators ", T["gens"], " with D = ", T["derivs"],
      If[T["q"] =!= None, StringForm[", y^2 = `1`", T["q"]], ""]];
    Print["  integrand: ", fpair]];
  res = ParallelIntegrateMixed[fpair, T, "Bounds" -> OptionValue["Bounds"], "Verbose" -> OptionValue["Verbose"],
                                "SplitSpecials" -> OptionValue["SplitSpecials"]];
  If[ListQ[res], Return[res //. back]];
  surf = res //. back;
  If[OptionValue["Verify"],
    ok = AllTrue[{3/2, 2, 7/3}, Abs[N[(D[surf, x] - integrand) /. x -> #, 30]] < 10^-20 &];
    If[! ok, Print["  WARNING: numeric verification of D[result] - integrand failed"]]];
  surf];

Options[ParallelIntegrateMixed] = {"Bounds" -> None, "Verbose" -> False, "Verify" -> False, "SplitSpecials" -> Automatic};

(* pair form: with "SplitSpecials" -> Automatic a failed system is retried with
   every special prime split into its linear factors over the algebraic
   closure (Theorem 6.1 describes the specials over Fbar; the integral of
   Sqrt[Tan[x]] needs distinct coefficients on the four factors of 1 + u^4). *)
ParallelIntegrateMixed[f0_List, T_Association, opts : OptionsPattern[]] := Module[{r, split = OptionValue["SplitSpecials"]},
  r = Catch[iPIM[f0, T, "SplitSpecials" -> (split === True), opts], "PIM"];
  If[split === Automatic && ListQ[r] && r[[1]] === "failed" && r[[2]] === "no solution within bounds" && r[[-1]] === "splittable",
    r = Catch[iPIM[f0, T, "SplitSpecials" -> True, opts], "PIM"]];
  If[ListQ[r] && r[[-1]] === "splittable", Most[r], r]];

(* iPIM[f, T, opts]
   The body of ParallelIntegrateMixed; ParallelIntegrateMixed wraps it in
   Catch so that the early exits (certificates and failures, raised with
   Throw[..., "PIM"] from inside the prime loop) return from the routine and
   not merely from the loop.  Local variables mirror the Python names:
     detLogs -- realised logands {tau, {a, b}} with known coefficient tau;
     unkLogs -- special primes {p, 0} offered with an unknown coefficient;
     denv    -- the denominator D_v of the rational part (special s-parts and
                Hermite factors);
     rem     -- the residual f - Sum tau D u / u over the realised logands;
     EE      -- the pair D(V) - rem + Sum beta_i D s_i / s_i whose vanishing
                is the linear system.                                        *)
iPIM[f0_, T_, OptionsPattern[ParallelIntegrateMixed]] := Module[
  {gens = T["gens"], q = T["q"], verbose = OptionValue["Verbose"], bounds = OptionValue["Bounds"],
   Y, f, dlcm, detLogs = {}, unkLogs = {}, denv = 1, fl, p, mult, branch, eta, delta, special,
   eP, vP, Dp, tp, texpr, pts, taus, cert, done, seen, cand, rem, ld, nb, db, monos, cs0, cs1,
   V, EE, betas, eqs, unks, sol, sub, frees, y, surf, I0, split = OptionValue["SplitSpecials"], splittable, newLogs, PP, rts, torsion = {}, got, tinf, lower, nonconst, gstar, a2, b2, c2, disc, s2, s, ok, pend, uu, tv},
  Y = Unique["y"];
  f = {Can[f0[[1]]], Can[If[q === None, 0, f0[[2]]]]};
  (* the components must be rational functions of the generators: an opaque
     function would be treated as a constant by the solver *)
  If[! AllTrue[f, RationalQ[#, gens] &],
    Throw[{"failed", "integrand component is not a rational function of the generators", f}, "PIM"]];
  dlcm = PolynomialLCM[Denominator[f[[1]]], Denominator[f[[2]]]];
  fl = Rest[FactorList[dlcm]];
  Do[{p, mult} = fac;
    If[FreeQ[p, Alternatives @@ gens], Continue[]];
    {branch, eta, delta, special} = ClassifyPrime[T, p];
    eP = If[branch, 2, 1];
    vP = VP[f, p, T, branch];
    If[special,
      denv *= p^mult; AppendTo[unkLogs, {p, 0}];
      If[verbose, Print["  (", p, "): special; s-part ", p, "^", mult, ", candidate log(", p, ")"]];
      Continue[]];
    If[verbose, Print["  (", p, "): ", If[branch, "branch", "unramified"], ", delta = ", delta,
        ", v_P(f) = ", vP, If[vP > -delta, "  [sub-critical]", ""]]];
    If[vP < -delta,
      denv *= p^Ceiling[(-vP - delta)/eP];
      (* deep residues (Proposition 7.6, constant-coefficient case: n = 1, D = d/dx) *)
      If[delta == 1 && ! branch && q =!= None && Length[gens] == 1 && T["derivs"][[1]] === {1, 0},
        pts = PointsOver[T, p];
        If[pts =!= None,
          taus = DeepResidues[T, f, p, pts, Y];
          If[verbose, Print["      deep residues at order ", -vP, ": ", taus]];
          If[MemberQ[taus, Undecided], Throw[{"failed", "deep residue sheet undecided", p}, "PIM"]];
          cert = CertifyNonconstant[#, gens] & /@ taus;
          If[MemberQ[cert, True], Throw[{"not elementary", p, First[Pick[taus, cert, True]]}, "PIM"]];
          If[MemberQ[cert, Undecided], Throw[{"failed", "residue constancy undecided", p, First[Pick[taus, cert, Undecided]]}, "PIM"]];
          If[AnyTrue[taus, # =!= 0 &],
            got = RealisePoints[T, p, pts, taus, Y, verbose];
            If[got === None, AppendTo[torsion, {p, taus}], detLogs = Join[detLogs, got]]]]]];
    If[vP == -delta,
      (* tau_P = e (f h / Dh)|_P with h = p *)
      Dp = TowerD[T, {p, 0}];
      tp = If[q =!= None, Pdiv[Pscale[eP p, f], Dp, q], {Can[eP p f[[1]]/Dp[[1]]], 0}];
      texpr = tp[[1]] + tp[[2]] Y;
      pts = PointsOver[T, p];
      If[pts === None, Throw[{"failed", "residues over a prime with no constant-coefficient direction", p}, "PIM"]];
      If[branch, Throw[{"failed", "critical branch residue", p}, "PIM"]];
      taus = ResFmt[ReduceAt[texpr, #, Y]] & /@ pts;
      If[verbose,
        If[q === None, Print["      residues ", taus],
          Print["      places ", ("y=" <> ToString[#[[3]]]) & /@ pts, ": residues ", taus]]];
      cert = CertifyNonconstant[#, gens] & /@ taus;
      If[MemberQ[cert, True],
        Throw[{"not elementary", p, First[Pick[taus, cert, True]]}, "PIM"]];
      If[MemberQ[cert, Undecided],
        Throw[{"failed", "residue constancy undecided", p, First[Pick[taus, cert, Undecided]]}, "PIM"]];
      If[AllTrue[taus, Simplify[# - taus[[1]]] === 0 &],
        If[taus[[1]] =!= 0, AppendTo[detLogs, {taus[[1]], {p, 0}}]];
        Continue[]];
      (* quadratic y-split: disc = s^2 q  =>  factors 2 a g + b -+ s y, N = 4 a p *)
      done = False;
      If[q =!= None,
        Do[gstar = gg;
          If[! (PolynomialQ[p, gstar] && Exponent[p, gstar] == 2), Continue[]];
          {c2, b2, a2} = PadRight[CoefficientList[p, gstar], 3];
          If[! FreeQ[{a2, b2, c2}, gstar] || ! (Head[a2] === Integer || Head[a2] === Rational), Continue[]];
          disc = Can[b2^2 - 4 a2 c2];
          s2 = Can[disc/q];
          s = PowerExpand[Sqrt[Factor[s2]]];
          (* s must lie in K: no algebraic function of the generators (algebraic
             constants such as Sqrt[3] are allowed) *)
          If[Simplify[s^2 - s2] =!= 0 || ! FreeQ[s, Power[b_, e_Rational] /; ! FreeQ[b, Alternatives @@ gens]], Continue[]];
          ok = True; pend = {};
          Do[uu = {Expand[2 a2 gstar + b2], -sg s};
            tv = Pick[taus, Simplify[ReduceAt[uu[[1]] + uu[[2]] Y, #, Y]] === 0 & /@ pts, True];
            If[tv =!= {} && AllTrue[tv, # === tv[[1]] &], AppendTo[pend, {tv[[1]], uu}], ok = False],
            {sg, {1, -1}}];
          If[ok,
            Do[If[tv0[[1]] =!= 0, AppendTo[detLogs, tv0]];
              If[verbose, Print["      y-split factor ", tv0[[2, 1]], " + (", tv0[[2, 2]], ")*y: residue ", tv0[[1]]]],
              {tv0, pend}];
            done = True; Break[]],
          {gg, gens}]];
      If[done, Continue[]];
      got = RealisePoints[T, p, pts, taus, Y, verbose];
      If[got === None, AppendTo[torsion, {p, taus}], detLogs = Join[detLogs, got]]],
    {fac, fl}];
  If[torsion =!= {}, Throw[{"needs torsion realisation (milestone iii)", torsion}, "PIM"]];

  (* residue at the hypertangent place at infinity (Lemma 8.1) *)
  If[q =!= None && Length[gens] >= 2,
    tinf = VinftyResidue[T, f, Y];
    If[tinf =!= None,
      If[verbose, Print["  v_oo (hypertangent top): delta = 1, v_oo(f) = -1, residue ", tinf[[1]], " + (", tinf[[2]], ")*y"]];
      lower = Most[gens];
      nonconst = Can[tinf[[2]]] =!= 0 || CertifyNonconstant[tinf[[1]], lower] === True;
      If[nonconst, Throw[{"not elementary", "v_oo", tinf}, "PIM"]]]];

  (* tower specials (Theorem 6.1): offered regardless of the integrand *)
  seen = unkLogs[[All, 1]];
  cand = {};
  Do[Do[If[comp === 0, Continue[]];
      Do[If[FreeQ[part, Alternatives @@ gens], Continue[]];
        Do[If[! FreeQ[fac2[[1]], Alternatives @@ gens], AppendTo[cand, fac2[[1]]]],
          {fac2, Rest[FactorList[part]]}],
        {part, {Numerator[Can[comp]], Denominator[Can[comp]]}}],
      {comp, dpair}],
    {dpair, Join[T["derivs"], If[q =!= None, {T["Dy"]}, {}]]}];
  Do[If[MemberQ[seen, pp], Continue[]];
    If[ClassifyPrime[T, pp][[4]],
      AppendTo[unkLogs, {pp, 0}]; AppendTo[seen, pp];
      If[verbose, Print["  tower special: candidate log(", pp, ")"]]],
    {pp, DeleteDuplicates[cand]}];

  (* specials over Fbar (Theorem 6.1): on request replace each special p(g)
     with constant coefficients and degree >= 2 by its linear factors g - r *)
  splittable = AnyTrue[unkLogs, Function[pl, AnyTrue[gens,
      PolynomialQ[pl[[1]], #] && Exponent[pl[[1]], #] >= 2 && FreeQ[CoefficientList[pl[[1]], #], Alternatives @@ gens] &]]];
  If[split === True && splittable,
    newLogs = {};
    Do[PP = pl[[1]];
      gstar = SelectFirst[gens, PolynomialQ[PP, #] && Exponent[PP, #] >= 2 && FreeQ[CoefficientList[PP, #], Alternatives @@ gens] &, None];
      If[gstar === None, AppendTo[newLogs, pl],
        rts = gstar /. Solve[PP == 0, gstar];
        Do[AppendTo[newLogs, {gstar - r, 0}], {r, rts}]],
      {pl, unkLogs}];
    unkLogs = newLogs;
    If[verbose, Print["  specials split over Fbar: ", unkLogs[[All, 1]]]]];

  (* units (stage 3): offered for even-degree q there; here none *)

  (* residual integrand *)
  rem = f;
  Do[ld = If[q =!= None, Pdiv[TowerD[T, u[[2]]], u[[2]], q], {Can[TowerD[T, u[[2]]][[1]]/u[[2, 1]]], 0}];
    rem = Padd[rem, Pscale[-u[[1]], ld]],
    {u, detLogs}];

  (* ansatz: degree bound max degree + 2 in each generator (top variable: Theorem 8.2) *)
  If[bounds === None,
    nb = Numerator /@ rem; db = (Denominator[#] denv) & /@ rem;
    bounds = Table[Max[Exponent[#, g] & /@ Join[nb, db]] + 2, {g, gens}]];
  monos = Tuples[Range[0, #] & /@ bounds];
  cs0 = c0 @@@ monos; cs1 = If[q =!= None, c1 @@@ monos, {}];
  V = {Total[MapThread[#1 Times @@ (gens^#2) &, {cs0, monos}]]/denv,
       If[q =!= None, Total[MapThread[#1 Times @@ (gens^#2) &, {cs1, monos}]]/denv, 0]};
  (* assembled WITHOUT Cancel: with the unknown coefficients present a gcd
     would treat them as variables (catastrophic over an algebraic
     extension), and a spurious common factor only rescales an equation *)
  EE = Together /@ (TowerD[T, V] - rem);
  betas = Table[beta[i], {i, Length[unkLogs]}];
  Do[EE = Together /@ (EE + betas[[i]] *
      If[q =!= None, Pdiv[TowerD[T, {unkLogs[[i, 1]], 0}], {unkLogs[[i, 1]], 0}, q],
                     {Can[TowerD[T, {unkLogs[[i, 1]], 0}][[1]]/unkLogs[[i, 1]]], 0}]),
    {i, Length[unkLogs]}];
  eqs = Flatten[If[# === 0, {}, CoefficientRules[Numerator[Together[#]], gens][[All, 2]]] & /@ EE];
  unks = Join[cs0, cs1, betas];
  sol = If[eqs === {}, {{}}, Solve[Thread[eqs == 0], unks]];
  If[sol === {}, Throw[If[splittable && split =!= True,
      {"failed", "no solution within bounds", bounds, "splittable"},
      {"failed", "no solution within bounds", bounds}], "PIM"]];
  sub = First[sol];
  frees = Complement[unks, sub[[All, 1]]];
  sub = Join[sub, Thread[frees -> 0]] /. (a_ -> b_) :> (a -> (b /. Thread[frees -> 0]));
  If[AnyTrue[EE, Can[# /. sub] =!= 0 &], Throw[{"failed", "internal: solution does not verify", bounds}, "PIM"]];

  y = If[q =!= None, Sqrt[q], None];
  surf[u_] := u[[1]] + If[q =!= None, u[[2]] y, 0];
  I0 = Can[V[[1]] /. sub] + If[q =!= None, Can[V[[2]] /. sub] y, 0]
       + Total[#[[1]] Log[surf[#[[2]]]] & /@ detLogs]
       + Total[Table[(betas[[i]] /. sub) Log[unkLogs[[i, 1]]], {i, Length[unkLogs]}]];
  I0];

End[];
EndPackage[];
