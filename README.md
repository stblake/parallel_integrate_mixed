# parallel_integrate_mixed

A SymPy implementation of the parallel (Risch–Norman) integration method for
towers of elementary functions that contain a **simple radical** $y^m=q$ at
any position — the setting of

> S. Blake, *Parallel Integration over Simple Radical Extensions II: Mixed
> Towers*

Every example in the paper is computed by this code and verified by
differentiation; `examples.py` reruns all of them and reports, for each, the
outcome the paper claims.

```
python examples.py            # everything (about six minutes; Günther dominates)
QUICK=1 python examples.py    # skip the two multi-minute benchmarks
```

## The algorithm in one paragraph

Let $K=F(t_1,\dots,t_n)$ be a tower of transcendental generators over a
constant field $F$, with $t_1=x$ and $Dx=1$, and let $L=K(y)$ with $y^m=q$.
Classical Risch–Norman requires $K$ to be closed under the derivation $D$,
so the radical must sit on top. Here it may sit anywhere: the generators
above it — logarithms, exponentials, tangents — may have derivatives
involving $y$. The method is still *parallel*: one working ring
$\mathcal A=\mathcal O[t_{j+1},\dots,t_n]$ (with $\mathcal O$ the integral
closure of the polynomial ring below the radical, on the explicit Trager
basis), one global ansatz for the integral

$$
\int f dx = \frac{b}{sD_v}+\sum_i c_i\log u_i ,
$$

and one linear system. There is no integral-basis computation, no Puiseux
expansion, and no recursion over the tower. The ingredients, in the order
the code runs them:

1. **Classification** of each prime of the denominator: unramified or
   branch; *normal* or *special*; and its pole order
   $\delta_P=1+v_P(\mathfrak d_D)$ for the derivation, computed locally from
   the *denominator divisor* $\mathfrak d_D$ (this generalises the
   $\delta_P\in\{1,e_P\}$ of Part I, which holds only for monomial towers).
2. **Hermite denominators** from the valuation lemma
   $v_P(Dg)=v_P(g)-\delta_P$: poles of order $>\delta_P$ force a factor of
   $D_v$; poles in the *sub-critical window* $-\delta_P<v_P(f)<0$ force
   nothing at all.
3. **Residues** $\tau_P(f)$ at the critical primes, on every sheet of the
   curve, with a canonical extension to any pole order. If some residue is
   not a constant, the integral is **certified non-elementary**.
4. **Realisation** of the residue divisor as logands: equal residues give a
   polynomial logand; residues split by the curve are realised by a norm
   search $a^2-qb^2=cp^k$; the remaining cases are torsion on the curve,
   handled for one-place elliptic curves by division polynomials and Miller
   functions.
5. **Units** (logands invisible to residues), found by the continued
   fraction of $\sqrt q$ — and, when that fails, a *non-torsion certificate*
   by reduction modulo two primes proves that no unit exists.
6. **Degree bounds** in the top variable (proved for primitive,
   hyperexponential and hypertangent tops), heuristic below it; then the
   linear system, then verification by differentiation.

## Certificates

Unlike the classical parallel method, whose failure proves nothing, the
algorithm returns proofs of non-elementarity in two situations:

* **Residue certificate.** A residue at a normal prime that does not lie in
  the constant field. This is decided *exactly* (the residue is reduced to
  canonical form $a+b\sqrt A$ in the residue field), so a constant in
  disguise is never mistaken for an obstruction.
* **Holomorphic-remainder certificate.** For $n=1$: after all residues are
  realised and the unit group is known, the residual is a second-kind
  differential; if the linear system with the *exact* degree bounds of
  Part I is inconsistent, the integral is not elementary. The residual is
  re-verified residue-free before the certificate is issued.

Everything else the code cannot decide is returned as `('failed', reason,
...)` and claims nothing.

## Return values

`parallel_integrate_mixed(f, T, verbose=False)` takes the integrand as a
pair `(f0, f1)` meaning $f_0+f_1y$, and a `Tower(gens, derivs, q=...)`
whose `derivs[i]` is $D(\text{gens}[i])$ as a pair. It returns one of

| value | meaning |
|---|---|
| a SymPy expression in the generators and `sqrt(q)` | the integral, verified by differentiation |
| `('not elementary', P, tau)` | certified: non-constant residue `tau` at the prime `P` |
| `('not elementary', 'v_oo', tau)` | certified: non-constant residue at the hypertangent place at infinity |
| `('not elementary', 'holomorphic remainder: ...', bounds)` | certified: residue-free remainder, exact system inconsistent |
| `('failed', reason, ...)` | undecided — a guessed input (special exponent, sub-top degree bound, inconclusive unit search) was in play |

## Files

| file | contents |
|---|---|
| `parallel_mixed.py` | the algorithm: classification, residues, realisation, torsion, certificates, the linear system |
| `pell.py` | continued-fraction unit search over $\mathbb Q$ and over $\mathbb F_p$; the non-torsion certificate |
| `examples.py` | every example of the paper, with the expected outcome and a surface-level check by differentiation |
| `rnrad2.py`, `weier.py` | from Parts I and III of the series: exact degree bounds for $n=1$, division polynomials |

## Limitations

* $m\le2$ and $q$ squarefree in the implementation; the paper's theory
  covers general $m$ and $q=\prod Q_l^{l}$.
* Places are enumerated over primes of degree $\le4$ in one generator with
  constant coefficients (roots in radicals); residues at primes of higher
  degree, or with non-constant coefficients beyond the quadratic
  $y$-split, are not computed.
* The canonical residue at poles deeper than $\delta_P$ is implemented only
  where the derivation acts trivially on the coefficient field ($n=1$,
  $D=d/dx$); in a tower the local Hermite reduction of the paper's
  Proposition 7.6 must be run as written.
* Torsion realisation covers elliptic curves $y^2=q$ with $\deg q=3$ and
  constant coordinates; the non-torsion certificate covers the class
  $[\infty_+-\infty_-]$ for $\deg q$ even.
* Degree bounds below the top variable, and the exponents of special
  logands, are guessed (as in Bronstein's ParallelIntegrate); the
  holomorphic-remainder certificate is therefore restricted to $n=1$.
* Assumption (T4) of the paper — no new constants in the tower — is not
  verified. A violation can only produce a spurious `not elementary` at the
  constancy decision, never a wrong integral.
* `examples.py` takes about six minutes in full; the Chebyshev (≈25 s) and
  Günther (≈4 min, torsion of order 6 on six places) benchmarks dominate.

## The examples

Numbering follows Section 10 of the paper. Throughout, $y$ is the radical
of the tower and $t$ the generator above it. Each entry gives the integral,
the answer or certificate, and what the example exercises.

### 10.1 The flagship

$$\int \log\bigl(x+\sqrt{x^2+1}\bigr)dx = x\log\bigl(x+\sqrt{x^2+1}\bigr)-\sqrt{x^2+1}.$$

$y^2=x^2+1$, $t=\log(x+y)$, $Dt=1/y\notin K$: the smallest tower outside
Part I. Single sub-critical branch pole, so $v$ is polynomial; one linear
block.

### 10.2 An irreplaceable unit

$$\int \frac{1+xe^{\sqrt{x^2+1}}}{\sqrt{x^2+1}}dx = e^{\sqrt{x^2+1}}+\log\bigl(x+\sqrt{x^2+1}\bigr).$$

$t=e^{y}$. The logand $x+y$ is a unit of $\mathcal O$: no residue sees it,
so it is offered unconditionally and the linear system forces its
coefficient.

### 10.3 Non-elementarity at a moving prime

$$\int \frac{dx}{x\log\bigl(x+\sqrt{x^2+1}\bigr)} \quad\text{is not elementary.}$$

The prime $(t)$ is *moving*; its residue $y/x$ is not a constant of the
residue field $\mathrm{Frac}(\mathcal O)$ — the residue certificate.

### 10.4 A nested radical: Bronstein's Example (E)

$$\int \frac{\log x+\sqrt{\log x+\sqrt{\log x}}}{1+\log x}dx \quad\text{is not elementary.}$$

The inner root $t=\sqrt{\log x}$ flattens into the transcendence basis
($Dt=1/(2xt)$); the outer root becomes the single radical $y^2=t^2+t$. The
four residues $x(-1\pm\sqrt{-1\pm i})$ over $\log x=-1$ are non-constant,
and their symmetric functions are the coefficients of Bronstein's
resultant $z^4+4xz^3+8x^2z^2+8x^3z+5x^4$ — his 1990 non-elementarity proof
recovered from four residue evaluations.

### 10.5 A pure root flattens

$$\int e^{\sqrt x}dx = 2\bigl(\sqrt x-1\bigr)e^{\sqrt x}.$$

$u=\sqrt x$ is a pure root of a generator and absorbs into the basis; the
computation is purely transcendental, with $\delta_{(u)}=2$ appearing as
the flattened image of the branch pole order.

### 10.6 A residue at the hypertangent place at infinity

$$\int \frac{\tan\sqrt x}{\sqrt x}dx = \log\bigl(1+\tan^2\sqrt x\bigr).$$

Flattened as in 10.5; the special logand $1+t^2$ of the hypertangent
generator carries the integral.

### 10.7 Hypertangent over the curve

$$\int \Bigl(x\bigl(1+\tan^2 y\bigr)+\frac{3x\tan y}{y}\Bigr)dx = y\tan y+\log\bigl(1+\tan^2 y\bigr),\qquad y=\sqrt{x^2+1}.$$

$t=\tan y$ with $Dt=(x/y)(1+t^2)$: a hypertangent whose derivative passes
through $y$. The algebraic rational part $yt$ comes out of the linear
system. The companion instance

$$\int \tan\sqrt{x^2+1}dx \quad\text{is not elementary:}$$

the residue at the place $v_\infty$ of the hypertangent is $-y/x$, a
non-constant.

### 10.8 Moving logands split by the curve

$$\int \frac{t^3+(4+x-x^2)t-(1+5x)y}{y(t^2-x^2-1)}dx = \tfrac12 t^2+2\log(t-y)+3\log(t+y),\qquad y=\sqrt{x^2+1},\ t=\log(x+y).$$

The prime $t^2-x^2-1$ is irreducible over $K$ but splits over the curve into
$(t-y)(t+y)$, with residues $2$ and $3$ on the two sheets — a logand that no
polynomial can realise, obtained from the $y$-split of the quadratic.

### 10.9 Bronstein's tutorial Example 14

$$\int \frac{(x+1)^2\sqrt{x+\log x}+(3x+1)\log x+3x^2+x}{(x\log x+x^2)\sqrt{x+\log x}+x^2\log x+x^3}dx = 2\sqrt{x+\log x}+2\log\bigl(x+\sqrt{x+\log x}\bigr).$$

The showcase of the recursive algorithm (integral basis, resultant, Puiseux
expansions, principality test, Risch differential equations) flattens: with
$u=\sqrt{x+\log x}$ it is a purely transcendental computation with one
residue and one linear block.

### 10.10 Bronstein's tutorial Example 15

$$\int \frac{3(x+e^x)^{1/3}+(2x^2+3x)e^x+5x^2}{x(x+e^x)^{1/3}}dx = 3x(x+e^x)^{2/3}+3\log x.$$

Also flattens, with $u=(x+e^x)^{1/3}$; the first $m=3$ instance,
$\delta_{(u)}=3$ matching $\delta_P=e_P=3$ of the unflattened curve.

### 10.11 Bronstein 1990, pp. 134 and 147

$$\int \frac{(x+1)dx}{(x\log x+x^2)\sqrt{x+\log x}} = -\frac{2}{\sqrt{x+\log x}}$$

is a pure Hermite computation. The p. 147 integrand is that of Example 14;
**as printed** (coefficient $x^2+x+1$ instead of $(x+1)^2$) it is
**not elementary** — its residue at $(u+x)$ is $2(2u^2-1)/(2u^2+u-1)$, a
non-constant — while the corrected integrand, in lowest terms,

$$\int \frac{(x+1)^2+(3x+1)\sqrt{x+\log x}}{x\sqrt{x+\log x}\bigl(x+\sqrt{x+\log x}\bigr)}dx = 2\sqrt{x+\log x}+2\log\bigl(x+\sqrt{x+\log x}\bigr).$$

### 10.12 Cohen's pseudo-elliptic integral (1993)

$$\int \frac{xdx}{\sqrt{x^4+10x^2-96x-71}} = \tfrac18\log\bigl(A+B\sqrt{x^4+10x^2-96x-71}\bigr),$$

$A=x^8+20x^6-128x^5+54x^4-1408x^3+3124x^2+10001$,
$B=x^6+15x^4-80x^3+27x^2-528x+781$. Every finite pole is sub-critical, so
the whole integral is a unit found by the continued fraction of $\sqrt q$.
The companion with constant term $-72$ is **not elementary**: the class
$[\infty_+-\infty_-]$ has orders $3,13,7,21$ modulo $7,11,13,17$, which
certifies non-torsion, and the exact linear system then excludes a
rational integral.

### 10.13 Schultz's genus-2 integral (2015)

$$\int \frac{(29x^2+18x-3)dx}{\sqrt{x^6+4x^5+6x^4-12x^3+33x^2-16x}} = \log\bigl(A+B\sqrt q\bigr),\qquad \deg A=29,\ \deg B=26,$$

again a pure unit, computed in a few seconds with coefficients matching
Schultz's paper digit for digit (and correcting one misprint there).

### 10.14 Bronstein's Risch differential equation on an algebraic curve (ISSAC 1991)

$$\int \Bigl(\frac{5x^4+2x-2}{x^2}\Bigl(1+\frac1{\sqrt{x^3+1}}\Bigr)+\frac{x}{\sqrt{x^3+1}}\Bigr)e^{x\sqrt{x^3+1}}dx = \frac2x\bigl(1+\sqrt{x^3+1}\bigr)e^{x\sqrt{x^3+1}}.$$

$t=e^{xy}$ over the elliptic curve $y^2=x^3+1$: the Risch differential
equation of the recursive method is the $t^1$-block of the linear system;
the first benchmark with a Hermite part.

### 10.15 Chebyshev's integral (Davenport, Example 5)

$$\int \frac{2x^6+4x^5+7x^4-3x^3-x^2-8x-8}{(2x^2-1)^2\sqrt{q}}dx = \frac{(2x+1)\sqrt q}{2(2x^2-1)}-\frac52\log\bigl(x^2+2x+\sqrt q\bigr)+\frac52\log\bigl(x^2+2x-\sqrt q\bigr)+\log\bigl(A+B\sqrt q\bigr),$$

$q=x^4+4x^3+2x^2+1$, $A=x^5+7x^4+15x^3+9x^2+2$, $B=x^3+5x^2+6x$. The only
benchmark exercising all three mechanisms at once: a Hermite part, residues
$\pm\tfrac52$ at a double pole realised by the norm search
$N(x^2+2x\pm\sqrt q)=2x^2-1$, and an order-5 unit.

### 10.16 Günther's integral (1882)

$$\int \frac{xdx}{(x^3+8)\sqrt{x^3-1}} = \frac{\sqrt3}{108}\log\!\left(\frac{(x^2+x+1)(x^2+10x-8)+3\sqrt3(x^2+2x)y}{(x^2+x+1)(x^2+10x-8)-3\sqrt3(x^2+2x)y}\right)-\frac1{27}\arctan\!\left(\frac{3y}{(x-1)^2}\right)+\frac1{54}\arctan\!\left(\frac{3(2+2x-x^2)y}{x^4-7x^3+3x^2+2x+10}\right),$$

$y=\sqrt{x^3-1}$. Six places with pairwise distinct residues, each an
order-6 torsion class on the CM curve $y^2=x^3-1$; realised by Miller
functions with orders certified by the division polynomial $\psi_6$. The
code returns the six-logarithm form, of which the display is the collapse
over conjugate pairs.

### Certificate: a torsion divisor with a holomorphic remainder

$$\int \frac{dx}{(x-2)\sqrt{x^3+1}} \quad\text{is not elementary.}$$

The residue divisor is $3$-torsion and is realised, yet the remainder is
$\tfrac13dx/y$: with the exact bounds of Part I the linear system is
inconsistent — the holomorphic-remainder certificate.

### Regression (not in the paper): the torus over the logarithmic tower

$$\int \frac{4\log^3x+3\log x+1+5\sqrt{\log^2x+1}}{2x\log x\sqrt{\log^2x+1}}dx = ty+\log(t+y)+2\log(t+1+y)+3\log(t+1-y),\qquad t=\log x,\ y=\sqrt{t^2+1}.$$

The curve $y^2=t^2+1$ over $t=\log x$ cannot be flattened; split residues
$3,2$ are realised by the norm search ($N(t+1\mp y)=2t$) and the unit
$t+y$ is forced through the system.

## Citing

Part I: S. Blake, *Parallel integration over simple radical extensions*,
[arXiv:2608.29482](https://arxiv.org/abs/2608.29482).
Part II: S. Blake, *Parallel integration over simple radical extensions II:
mixed towers*, in preparation.
