# Delayed, truncated packets: an alternative analytic proof of prime abundance

## Status and the change of theorem

This is a **complete mathematical proof proposal for an alternative packet family**, supplied for independent review. It is not a Lean-verified theorem, not a verification of the unavailable manuscript, and not a proof of the originally proposed overlap bound for the entire packet family.

The change is explicit: keep only primitive rays whose two coordinates lie between a logarithmic lower cutoff and a small power of the row cutoff, and begin the scale parameter much later. The mean retains its required order. Distinct rays then have no dangerous short scale progression. Removing the smallest rays also makes the same-ray overlap tend to zero.

The result proved below for this smaller family is

\[
 \nu_B\asymp\frac{(\log B)^3}{\log w_B},\qquad
 \Lambda_B=O(1/\log B),\qquad
 w_B=\lfloor(8\log B)^{100}\rfloor.
\]

In particular, the corresponding prime-abundance conclusion is

\[
 \#\{p\le N:\ p\text{ prime and lacks the specified number of strict Type-II solutions}\}
 \ll \frac{N\log\log N}{(\log N)^3},
\]
with solution threshold a positive constant times \((\log p)^3/\log\log p\). This is an alternative to estimating the full-family overlap, not a deduction of that estimate. No priority or novelty claim is made.

All limits and asymptotic comparisons below are for the indicated integer parameter tending to infinity. Implied constants are absolute. Logarithms are natural. The substantive counting and number-theoretic estimates used in the analytic argument are proved below. Ordinary CRT, finite Hölder, unique factorization, and elementary calculus are used. In particular no Henriot theorem, prime number theorem, unproved lower sieve, or composite square-root-count theorem is assumed.

The initial finite review packet remains the source for the original definitions and requested scope. The construction and estimates in this document are new derivations. Computational checks are separate and do not establish any asymptotic assertion.

## 1. Exact smaller packet family

Let \(B\ge2\) be an integer and set

\[
 L=\log B,\qquad K=\lfloor L^2\rfloor+2,\qquad Y=B^8,
 \qquad w=w_B=\lfloor(\log Y)^{100}\rfloor.
\]

Consider integer parameters

\[
 K\le a<b\le B,\quad (a,b)=1,\qquad B^4<u\le B^6.
\]

They define

\[
 M=3abu,\qquad s=3a^2u,\qquad Q=4M-1=12abu-1.
\]

Keep the parameter exactly when every prime divisor of \(Q\) is greater than \(w\). All rough composite \(Q\), as well as rough prime \(Q\), are included. Call the resulting finite family \(\mathcal L_B\).

These are authentic original packets at cutoff \(Y=B^8\):

* \(3\mid M\), \(M\le3B^8\), and \(Q<12B^8\).
* \(0<s<M\), because \(a<b\).
* \(M^2/s=3b^2u\) is a positive integer.
* \(Q>1\), so roughness is precisely the original `minFac(Q)>w` condition.

There is no multiplicity from parametrization. The reduced fraction \(s/M=a/b\) recovers \(a,b\), after which \(u=M/(3ab)\). Thus distinct parameters give distinct pairs \((M,s)\).

Define

\[
 T_B(n)=\#\{(M,s)\in\mathcal L_B:Q\mid n+4s\},\qquad
 \nu_B=\sum_{\mathcal L_B}\frac1Q.
\]

Define \(\Lambda_B\) exactly as the original unordered overlap, but restricted to \(\mathcal L_B\): sum \(g/(QQ')\) over \(Q<Q'\), \(g=(Q,Q')>1\), and \(s\equiv s'\pmod g\). The full numerical gcd, with all prime-power exponents, is used.

Because \(\mathcal L_B\) is a subset, its solution witnesses are also witnesses for the original family. However, a bound on \(\Lambda_B\) is **not** an upper bound on the original \(\Delta_{B^8}\). The restricted finite second moment is proved directly in Section 9; no monotonicity of a variance quotient is asserted.

Small \(B\) may give an empty family, including because \(K>B\) or \(w>Q\). The eventual positive lower bound in Section 6, not a small numerical example, establishes nonvacuity.

## 2. The determinant identity and full compatibility

For two parameters \((a,b,u)\), \((c,e,v)\), put

\[
 D=ae-cb.
\]

The exact integer identity is

\[
 4be(s-s')=aeQ-cbQ'+D.                                      \tag{2.1}
\]

If \(d\mid Q,Q'\), then \((d,12abce)=1\): any common prime factor would divide a product and that product minus one. Consequently \((d,4be)=1\). Identity (2.1), followed by cancellation of the unit \(4be\) modulo \(d\), proves

\[
 s\equiv s'\pmod d\quad\Longleftrightarrow\quad d\mid D.     \tag{2.2}
\]

This equivalence holds at the **full modulus \(d\)**, not merely its radical.

Two reduced rays \((a,b)\ne(c,e)\) have \(D\ne0\). Indeed equality of the two reduced fractions forces equality of their positive coprime numerators and denominators. Since all coordinates are at most \(B\),

\[
 0<|D|<B^2.                                                \tag{2.3}
\]

For a compatible pair on distinct rays, its actual full gcd therefore satisfies

\[
 1<g\le |D|<B^2<B^4<u,v.                                  \tag{2.4}
\]

This is the reason for delaying the scale. The problematic first scale value in a progression never has size comparable to one while its modulus is large.

If the rays agree, \(g\mid u-v\), because \((g,12ab)=1\). Thus same-ray pairs are compatible at their full gcd; they will be bounded separately.

## 3. A uniform reciprocal progression bound with its first term

Fix a ray \((a,b)\) and a positive integer \(d<B^2\). Drop the roughness condition and write

\[
 S_{a,b}(d)=
 \sum_{\substack{B^4<u\le B^6\\d\mid12abu-1}}\frac1{12abu-1}.
\]

If \((d,12ab)>1\), this sum is zero. Otherwise its scale values are one residue class modulo \(d\). If \(u_0\) is the first value in the interval, the integral comparison for a decreasing reciprocal gives

\[
 \sum_{j=0}^{J}\frac1{u_0+jd}
 \le\frac1{u_0}+\frac1d\log\frac{u_0+Jd}{u_0}
 \le B^{-4}+\frac{2\log B}{d}
 \le\frac{1+2\log B}{d}.                                  \tag{3.1}
\]

The last inequality uses \(d<B^2\le B^4\). If there is no value, the same upper bound holds trivially.

Since \(12abu-1\ge11abu\),

\[
 S_{a,b}(d)\le\frac{1+2L}{11ab\,d}
             \le\frac{3\log(2B)}{11ab\,d}.                \tag{3.2}
\]

The first term has not been discarded. It is small because of the actual lower limit on \(u\).

## 4. Different-ray overlap: an elementary divisor-moment estimate

### 4.1 Positive full-divisor cover

For every integer \(g>1\),

\[
 g\le2(g-1)=2\sum_{d\mid g,\ d>1}\varphi(d).
\]

Every \(d>1\) dividing a retained row modulus is greater than \(w\). By (2.2), it also divides \(|D|\) for a different-ray compatible pair. Enlarge to all ordered pairs of distinct rays and all independent scale values. This overcounts, which is safe for an upper bound. With \(R=\log(2B)\), (3.2) and \(\varphi(d)\le d\) give

\[
\begin{aligned}
 \Lambda_B^{\rm diff}
 &\le 2\sum_{\text{ordered distinct rays}}
       \sum_{\substack{d\mid |D|\\d>w}}
           \varphi(d)S_{a,b}(d)S_{c,e}(d)\\
 &\le\frac{18R^2}{121}
       \sum_{\text{ordered distinct rays}}\frac1{abce}
          \sum_{\substack{d\mid |D|\\d>w}}\frac1d\\
 &\le\frac{18R^2}{121w}
       \sum_{\substack{1\le a,b,c,e\le B\\ae\ne bc}}
          \frac{\tau(|ae-bc|)}{abce}.                     \tag{4.1}
\end{aligned}
\]

The ordered enlargement is deliberately generous. It does not change the definition of \(\Lambda_B\). No equality between this cover and the original overlap is claimed. The divisor sum is over all divisors, including prime powers. The factor two from \(g\le2(g-1)\) is a separate upper-bound device; it is not the covariance factor two on unordered overlap in Section 9.

### 4.2 Bounding the remaining harmonic determinant sum

Set \(x=ae\), \(y=bc\), and \(X=B^2\). There are at most \(\tau(x)\tau(y)\) ordered factorizations, and \(abce=xy\). Therefore the final sum in (4.1) is at most

\[
 \mathcal E(X)=
 \sum_{\substack{1\le x,y\le X\\x\ne y}}
       \frac{\tau(x)\tau(y)\tau(|x-y|)}{xy}.              \tag{4.2}
\]

Here is a self-contained logarithmic bound. Let \(d_8(n)\) count ordered factorizations into eight positive factors. Then

\[
 \tau(n)^3\le d_8(n),\qquad
 \sum_{n\le Z}d_8(n)\le Z(1+\log Z)^7.                   \tag{4.3}
\]

For the first inequality, at a prime power \(p^h\), three divisors are three exponents in \(\{0,\ldots,h\}\). Assign each level \(j=1,\ldots,h\) to its three-bit membership pattern. The eight pattern counts are nonnegative and sum to \(h\); the three exponents can be recovered by summing the appropriate counts. This is an injection into the exponent choices for an eightfold factorization. Multiply the local injections over the prime factors. For the second inequality in (4.3), choose the first seven factors; there are at most \(Z\) divided by their product choices for the eighth, and enlarge each of the first seven ranges to \([1,Z]\).

Split \(x,y\) into dyadic boxes \([U,2U)\), \([V,2V)\), where \(U,V\) are powers of two. Let \(A=1+\log(2X)\). In such a box, excluding \(x=y\),

\[
\begin{aligned}
 \sum_{x,y}\tau(x)^3&\le2UV A^7,\\
 \sum_{x,y}\tau(y)^3&\le2UV A^7,\\
 \sum_{x,y}\tau(|x-y|)^3&\le4UV A^7.
\end{aligned}
\]

For the last bound, each positive difference has at most \(2\min(U,V)\) ordered representations, and every difference is at most \(2\max(U,V)\). Apply (4.3). Hölder's inequality now gives

\[
 \sum_{x,y}\tau(x)\tau(y)\tau(|x-y|)\le4UV A^7.
\]

Since \(xy\ge UV\), each box contributes at most \(4A^7\) to (4.2). The number of boxes is at most \((3R)^2\), and \(A\le3R\), for \(B\ge2\). Hence

\[
 \mathcal E(B^2)\le 78732 R^9\le100000R^9.                \tag{4.4}
\]

Equations (4.1) and (4.4) prove the explicit bound

\[
 \boxed{\Lambda_B^{\rm diff}
       \le 20000\frac{(\log(2B))^{11}}{w}}
       \qquad(B\ge2,\ w\ge2).                            \tag{4.5}
\]

This applies to the family with an auxiliary cutoff \(w\) as well. At the actual cutoff, \(w\asymp L^{100}\), so it is \(O(L^{-89})\). Equal-label pairs on distinct rays are included here; no additional equal-label term is needed.

## 5. Same-ray overlap: why the lower ray cutoff matters

We first prove a uniform kernel bound. For integers \(b_0\ge2\), \(1\le U_0\le T_0\), put

\[
 G(b_0;U_0,T_0)=\sum_{U_0\le m<n\le T_0}
 \frac{(b_0m-1,b_0n-1)}{(b_0m-1)(b_0n-1)},
 \qquad \ell=\log(2b_0T_0).
\]

Full-divisor expansion of the gcd, with \((d,b_0)=1\) whenever \(d\mid b_0m-1\), yields

\[
 G\le\frac\ell{b_0}
       \sum_{U_0\le m\le T_0}\frac{\tau(b_0m-1)}{b_0m-1}. \tag{5.1}
\]

Indeed, for fixed \(m,d\), the later indices are \(m+jd\), and

\[
 \sum_{1\le j\le(T_0-m)/d}\frac1{b_0m-1+b_0dj}
 \le\frac1{b_0d}\log\frac{b_0T_0-1}{b_0m-1}
 \le\frac\ell{b_0d}.
\]

Then use \(\varphi(d)\le d\). For an integer block \(U\le m<2U\), divisor pairing and the residue-class bound \(U/d+1\) give

\[
 \sum_{U\le m<2U}\tau(b_0m-1)
 \le U[2+\log(2b_0U)]+2\sqrt{2b_0U}.
\]

As \(b_0m-1\ge b_0U/2\), the weighted block sum is at most

\[
 6\ell/b_0+6/\sqrt{b_0U}\qquad(U\le T_0).
\]

Cover the range by full blocks \(U=2^jU_0\), enlarging the final block if necessary. There are at most \(3\ell\) blocks and their inverse-square-root sum is less than \(4/\sqrt{U_0}\). Inserting in (5.1) proves

\[
 G(b_0;U_0,T_0)
 \le32\left(\frac{\ell^3}{b_0^2}
       +\frac\ell{b_0^{3/2}\sqrt{U_0}}\right).             \tag{5.2}
\]

For each ray, apply (5.2) with \(b_0=12ab\), \(U_0=B^4+1\), \(T_0=B^6\). Drop roughness and include coprime row pairs; both changes increase the bound. Set

\[
 \ell_B=\log(24B^8)\le13L.
\]

The elementary integral bounds

\[
 \sum_{n\ge K}n^{-2}\le\frac1{K-1},\qquad
 \sum_{n\ge K}n^{-3/2}\le\frac2{\sqrt{K-1}}
\]

show

\[
 \boxed{\Lambda_B^{\rm same}
  \le\frac{\ell_B^3}{(K-1)^2}
       +\frac{4\ell_B}{B^2(K-1)}.}                         \tag{5.3}
\]

The constants in (5.3) are larger than those directly given by (5.2). Since \(K-1=\lfloor L^2\rfloor+1\ge L^2\),

\[
 \Lambda_B^{\rm same}\le\frac{2197}{L}+\frac{52}{B^2L}.
\]

The definition of \(\Lambda_B\) does not count any diagonal packet term; that term will be handled exactly once in the variance.

Combining (4.5) and (5.3) proves

\[
 \boxed{\Lambda_B\le
  \frac{\ell_B^3}{(K-1)^2}+\frac{4\ell_B}{B^2(K-1)}
       +20000\frac{(\log(2B))^{11}}{w_B}
       =O(1/\log B).}                                    \tag{5.4}
\]

In particular \(\Lambda_B\to0\). This is a statement about the deliberately restricted family, not the full original overlap.

## 6. The mean: no unproved sieve premise

### 6.1 Finite uniform linear sieve

Let \(c\ge2,w\ge2,U,H\ge0\) be integers, and let

\[
 S(c;U,H;w)=\#\{U<m\le U+H:(cm-1,P(w))=1\},
\]
where \(P(w)\) is the product of primes at most \(w\). Define

\[
 V_c(w)=\prod_{p\le w,\ p\nmid c}(1-1/p),\quad
 V(w)=\prod_{p\le w}(1-1/p),\quad
 k=2\lceil10\log w\rceil.
\]

Then

\[
 |S-HV_c(w)|\le H/w^4+2w^{k+1}.                            \tag{6.1}
\]

To prove this, apply the even Bonferroni truncation through \(k\) and the odd truncation through \(k+1\) to the excluded events \(p\mid cm-1\), for \(p\nmid c\). A subset with prime product \(d\) cuts out exactly one residue class modulo \(d\), hence its count differs from \(H/d\) by at most one. The number of terms is at most \(\sum_{j=0}^{k+1}w^j\le2w^{k+1}\). This count does not require \(d\le H\).

The expected truncation differs from \(V_c(w)\) by at most

\[
 \sum_{j\ge k+1}\frac{\sigma^j}{j!},\quad
 \sigma=\sum_{p\le w,\ p\nmid c}1/p\le\log w.
\]

The factorial bound \(j!\ge(j/e)^j\), the inequality \(k+1\ge20\log w+1\), and the successive-term ratio at most \(1/20\) bound this tail by

\[
 (20/19)(e/20)^{k+1}\le w^{-4}.
\]

This proves (6.1), uniformly in the coefficient \(c\).

Set \(D(w)=\lceil\exp(40(\log w)^2)\rceil\). If \(H\ge D(w)\), then

\[
 2w^{k+1}/H\le w^{-4}.
\]

For example, put \(l=\log w\). Since \(k+1\le20l+3\), the logarithm of the left side is at most \(\log2-20l^2+3l\le-4l\). Also \(V_c(w)\ge V(w)\ge1/w\), by comparison with the telescoping product over all integers from 2 to \(w\). Thus

\[
 \boxed{\tfrac12HV_c(w)\le S(c;U,H;w)
               \le\tfrac32HV_c(w)\quad(H\ge D(w)).}        \tag{6.2}
\]

The large length requirement is explicit. No claim is made for arbitrary short intervals.

### 6.2 Elementary prime-product bounds

For integers \(w\ge2\),

\[
 \frac1{3e^{18}\log w}\le V(w)\le\frac1{\log w}.           \tag{6.3}
\]

For the upper bound, expand the finite geometric Euler product \(V(w)^{-1}\). It includes \(\sum_{n\le w}1/n\ge\log(w+1)\).

For the lower bound, let \(\vartheta(x)=\sum_{p\le x}\log p\). The product of primes in \((n,2n]\) divides \(\binom{2n}{n}\le4^n\). Summing this inequality on powers of two and enlarging a general \(x\) to the next power of two gives \(\vartheta(x)\le3x\). Partial summation then gives

\[
 \sum_{p\le w}\frac{\log p}{p-1}\le6(1+\log w).
\]

Put \(\sigma=1+1/\log w\). Integration of the logarithmic Euler factors gives

\[
 \log\frac{V(w)^{-1}}{\prod_{p\le w}(1-p^{-\sigma})^{-1}}
 \le\frac1{\log w}\sum_{p\le w}\frac{\log p}{p-1}\le18.
\]

The finite Euler product at \(\sigma\) is at most
\(\sum_{n\ge1}n^{-\sigma}\le1+1/(\sigma-1)\le3\log w\), by an integral comparison. This proves (6.3). Only convergent nonnegative sums have been rearranged.

### 6.3 Harmonic mass of the truncated primitive rays

Write \(H_B=\sum_{n\le B}1/n\), and

\[
 C_B=\sum_{a,b\le B,\ (a,b)=1}\frac1{ab}.
\]

Decomposing by the gcd gives

\[
 H_B^2=\sum_{g\le B}\frac1{g^2}C_{\lfloor B/g\rfloor}
       \le C_B\sum_{g\ge1}g^{-2}\le2C_B.
\]

The only coprime diagonal pair is \((1,1)\), so the harmonic mass of all rays \(1\le a<b\le B\) is at least \(H_B^2/4-1/2\). Removing rays with \(a<K\) loses at most \(H_{K-1}H_B\). Consequently

\[
 \sum_{K\le a<b\le B,\ (a,b)=1}\frac1{ab}
 \ge\frac{H_B^2}{4}-\frac12-H_{K-1}H_B
 \ge\frac{L^2}{8}                                        \tag{6.4}
\]

for all sufficiently large \(B\), because \(\log K=O(\log L)=o(L)\). This proves nonemptiness of a substantial ray family rather than assuming it.

For the upper bound define \(F(n)=\prod_{p\mid n}(1-1/p)^{-1}\). Then

\[
 F(ab)\le F(a)F(b),\qquad
 \sum_{n\le B}\frac{F(n)}n\le e(1+L).                     \tag{6.5}
\]

Indeed \(F(n)=\sum_{d\mid n,\ d\text{ squarefree}}1/\varphi(d)\), so the harmonic sum is at most \(H_B\prod_p(1+1/[p(p-1)])\le eH_B\), using the telescoping sum \(\sum_{n\ge2}1/[n(n-1)]=1\).

### 6.4 Lower and upper mean bounds

For the actual \(w_B\), \(\log w_B=O(\log L)\), so

\[
 \log D(w_B)=O((\log L)^2)=o(L).
\]

Thus \(B^4\ge D(w_B)\) eventually. This also ensures that the length condition is compatible with the cutoff. All statements can use a common eventual threshold; for example an unnecessarily large choice with \(\log B\ge e^{100}\) suffices for these elementary growth inequalities and (6.4).

Use disjoint complete dyadic blocks \(U<u\le2U\) inside \((B^4,B^6]\), with \(U=2^jB^4\). There are \(J=\lfloor2L/\log2\rfloor\ge L/\log2\) such blocks for \(B\ge2\). On each ray and block, (6.2) supplies at least \(UV(w)/2\) retained scales. Each has reciprocal row weight at least \(1/(24abU)\). By (6.4),

\[
 \nu_B\ge\frac{JV(w)}{48}
                \sum_{\rm rays}\frac1{ab}
       \ge\frac{V(w)L^3}{384\log2}
       \gg\frac{L^3}{\log w}.                             \tag{6.6}
\]

For the upper bound, cover the scale range by at most \(\lceil2L/\log2\rceil\) complete dyadic blocks, enlarging the final block. On each block the count is at most \(3UV_{12ab}(w)/2\) and the reciprocal weight is at most \(1/(11abU)\). Further,

\[
 V_{12ab}(w)\le3V(w)F(a)F(b).
\]

Use (6.5) and sum over \(O(L)\) blocks to obtain

\[
 \nu_B\ll V(w)L\left(\sum_{a\le B}\frac{F(a)}a\right)^2
       \ll V(w)L^3\ll\frac{L^3}{\log w}.                 \tag{6.7}
\]

Thus the two-sided mean estimate is proved. It follows that \(\nu_B\to\infty\); in particular, the eventual natural multiplicity thresholds are positive and unbounded.

## 7. Combined analytic result and what it does not say

Sections 4–6 give, for the explicitly defined \(\mathcal L_B\),

\[
 \boxed{
  \nu_B\asymp\frac{(\log B)^3}{\log\log B},\qquad
  \Lambda_B=O(1/\log B)=o(1).
 }
\]

Writing the first expression with \(\log w_B\) rather than \(\log\log B\) gives the more literal version above. The factor 100 changes absolute constants, not these orders.

These statements are stronger overlap control for a **different, smaller family**. The following implications are not asserted:

* \(\Lambda_B=o(1)\) does not imply \(\Delta_{B^8}=o(1)\).
* It does not prove the original full-family bound \(\Delta_Y=O((\log Y)^3\log(2\log Y))\).
* The earlier original mean proof is not needed for this replacement argument.
* The earlier composite-root-count Lean candidate is not needed as an analytic input here. Ordinary two-modulus CRT is still used in the finite probability calculation.

## 8. Strict Type-II decoding and distinctness

For completeness, no counting convention is changed. If a retained packet fires at an integer \(n>Q\), set

\[
 x=(nM+s)/Q,\qquad y=nM,\qquad z=nMx/s.
\]

To see integrality, the firing condition and
\(M(n+4s)=(nM+s)+Qs\), together with \((M,Q)=1\), give \(Q\mid nM+s\). Further,

\[
 QMx=nM^2+Ms.
\]

Since \(s\mid M^2\) and \((s,Q)=1\), this proves \(s\mid Mx\), not merely \(s\mid nMx\). Thus \(z\) is an integer divisible by \(n\).

One has \(x>M>s\) because \(n>Q\), and \(x<n\) because \(n(3M-1)>s\). Hence \(x<y\), while \(z/y=x/s>1\). All three are positive. The identity

\[
 4Mx=nM+x+s
\]

gives \(4/n=1/x+1/y+1/z\) by division by \(nMx\). If \(n=p\) is prime, \(0<x<p\) gives \((p,x)=1\), while \(p\mid y,z\).

For fixed \(n\), recover \(M=y/n\), \(Q=4M-1\), and \(s=Qx-nM\). Therefore firing packets inject into distinct strictly ordered Type-II triples at a prime. No finiteness assumption on the entire solution set is used.

## 9. The restricted finite second moment, including all constants

The following finite argument applies to \(\mathcal L_B\) itself. Let \(m=\#\mathcal L_B\), \(\nu=\nu_B>0\), and \(\Lambda=\Lambda_B\). Average the firing indicators over a common multiple of their row moduli. Each indicator has mean \(1/Q\), so \(\mathbb ET=\nu\).

For a pair, CRT gives intersection probability zero if incompatible, otherwise \(1/\operatorname{lcm}(Q,Q')=g/(QQ')\). Same-row distinct labels cannot both fire: their label difference has magnitude less than \(Q\). Coprime pairs have zero covariance; incompatible pairs have nonpositive covariance. The diagonal variance contribution is \(\sum(1/Q-1/Q^2)\le\nu\). Unordered compatible different-row pairs occur twice in the square, so

\[
 v:=\mathbb E(T-\nu)^2\le\nu+2\Lambda.                    \tag{9.1}
\]

There is no extra diagonal factor two.

On \(H\) consecutive integers starting at \(A\), a residue class count differs from its expected value by at most one. For ordered compatible pairs the same assertion uses the full lcm. Expanding the normalized square, with the lower error bound on its negative linear term, gives

\[
 \sum_{0\le k<H}\left(1-\frac{T_B(A+k)}\nu\right)^2
 \le\frac{Hv}{\nu^2}+\frac{2m}\nu+\frac{m^2}{\nu^2}
 \le\frac{H(\nu+2\Lambda)}{\nu^2}+(1+12B^8)^2.            \tag{9.2}
\]

The final inequality uses \(Q<12B^8\), hence \(m/\nu\le12B^8\). This is an endpoint cost, not a hidden lcm-dependent loss.

Each integer with \(T_B(A+k)\le\nu/2\) contributes at least \(1/4\). For a natural \(r\le\nu/2\) and \(A>12B^8\), failure to have an injection from \(\operatorname{Fin}(r)\) into strict Type-II solutions at a prime implies membership in this lower-tail set. Therefore

\[
 \boxed{
 \#\{0\le k<H:A+k\text{ prime and lacks }r\text{ strict Type-II solutions}\}
 \le4\left[\frac{H(\nu_B+2\Lambda_B)}{\nu_B^2}
                 +(1+12B^8)^2\right].}                   \tag{9.3}
\]

The outer factor four multiplies the endpoint term. The case \(H=0\) is harmless. The division by zero case is excluded explicitly and is absent eventually by Section 6.

This is a fresh proof for the smaller family; it is not the invalid operation of replacing parameters in a theorem stated only for the original family.

## 10. Asymptotic intervals and global relative prime density

Let \(N\) be a sufficiently large integer, take

\[
 B=\lfloor N^{1/24}\rfloor,\qquad A=H=N.
\]

Then \(\log B\asymp\log N\), \(12B^8<N\) eventually, and

\[
 (1+12B^8)^2=O(N^{2/3}),\quad
 \nu_B\gg(\log N)^3/\log\log N,\quad
 \Lambda_B=o(1).
\]

In particular \(\nu_B+2\Lambda_B\le2\nu_B\) eventually. Formula (9.3) yields an exceptional count

\[
 O\!\left(\frac{N\log\log N}{(\log N)^3}+N^{2/3}\right)
 =O\!\left(\frac{N\log\log N}{(\log N)^3}\right).          \tag{10.1}
\]

To make the multiplicity threshold uniform in the prime, put
\(f(x)=(\log x)^3/\log\log x\) for sufficiently large \(x\). It is increasing eventually, and \(f(2N)\asymp f(N)\). By the lower mean estimate choose an absolute \(c>0\) so small that

\[
 r_N:=\lceil c f(2N)\rceil\le\nu_B/2
\]

for every sufficiently large \(N\). Formula (9.3) applies to this **integer** threshold. If a prime \(p\in[N,2N)\) has \(r_N\) distinct strict solutions, restricting the injection gives at least \(\lfloor c f(p)\rfloor\) such solutions. This proves (10.1) for the pointwise threshold, not only for a threshold depending on the interval.

For a global cutoff \(X\), sum dyadic intervals above \(\sqrt X\), where the logarithms are uniformly comparable with \(\log X\), and use the trivial count \(\sqrt X\) below that. The geometric sum of interval lengths is \(O(X)\). The result is

\[
 \#\{p_0\le p\le X:p\text{ prime and lacks }
          \lfloor c f(p)\rfloor\text{ strict Type-II solutions}\}
 \ll \frac{X\log\log X}{(\log X)^3}.                      \tag{10.2}
\]

Here \(p_0\) is a fixed sufficiently large integer, so no problematic small logarithms are used.

Finally one needs a denominator for a **relative prime-density** statement. An elementary bound suffices. For integer \(n\),

\[
 4^n/(2n+1)\le\binom{2n}{n}\le(2n)^{\pi(2n)}.
\]

For the upper inequality, the exponent of each prime in the binomial coefficient is a sum of zeros or ones over its prime powers, so the contribution of that prime is at most \(2n\). Taking logarithms gives \(\pi(X)\gg X/\log X\), first at even integers and then at all sufficiently large \(X\) by monotonicity. Dividing (10.2) by this lower bound shows that the relative exceptional prime proportion is

\[
 O\!\left(\frac{\log\log X}{(\log X)^2}\right)\longrightarrow0.
\]

This supplies the actual prime-density implication; an isolated algebraic logarithm comparison is not being called a density theorem. No prime number theorem is required.

## 11. Safe manuscript replacement and exact verification boundary

The original full-overlap assertion should not be marked proved on the basis of this note. The replacement narrative is:

> We restrict to delayed, truncated primitive-ray packets. This subfamily consists of authentic packets and still has mean of order \((\log Y)^3/\log\log Y\). A full-modulus determinant identity bounds common divisors between distinct rays by the square of the ray cutoff. Since the scale starts later, the reciprocal progression endpoint is controlled. An elementary third divisor-moment bound handles different rays, and a weighted gcd kernel handles the same rays. The resulting restricted overlap tends to zero. Applying the restricted finite second moment yields the stated abundance conclusion, with exceptional count \(O(N\log\log N/(\log N)^3)\).

For formalization status, add separately:

> The finite formal development previously described has not been upgraded by this mathematical argument. The new restricted family, its estimates, and the density assembly have not been checked by Lean. This note does not certify the integrated source build or the original full-family overlap estimate.

The source-level acceptance requirements are precise: define this finite subfamily with its actual cutoffs; prove parameter injectivity; prove the full-modulus identity (2.2); formalize (3.2), (4.3)–(4.5), (5.2)–(5.4), and (6.1)–(6.7); specialize the finite second moment without changing its counting conventions; and formalize the eventual/prime-density argument of Section 10. None of these requirements may be replaced by an axiom asserting its conclusion.

This manuscript-ready mathematical route removes the need to solve the earlier mixed first/first problem for the entire packet family. It does not pretend that the originally requested full-family estimate, or the Lean formalization of these replacement estimates, has been completed.
