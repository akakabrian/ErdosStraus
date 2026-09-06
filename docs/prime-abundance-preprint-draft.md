---
title: "A proposed density-one lower bound for strict Erdős–Straus solution counts"
author: "Brian Akaka"
date: "6 September 2026 — working draft v0.5"
lang: en
fontsize: 11pt
geometry: margin=1in
---

**Draft status.** This manuscript presents a proof for specialist scrutiny.
The prime exceptional-set lower bound and relative-density conclusion now
have an end-to-end Lean certificate through a restricted-subfamily argument.
The integer assertion, the manuscript's exact Proposition 3 route, the
published-upper-bound integration used for the exponent-matching corollary,
and the sharper Section 10 refinement are not all formalized in that
certificate. The work has not received independent human specialist review,
and literature-wide originality remains unestablished. This is not a proof
of the Erdős–Straus conjecture. License: Creative Commons Attribution 4.0
International (CC BY 4.0).

## Abstract

Let $R(n)$ count triples of positive integers $x<y<z$ satisfying
$4/n=1/x+1/y+1/z$. For a prime $p$, let $R_{\mathrm{II}}(p)$ count those
triples with $p\mid y,z$ and $(p,x)=1$. We present an argument for the
existence of an absolute constant $c>0$ such that
$$
\#\left\{p\le N:p\text{ prime},\ p\ge n_0,
 R_{\mathrm{II}}(p)<c\frac{(\log p)^3}{\log\log p}\right\}
\ll \frac{N(\log\log N)^3}{(\log N)^3}.
$$
Here $n_0$ is an absolute fixed threshold. The same exceptional-set estimate
holds for integers with $R(n)$ in place of $R_{\mathrm{II}}(p)$. The
arithmetic step is a weighted compatible-pair estimate for rough, possibly
composite witness moduli. An explicit second-moment argument transfers this
estimate to finite intervals, and an injective decoder gives strictly
ordered solutions. Combined with the published prime first-moment upper
bounds of Elsholtz and Tao, the proposed lower bound gives
$R_{\mathrm{II}}(p)=(\log p)^{3+o(1)}$ and $R(p)=(\log p)^{3+o(1)}$ on one
set of primes of relative density one. If valid, this improves the
density-one prime lower bound in Elsholtz–Tao's Theorem 1.8, replacing its
logarithmic exponent $(\log 3)/2$ by $3-o(1)$, already for strict Type-II
solutions. A separate proposed refinement to $\Delta=O(\mu)$ reduces the
exception bound to $O(N\log\log N/(\log N)^3)$; the main proof does not
depend on this refinement. Neither result gives a leading constant,
control every prime, or improve the classical zero-solution exceptional-set
benchmark. The arithmetic estimates and their applications are separated
to make the proof's dependencies explicit.

The prime lower-bound and relative-density assertion have also been proved
in Lean by an alternative argument using a genuine restricted subfamily and
weaker sufficient intermediate estimates. That certificate does not by
itself formalize the all-integer assertion or the published upper-bound input
used to identify the matching exponent as exactly three.

## 1. Statements and scope

All logarithms are natural. Constants in $\ll$ and $\asymp$ are absolute
unless a fixed divisor-function index is specified. All asymptotic assertions
concern sufficiently large arguments. Write $\tau_j$ for the $j$-fold
divisor function, $\tau=\tau_2$, $\omega$ for the number of distinct prime
factors, $\varphi$ for Euler's function, and $P^-(m)$ for the least prime
factor, with $P^-(1)=\infty$.

Define
$$
R(n)=\#\{(x,y,z)\in\mathbb N^3:1\le x<y<z,
 4/n=1/x+1/y+1/z\}.
$$
For prime $p$, $R_{\mathrm{II}}(p)$ imposes the additional conditions
$p\mid y$, $p\mid z$, and $(p,x)=1$. The subscript is tied to these
positions in the strictly ordered triple.

**Theorem 1 (proposed abundance bound).** There exist absolute constants
$c,C>0$ and $n_0>e^e$ such that, for all sufficiently large $N$,
$$
\#\left\{n_0\le n\le N:R(n)<c\frac{(\log n)^3}{\log\log n}\right\}
\le C\frac{N(\log\log N)^3}{(\log N)^3}. \tag{1}
$$
The same estimate holds when the set is replaced by
$$
\left\{n_0\le p\le N:p\text{ prime},\
R_{\mathrm{II}}(p)<c\frac{(\log p)^3}{\log\log p}\right\}. \tag{2}
$$

**Corollary 2 (proposed typical prime exponent).** There exists a set
$\mathcal P_0$ of primes such that
$$
\frac{\#\{p\le N:p\in\mathcal P_0\}}{\pi(N)}\longrightarrow1
$$
and, as $p\to\infty$ through this one set,
$$
\frac{\log R_{\mathrm{II}}(p)}{\log\log p}\longrightarrow3,
\qquad \frac{\log R(p)}{\log\log p}\longrightarrow3. \tag{3}
$$

Theorem 1 is deduced below from Proposition 3. Its deduction is independent
of how Proposition 3 is proved. Sections 5–9 give the proposed arithmetic
proof, using the specified classical analytic inputs. A reader questioning
one of those estimates can therefore still assess the conditional
implication separately. Section 10 presents a stronger overlap claim and
its sharper exception bound, with their additional argument and distinct
review status. Sections 2–9 and Corollary 2 do not depend on Section 10.

The exceptional proportion in (2) is
$O((\log\log N)^3/(\log N)^2)$ by the prime number theorem. It tends to
zero, but its counting bound tends to infinity. No assertion about the
remaining primes follows. In particular, (3) is not an asymptotic formula
$R(p)\sim C_0(\log p)^3$ and does not settle the conjecture.

### 1.1. Relation to earlier work

Elsholtz–Tao's Theorem 1.8 gives
$f(p)\ge(\log p)^{(\log 3)/2-o(1)}$ on a set of primes of relative
density one [ET, p. 56]. Theorem 1, if valid, improves this particular
lower-bound conclusion: it gives
$f(p)\ge R_{\mathrm{II}}(p)\ge c(\log p)^3/\log\log p$ on a set of
primes of relative density one, with an explicit exceptional-set estimate.
Thus the proposed lower logarithmic exponent increases from
$(\log 3)/2\approx0.5493$ to $3-o(1)$, even for the strict Type-II subset.
This comparison needs inclusion, not equality, of counting conventions.

This is not an improvement of every assertion in Theorem 1.8, nor of
Elsholtz–Tao's first-moment bounds in Theorem 1.1. Their upper bounds
supply the upper side of (3) and are credited as an input in Section 4.
Improving this identified 2013 conclusion, if the proof is correct, is a
precise comparison; being the first work to do so is a separate priority
claim that this draft does not make.

Elsholtz–Planitzer study related lower bounds with different quantifiers
[EP]. A statement on a density-one set of integers cannot, by itself, be
restricted to primes. Dahan studies closely related witness systems and
fixed and growing search depths [D, Sections 4.1–4.4]. These comparisons
must include consequences of prime-witness mass estimates, not just the
older printed exponent. This draft does not assert that all such
consequences or subsequent literature have been exhausted.

The candidate contribution here is the compatible-pair estimate and its
quantitative multiplicity consequence, not a new parametrization, CRT
identity, second-moment principle, or published upper bound. The classical
exceptional-set problem for *zero* solutions is different from (1)–(2).

## 2. Witness family and the arithmetic proposition

For $Y\to\infty$, put
$$
X=3Y,\qquad L=\log Y,\qquad w=L^{100}.
$$
Retain all rows
$$
M=3u\le X,\qquad Q=4M-1=12u-1,\qquad P^-(Q)>w.
$$
Both prime and composite $Q$ are included. Define
$$
S_M=\{s\in\mathbb N:1\le s<M,\ s\mid M^2\},\qquad
\mathcal A_Y=\{(Q,s):Q\text{ retained},\ s\in S_M\},
$$
$$
\mu=\sum_{(Q,s)\in\mathcal A_Y}\frac1Q.
$$
Each label has the unique squarefree representation
$$
s=rb^2,\qquad M=rbc,\qquad r\text{ squarefree},\quad b<c.
$$
Set $\kappa(s)=rb$ and $h_s=\operatorname{lcm}(3,\kappa(s))$.
For fixed $s$, the divisibility and row conditions, apart from $s<M$ and
roughness, are exactly $h_s\mid M$. Every label is coprime to its row modulus.

Define the unordered distinct-row overlap
$$
\Delta=\sum_{\substack{Q<Q'\text{ retained}\\g=(Q,Q')>1}}
\frac{g}{QQ'}
\#\{(s,t)\in S_M\times S_{M'}:s\equiv t\pmod g\}. \tag{4}
$$
All moduli and divisor sums retain full prime powers.

**Proposition 3 (arithmetic estimate claimed here).** For this family,
$$
\mu\asymp\frac{L^3}{\log w},\qquad
\Delta\ll L^3\log(2L). \tag{5}
$$
The stronger assertion $\Delta=O(\mu)$ is proposed separately in Section 10;
it is not an assumption of the main argument in Sections 2–9.

## 3. From arithmetic estimates to interval abundance

### 3.1. An injective strict decoder

**Lemma 4.** Suppose $n>Q$, $s\in S_M$, and $Q\mid n+4s$. Then
$$
x=\frac{nM+s}{Q},\qquad y=nM,\qquad z=\frac{nMx}{s} \tag{6}
$$
is a positive integer solution counted by $R(n)$. If $n=p$ is prime,
it is counted by $R_{\mathrm{II}}(p)$. For fixed $n$ the map is injective.

*Proof.* Since $4(nM+s)=n(Q+1)+4s$ and $(4,Q)=1$, $x$ is integral.
The equality $QMx=nM^2+Ms$, together with $s\mid M^2$ and $(s,Q)=1$,
implies $s\mid Mx$. Thus $z$ is integral and divisible by $n$.
The inequality $n>Q$ gives $x>M>s$, whence $z>y$. Also
$$
x<\frac{(n+1)M}{Q}\le\frac{n+1}{3}<n\le y,
$$
since $Q=4M-1\ge3M$ and $n>2$. Finally $Qx=nM+s$ gives
$4Mx=nM+x+s$, which is the desired reciprocal identity after division
by $nMx$. For prime $p$, $1\le x<p$ gives $(p,x)=1$. The inverse is
$$
M=y/n,\qquad Q=4M-1,\qquad s=Qx-nM. \tag{7}
$$
The triple is already strictly sorted, so this also rules out collisions
after sorting. $\square$

### 3.2. Complete-period variance and the interval endpoint

Put
$$
T_Y(n)=\sum_{(Q,s)\in\mathcal A_Y}\mathbf1_{Q\mid n+4s}.
$$
On the uniform probability space modulo the least common multiple of all
retained $Q$, its mean is $\mu$. Two indicators on different rows have
intersection probability $g/(QQ')$ when $s\equiv t\pmod g$, and zero
otherwise. For coprime rows the covariance is zero. Different labels on
one row are disjoint, since $s,t<M<Q$ and $(4,Q)=1$. Dropping negative
covariances therefore gives
$$
v:=\operatorname{Var}_{\mathrm{CRT}}(T_Y)\le\mu+2\Delta. \tag{8}
$$

Let $m=|\mathcal A_Y|$. Since $Q<12Y$, $m/\mu\le12Y$. The sum of absolute
formal coefficients of $F=1-T_Y/\mu$ is at most $1+12Y$. Each monomial
in its square is either identically zero or the indicator of one residue
class modulo its full least common multiple. On any interval $J$ of $H$
consecutive integers, such a class has counting error at most one.
Expanding the square and bounding the errors in absolute value yields
$$
\sum_{n\in J}\left(1-\frac{T_Y(n)}{\mu}\right)^2
\le H\frac{v}{\mu^2}+(1+12Y)^2. \tag{9}
$$
Consequently
$$
\#\{n\in J:|T_Y(n)-\mu|\ge\mu/2\}
\le4\left(H\frac{v}{\mu^2}+(1+12Y)^2\right). \tag{10}
$$
This retains the entire interval error; no equidistribution over a period
longer than $J$ has been assumed.

### 3.3. Proof of Theorem 1 from Proposition 3

By (5) and (8), $v/\mu^2\ll(\log L)^3/L^3$. On
$J=(N/2,N]\cap\mathbb Z$, choose $Y=N^{1/3}$. For sufficiently large
$N$ all $n\in J$ exceed $12Y$, and (10) implies, apart from
$$
O\left(\frac{N(\log\log N)^3}{(\log N)^3}+N^{2/3}\right)
$$
integers, that $T_Y(n)\ge\mu/2\gg(\log N)^3/\log\log N$.
Lemma 4 gives $R(n)\ge T_Y(n)$ and $R_{\mathrm{II}}(p)\ge T_Y(p)$.
Choose a single sufficiently small absolute $c$ for all large dyadic blocks.

To sum to $N$, discard the integers below $\sqrt N$. In the remaining
dyadic blocks logarithms are comparable to $\log N$; the block lengths
sum to $O(N)$ and the endpoint errors sum to $O(N^{2/3})$. Both the discarded
prefix and the endpoints are absorbed in (1). The prime assertion follows
from the same blockwise argument: any prime failing the Type-II threshold
must be among the integers failing the packet threshold. This is stronger
than merely restricting a density-one statement about $R(n)$. $\square$

## 4. The published upper side and proof of Corollary 2

With the notation of Elsholtz–Tao [ET, Theorem 1.1 and equation (1.4),
pp. 53–54],
$$
\sum_{p\le N}f_{\mathrm{II}}(p)\ll N(\log N)^2,\qquad
\sum_{p\le N}f(p)\ll N(\log N)^2\log\log N. \tag{11}
$$
Their unrestricted solution count includes every strictly ordered triple
here. Their Type-II count fixes the same divisibility positions and
includes ours. Thus
$$
R_{\mathrm{II}}(p)\le f_{\mathrm{II}}(p),\qquad R(p)\le f(p).
$$
There is no use of $R(p)\le f_{\mathrm{II}}(p)$ or an equality of conventions.

Markov's inequality on dyadic blocks, followed by summation above $\sqrt N$,
shows that the primes violating
$R(p)\le C_1(\log p)^3(\log\log p)^2$ have relative density zero. This
upper-tail consequence is already contained in [ET, p. 54], not a new result.
Intersect its complement with the complement of the exceptional set (2).
The resulting single set $\mathcal P_0$ has relative density one and satisfies
$$
c\frac{(\log p)^3}{\log\log p}
\le R_{\mathrm{II}}(p)\le R(p)
\le C_1(\log p)^3(\log\log p)^2
$$
for sufficiently large $p\in\mathcal P_0$. Taking logarithms proves (3),
since $\log\log\log p=o(\log\log p)$. $\square$

## 5. Analytic inputs and the mean estimate

### 5.1. Uniform linear-polynomial upper bounds

We use the following consequences of Henriot's corrected upper theorem
[H, HE, New Theorem 5, p. 377]. For fixed $j\ge1$, integer $1\le A\le16x^2$,
and $x\ge1$, with positive polynomial values,
$$
\sum_{x<v\le2x}\tau_j(Av-1)\ll_j x\log(2x)^{j-1}, \tag{12}
$$
$$
\sum_{x<v\le2x}\mathbf1_{P^-(Av-1)>w}
\ll\frac{xG(A)}{\log(2\min(w,x))},\qquad G(A)=A/\varphi(A). \tag{13}
$$
In the corrected theorem take degree $1$, $\alpha=1/2$, $\delta=1/4$,
and $\varepsilon=1/1000<1/500$. The coefficient condition is uniform
because $x\ge C_0(A+1)^{1/4}$ for all sufficiently large $x$ in this range.
For $p\nmid A$ the exact valuation-$e$ density, $e\ge1$, is
$(p-1)/p^{e+1}$; for $p\mid A$ it is zero. Euler-product bounds give
(12)–(13). The multiplicative-function growth constants can be chosen
independently of the roughness cutoff. Bounded $x$ has bounded $A$;
the denominator in (13) stays bounded even if the value $1$ is retained.
Only the corrected upper theorem is used, not Henriot's lower theorem.

The other classical inputs are the dimension-one lower fundamental lemma
of sieve theory, Mertens' estimates, the prime number theorem, and the
standard harmonic divisor sums
$\sum_{m\le Z}\tau_j(m)/m\ll_j\log(2Z)^j$.
The precise lower-sieve application is given next; [HR] is the general
reference. The final submission must pin its exact theorem locator.

### 5.2. Lower mean

For $(u,6)=1$,
$$
|S_{3u}|=\frac{3\tau(u^2)-1}{2}\ge\tau(u^2)
=\sum_{a\mid u}2^{\omega(a)}.
$$
Hence
$$
\mu\ge\frac1{12}
\sum_{\substack{am\le Y\\(am,6)=1\\P^-(12am-1)>w}}
\frac{2^{\omega(a)}}{am}. \tag{14}
$$
Restrict $a\le Y^{2/3}$ and put $H=Y/a$. For
$\sqrt H\le T\le H/2$ and squarefree $e$ supported on primes at least
$5$ not dividing $a$, CRT gives
$$
\#\{T<m\le2T:(m,6)=1,\ e\mid12am-1\}
=\frac{T}{3e}+O(1). \tag{15}
$$
There are two classes modulo $6e$, giving an absolute error. Use lower-sieve
weights of level $T^{1/4}$. Uniformly in these parameters,
$\log(T^{1/4})/\log w\to\infty$, and the summed $O(1)$ remainders are
$O(T^{1/4})=o(T/\log w)$. The local forbidden density is $1/p$ for
$p\ge5$, $p\nmid a$, and zero at primes dividing $a$. The local product
is therefore $\gg1/\log w$, uniformly in $a$. The fundamental lemma
gives $\gg T/\log w$ surviving $m$ in each block.

Summing harmonically over these blocks gives $\gg\log H/\log w$.
The standard estimate
$\sum_{a\le Z,(a,6)=1}2^{\omega(a)}/a\asymp(\log Z)^2$, together
with $\log(Y/a)\ge L/3$, proves $\mu\gg L^3/\log w$.

### 5.3. Upper mean and two weighted moments

In a dyadic box $r\asymp U,b\asymp B,c\asymp C$, choose a largest
coordinate scale $H_1$. Fix the other coordinates; the linear coefficient
is four times their product and is at most $16H_1^2$. Use (13), drop
positive restrictions, and average
$G(4ab)\le2G(a)G(b)$ with $\sum_{j\le T}G(j)\ll T$.
A nonempty rough box has $w<32H_1^3$, so
$\log(2\min(w,H_1))\gg\log w$. Its reciprocal weighted contribution is
$O(1/\log w)$. There are $O(L^3)$ boxes, proving the upper mean in (5).

The same largest-coordinate argument using (12) gives, for $j=2,3$,
$$
\mathcal S_j:=\sum_{(Q,s)\in\mathcal A_Y}\frac{\tau_j(Q)}Q
\ll L^{j+2}, \tag{16}
$$
$$
\sum_{(Q,s)\in\mathcal A_Y}\frac{\tau(Q)}Q
\frac bc\log(2Lc/b)\ll L^3\log(2L). \tag{17}
$$
Indeed, (12) costs $L^{j-1}$ per reciprocal weighted box. For (17),
summing over the dyadic difference of the $b,c$ scales uses
$\sum_{h\ge0}2^{-h}(\log(2L)+h)\ll\log(2L)$; only two independent
scale sums remain, alongside the single $L$ from the divisor average.
Boundary boxes with a coordinate $1$ are included.

## 6. Positive divisor expansion and the tail

For a full divisor $d>1$ of a retained modulus and a literal label $s\le X$,
write
$$
H_{s,d}=\sum_{\substack{Q=dq\text{ retained}\\s\in S_{(Q+1)/4}}}\frac1{dq}.
$$
If this is nonempty, let $q_0$ be its **first retained** cofactor and set
$$
B_{s,d}=\begin{cases}(dq_0)^{-1},&q_0=1\text{ or }w<q_0<h_s/L,\\
0,&\text{otherwise},\end{cases}\qquad T_{s,d}=H_{s,d}-B_{s,d}.
$$
Both are zero for an empty sum. Every eligible cofactor satisfies
$dq\equiv-1\pmod{4h_s}$ and $(dq+1)/4>s$. The congruence is one residue
class because $(d,4h_s)=1$. Proper retained cofactors exceed $w$.
After $q_0$ their spacing is at least $4h_s$; a first term assigned to
$T$ has mass at most $L/(dh_s)$. Harmonic summation yields
$$
0\le T_{s,d}\ll\frac{L}{d\kappa(s)}. \tag{18}
$$

For $a\in(\mathbb Z/d\mathbb Z)^\times$, set
$b_{d,a}=\sum_{s\equiv a(d)}B_{s,d}$ and
$t_{d,a}=\sum_{s\equiv a(d)}T_{s,d}$. Use the norm
$$
\|v\|^2=\sum_{d>1}\varphi(d)\sum_{a\in(\mathbb Z/d\mathbb Z)^\times}v_{d,a}^2.
$$
Expanding $\|b+t\|^2$ sums **ordered** packet pairs and every divisor
$d>1$ of $\gcd(Q,Q',s-t)$. Its coefficient for a packet pair is exactly
$$
\frac{\gcd(Q,Q',s-t)-1}{QQ'}, \tag{19}
$$
with $\gcd(Q,Q',0)=\gcd(Q,Q')$. If the pair contributes to (4), its two
orientations contribute $2(g-1)/(QQ')\ge g/(QQ')$. All other terms are
nonnegative. Therefore
$$
\Delta\le\|b+t\|^2. \tag{20}
$$
Neither same-row terms nor partially compatible divisors are deleted.

The representation $s=rb^2$ gives
$\sum_{s\le X}\kappa(s)^{-2}\ll1$ and
$\sum_{s\le X}\kappa(s)^{-1}\ll L^2$. Rough harmonic summation gives
$$
\sum_{\substack{1<d\le4X\\P^-(d)>w}}\frac1d\ll\frac L{\log w}.
$$
For $0<|s-t|\le X$, the positive full-prime-power Euler product gives
$$
\sum_{\substack{d\mid |s-t|\\d>1,\ P^-(d)>w}}\frac1d
\ll\frac{L}{w\log w};
$$
there are $O(L/\log w)$ possible prime factors, each exceeding $w$.
Using $\varphi(d)\le d$ in (18), equal literals contribute
$O(L^3/\log w)$ and unequal literals $O(L^7/(w\log w))$. Thus
$$
\|t\|^2\ll\frac{L^3}{\log w}+\frac{L^7}{w\log w}=O(\mu). \tag{21}
$$

## 7. Primitive rays and nested pairs

### 7.1. Ray counting with all multiples included

Consider an anchor $s=rb^2$, $M=rbc$, and a compatible partner
$t=r'\beta^2$, $M'=r'\beta c'$. Let $d$ divide both row moduli and
assume $s\equiv t\pmod d$. Put
$$
\gamma=\frac{\operatorname{lcm}(3,r'\beta)}{r'\beta}\in\{1,3\},\quad
a=c'/\gamma,\quad \ell=(a,\beta),\quad
a=\ell a_0,\quad \beta=\ell\beta_0,\quad D_0=a_0\beta_0.
$$
Writing $Q'=d\nu$ gives
$$
4\gamma s a_0\equiv\beta_0\pmod d,\qquad
d\nu+1=4\gamma D_0r'\ell^2,\qquad
\beta_0<\gamma a_0,\quad(a_0,\beta_0)=1. \tag{22}
$$
All cancelled factors are units modulo $d$. For fixed primitive ray,
$\gamma$, and $\nu$, unique squarefree decomposition determines at most
one pair $(r',\ell)$, hence one original label. Also
$(d,4\gamma D_0)=1$. The number of occurrences with $V\le\nu<2V$ is at
most $V/(4\gamma D_0)+1$. The endpoint is charged once per primitive ray,
not once per multiple.

Distinct positive primitive vectors in this congruence lattice have a
nonzero determinant divisible by $d$. In a rectangle
$a_0\asymp U,\beta_0\asymp B$, slopes are separated by $\gg d/U^2$,
so there are $O(1+UB/d)$ vectors. Covering a product shell by
$O(\log(2D))$ such rectangles gives $O(\log(2D)(D/d+1))$ rays. Thus,
if all products considered satisfy $D_0\ge d_0\ge1$,
$$
\#\{D_0\le T\}\ll T\log(2T)/d+\log^2(2T),
$$
$$
\sum_{d_0\le D_0\le T}\frac1{D_0}
\ll\frac{\log^2(2T)}d+\frac{\log(2d_0)}{d_0}. \tag{23}
$$
The counts and sums in (23) range over primitive rays, not merely distinct
integer values of their products. These bounds include unbalanced rectangles.

### 7.2. Complete nested mass

Let $\mathcal N$ be the sum of $1/Q'$ over compatible labels on retained
rows $Q<Q'$ with $Q\mid Q'$. Then $Q'=Q\nu$ with $\nu>w$.
The vector $(c,\gamma b)$ is parallel to the anchor. For a partner of
unequal slope the determinant has absolute value at least $Q$; hence
$$
D_0\ge\min\left(\frac{Q^2}{4\gamma c^2},\frac Q{2\gamma b}\right)
\ge\tfrac12\min((rb)^2,rc). \tag{24}
$$
For example, one of $c\beta_0$ or $\gamma ba_0$ is at least $Q/2$;
use $\beta_0<\gamma a_0$ in the first case and $\beta_0\ge1$ in the second.

Set $d_0=\max(1,\min((rb)^2,rc)/2)$. For $r'>R$, (22) gives
$D_0<QV/R$. Equations (22)–(24) bound the weighted mass in a cofactor
block for fixed $Q,s,\gamma$ by
$$
\ll\frac{L^2}{Q^2}+\frac{\log(2d_0)}{Qd_0}
+\frac{L}{QR}+\frac{L^2}{QV}. \tag{25}
$$
The sum of its second term over labels is $O(L)$, by enlarging to the
positive sums
$$
\sum_{rbc\le X,\ b<c}\frac{\log(2rb)}{r^3b^3c}=O(L),\qquad
\sum_{rbc\le X,\ b<c}\frac{\log(2rc)}{r^2bc^2}=O(1).
$$
Summing the cofactor blocks, using $\sum_V1/V\ll1/w$ and
$\sum_{Q,s}Q^{-2}\le\mu/w$, proves
$$
\mathcal N_{\mathrm{nonparallel},\ r'>R}
\ll L^2+\mu(L^3/w+L^2/R). \tag{26}
$$

Here is the remaining cover of the nested mass. Same-literal later rows
satisfy $Q\nu\equiv-1\pmod{4h_s}$ and $Q\equiv-1\pmod{4h_s}$,
so $\nu\equiv1\pmod{4h_s}$. The retained anchor is the first cofactor,
$\nu=1$; every later cofactor is at least $1+4h_s$. All same-literal
later terms therefore lie in the tail and cost
$O(L\sum_{rbc\le X}1/(r^2b^2c))=O(L^2)$.

For unequal literals, $t=s+kQ>Q$. Put $W=2^{\omega(Q)}$. The inequality
$1/\kappa(t)\le\sum_{d_1^2u=t}1/(d_1u)$ and the bound of $W$ unit
quadratic roots modulo the full odd $Q$ give, for dyadic $D,U$,
$$
\#\{d_1\asymp D,u\asymp U:d_1^2u\equiv s\pmod Q\}
\ll\min\{D(U/Q+1),WU(D/Q+1)\}.
$$
After reciprocal weighting this is bounded by a constant times
$W/Q+\min(1/U,W/D)$, with the important restriction $D^2U>Q/8$.
Let $D_*=(QW)^{1/3}$. For $D\le D_*$ the endpoint sum is
$O(D^2/Q)$. For $D>D_*$, retain
$U_{\min}=\max(1,Q/(8D^2))$. Then
$$
\sum_{U\ge U_{\min}\text{ dyadic}}\min(1/U,W/D)
\ll\frac WD\left(1+\log^+\frac{8D^3}{QW}\right).
$$
At $D\asymp2^jD_*$ this is $O((W/D_*)2^{-j}(1+j))$, a summable
series in both regimes of $U_{\min}$. No extra logarithm is introduced.
Consequently
$$
\sum_{\substack{Q<t\le X\\t\equiv s\ (Q)}}\frac1{\kappa(t)}
\ll W^{2/3}Q^{-1/3}+L^2W/Q. \tag{27}
$$
Weighted Cauchy–Schwarz, $|S_M|\le\tau_3(M)$,
$\tau_3(M)^2\le\tau_9(M)$ and $4^{\omega(Q)}\le\tau_4(Q)$ give
$\sum_{Q,s}W/Q\ll L^{13/2}$. Thus (18) and (27) bound all unequal-literal
tails and soft first terms by
$$
O(L^{15/2}w^{-1/3}+L^{19/2}/w). \tag{28}
$$

For squarefree $r'\le R$, a label $t=r'\beta^2\equiv s\pmod Q$ has at
most $W$ unit root classes; nonunit $r'$ contributes none. Each label has
at most one selected first row, of weight at most
$\min(1/(Qw),1/(3r'\beta^2))$. Split at
$U=\sqrt{Qw/r'}<Q$. Each class has at most one representative below $U$;
the tail includes both its first term and its spacing-$Q$ integral.
Its mass is $O(1/(Qw))$. Summing gives
$$
O((R/w)L^{13/2}). \tag{29}
$$

For parallel pairs write $b=jB,c=jC$, $(B,C)=1$. Necessarily
$\beta=\lambda B$, $c'=\lambda C$, and
$$
r'\lambda^2=rj^2+kQ,\qquad k\ge1,\qquad \nu=1+4kBC.
$$
Squarefree decomposition is unique. Retaining the finite later-row cutoff
and $\nu>w$ gives mass per anchor $O(1/(Qw)+L/(QBC))$.
The total is $O(\mu/w+L^2)$, since
$\sum_{rj^2BC\le X}1/(rj^2B^2C^2)=O(L)$.

Taking $R=L^{93}$ in (26), (28), and (29), and using $w=L^{100}$ and
the elementary bound $\mu=O(L^3)$, proves
$$
\mathcal N\ll L^2. \tag{30}
$$
The decomposition uses the first *retained* row throughout. Unretained
eligible rows add no mass, and all subsequent eligible rows obey the same
spacing bound. The square case $r'=1$ is included in (29).

## 8. Equal slopes and hard proper first cofactors

### 8.1. Equal slopes

There is also a unique representation
$M=kxy,s=kx^2$ with $x<y$ and $(x,y)=1$. Put $a=xy$ and $Q_k=4ak-1$.
Then
$(Q_k,Q_{k'})=(Q_k,k'-k)$, and this divides $s_{k'}-s_k$.
For $d\mid Q_k$, later rows divisible by $d$ have $k'=k+jd$, $j\ge1$,
and their reciprocal sum is $O(L/(ad))$. Thus the equal-slope
off-diagonal expanded mass for fixed $x,y$ is at most
$$
\frac{CL}{a^2}\sum_{k\le X/a}\frac{\tau(4ak-1)}k.
$$
Divisor pairing gives
$\sum_{k\le H}\tau(4ak-1)\ll H\log(2aH)+\sqrt{aH}$.
Partial summation bounds the displayed reciprocal sum by
$O(L^2+\sqrt a)$. Both $\sum_{x<y}(xy)^{-2}$ and
$\sum_{x<y}(xy)^{-3/2}$ converge. Including the diagonal, whose total
is at most $\mu$, the complete equal-slope contribution is $O(L^3)$.

### 8.2. Unequal slopes at a hard anchor

Now $d$ is an arbitrary divisor in (19), not necessarily the full gcd.
A hard proper first anchor has
$$
Q=dq=4rbc-1,\qquad w<q<h_s/L\le3rb/L,
$$
so $d>Lc$. Applying the determinant argument modulo $d$ gives
$$
D_0\ge\min\left(\frac{d^2}{4\gamma c^2},\frac d{2\gamma b}\right)
>\min(L^2/12,Lc/(6b)).
$$
The reciprocal-shell endpoint in (23) is therefore
$O(F_L(b,c))$, where
$$
F_L(b,c)=\frac{\log(2L)}{L^2}+\frac{b\log(2Lc/b)}{Lc}. \tag{31}
$$
For any retained unequal-slope partner $Q'=d\nu$, $\nu>w$, $r'>R$,
the weight is $\varphi(d)/(QQ')\le1/(Q\nu)$. As in (25), a cofactor
block contributes
$$
\ll\frac{L^2}{Qd}+\frac{F_L(b,c)}Q+\frac{L}{QR}+\frac{L^2}{QV}.
\tag{32}
$$
This estimate does not require the partner to be first or hard, and allows
$Q'=Q$. Summing cofactor blocks and divisors $d\mid Q$, using $d>w$
and (16)–(17), gives
$$
\text{large-squarefree-part mass}
\ll L^3\log(2L)+L^6/R+L^7/w. \tag{33}
$$
In particular its endpoint is
$L\sum_{Q,s}\tau(Q)F_L(b,c)/Q$; the first part is
$(\log(2L)/L)\mathcal S_2$ and the second is (17). There is no
pointwise substitution $\tau(Q)\ll\log Q$.

For squarefree $r'\le R$, only first partners enter $\|b\|^2$. The label
$r'\beta^2$ occupies at most $2^{\omega(d)}$ unit root classes modulo
$d$ and selects at most one $B$ row. Its weight is at most
$\min(1/(Qw),d/(3Qr'\beta^2))$. Split at $U=\sqrt{dw/r'}<d$.
The first term and integral tail in each class have combined mass
$O(1/(Qw))$. Since
$$
\sum_{d\mid Q}2^{\omega(d)}=\tau(Q^2)\le\tau_3(Q),
$$
(16) yields
$$
\text{small-squarefree-part first-partner mass}\ll R L^5/w. \tag{34}
$$
This is not asserted for all small-squarefree-part later rows; their
contribution is already assigned to the tail norm (21).

## 9. Completion of the proposed overlap proof

The positive expansion of $\|b\|^2$ has the following exhaustive cover.

1. If either selected cofactor is $1$, then $d$ equals that row modulus.
   The diagonal and both nested orientations cost at most $\mu+2\mathcal N$.
2. Equal slopes cost $O(L^3)$ by Section 8.1.
3. Otherwise both selected cofactors are hard and proper, with unequal
   slopes. Split the partner's squarefree part at $R$ and apply (33) or (34).
   Its first-row property in (34) follows from membership in $B$.

The cover may overlap, which only enlarges a positive upper bound. It
includes same-row different-label pairs for proper $d$. The cutoff here
can be chosen independently of the cutoff used to prove (30). Taking
$R=L^{10}$ and $w=L^{100}$ gives
$$
\|b\|^2\ll\mu+\mathcal N+L^3+L^3\log(2L)
+L^6/R+L^7/w+RL^5/w\ll L^3\log(2L).
$$
Combine this with (21) and
$\|b+t\|^2\le2\|b\|^2+2\|t\|^2$ to obtain
$\|b+t\|^2\ll L^3\log(2L)$. Equation (20) proves the second estimate
in (5); Section 5 proves the first. This completes the proposed argument
for Proposition 3 and hence Theorem 1. $\square$

## 10. A separate proposed $O(\mu)$ strengthening

**Status of this section.** The following refinement comes from a separate
internally audited argument. It has not received the same scope of completed
external-model review as Sections 2–9, independent human specialist
certification, or a complete Lean certificate. The completed Lean certificate
for the weaker prime exceptional-set rate does not establish this sharper
claim. Its inclusion records the strengthening without making Theorem 1
depend on it.

**Proposition 5 (proposed stronger overlap).** With exactly the family,
first-retained-cofactor split and norm of Sections 2 and 6,
$$
\|b\|^2=O(\mu),\qquad \|t\|^2=O(\mu),\qquad
\Delta=O(\mu). \tag{35}
$$

**Corollary 6 (proposed sharper exception bound).** Subject to Proposition 5,
the right-hand side of (1), and the bound for (2), can be replaced by
$$
C\frac{N\log\log N}{(\log N)^3}. \tag{36}
$$
The lower threshold is unchanged. The relative prime exception bound is
$O(\log\log N/(\log N)^2)$, and Corollary 2 is unchanged.

### 10.1. Retaining roughness in the divisor moments

For $j=2,3$, apply the corrected upper theorem [HE] with the same parameters
as Section 5.1 to the nonnegative multiplicative function
$$
f_{j,w}(m)=\tau_j(m)\mathbf1_{P^-(m)>w},\qquad f_{j,w}(1)=1.
$$
Its growth constants are independent of $w$: it is multiplicative on
coprime inputs, $\tau_j(p^e)\le j^e$, and
$\tau_j(m)\ll_{j,\varepsilon}m^\varepsilon$. Zero values are allowed
by the upper theorem; no positive lower-growth hypothesis is used.

For $p\nmid A$, upper-bound local factors after the sieve prefactor are
$1-1/p$ for $p\le\min(w,x)$ and $(1-1/p)^{-(j-1)}$ for $w<p\le x$.
For $p\mid A$ the factor is $1$. The removed small-prime sieve factors
cost at most $G(A)=A/\varphi(A)$; removed large-prime factors only decrease
the upper bound. Thus the refinement of (12)–(13) is
$$
\sum_{x<v\le2x}f_{j,w}(Av-1)
\ll_j\frac{xG(A)\log(2x)^{j-1}}{\log(2\min(w,x))^j},
\qquad 1\le A\le16x^2. \tag{37}
$$
Bounded $x$ is handled as in Section 5.1, including the retained value $1$.

The coefficient correction must be averaged, not treated as a bounded
pointwise constant. Writing $\mu_{\mathrm{Mob}}$ for the Möbius function,
$$
G(n)=\sum_{d\mid n}\frac{\mu_{\mathrm{Mob}}(d)^2}{\varphi(d)},\qquad
\sum_{n\le T}G(n)\le T\prod_p\left(1+\frac1{p(p-1)}\right)\ll T.
$$
Together with $G(4uv)\le2G(u)G(v)$, the largest-coordinate dyadic
argument of Section 5.3 now proves
$$
\mathcal S_j\ll\frac{L^{j+2}}{(\log w)^j},\quad j=2,3,
\qquad
\mathcal J:=\sum_{Q,s}\frac{\tau(Q)}Q\frac bc\log(2Lc/b)
\ll\frac{L^3\log(2L)}{(\log w)^2}. \tag{38}
$$
Indeed every nonempty rough box has $w<32H_1^3$, so its denominator
in (37) is bounded below by a constant times $(\log w)^j$ even when
$H_1<w$. Averaging $G$ in the two fixed coordinates then gives the same
scale sums as before, with these extra denominators retained.

### 10.2. Equal slopes and the exceptional coefficient range

The equal-slope estimate of Section 8.1, retaining roughness on the
earlier row, gives off-diagonal mass at most
$$
CL\sum_{x<y,(x,y)=1}a^{-2}
\sum_{\substack{k\le X/a\\P^-(4ak-1)>w}}\frac{\tau(4ak-1)}k,
\qquad a=xy. \tag{39}
$$
Split into $k\ge a$ and $k<a$. In a dyadic block $k\asymp H$ meeting
the first range, $A=4a\le8H\le16H^2$. A retained term also forces
$w<16H^2$, so (37) with $j=2$ applies with denominator comparable to
$(\log w)^2$. Dividing by $k\asymp H$ and summing blocks bounds this
inner sum by $O(G(4a)L^2/(\log w)^2)$. Since
$\sum_{x<y}G(4xy)/(xy)^2$ converges, the contribution to (39) is
$O(L^3/(\log w)^2)$.

For $k<a$, roughness forces $a>\sqrt{w/4}$. The elementary divisor bound
$\tau(m)\ll m^{1/8}$ gives
$\sum_{k<a}\tau(4ak-1)/k\ll a^{1/4}$. There are at most
$\tau(a)\ll a^{1/8}$ slopes with product $a$. This part of (39) is
$$
\ll L\sum_{a>\sqrt{w/4}}a^{-2+1/4+1/8}
\ll Lw^{-5/16}\ll Lw^{-1/4}.
$$
It is not fed to (37) outside that theorem's coefficient range. Adding
the diagonal of mass at most $\mu$, the full equal-slope contribution is
$$
\ll\mu+\frac{L^3}{(\log w)^2}+Lw^{-1/4}=O(\mu). \tag{40}
$$

### 10.3. Reusing the geometry with the sharper moments

The determinant, primitive-ray, first-partner and tail estimates of
Sections 6–8 remain unchanged. The endpoint from (31)–(32) is now
$$
E:=L\sum_{Q,s}\frac{\tau(Q)}QF_L(b,c)
\ll\frac{\log(2L)}L\mathcal S_2+\mathcal J
\ll\frac{L^3\log(2L)}{(\log w)^2}=O(\mu). \tag{41}
$$
For the large-squarefree-part partners, (32) summed over divisors and
cofactor blocks gives
$$
\ll E+(L^2/R+L^3/w)\mathcal S_2
\ll E+\frac{L^6}{R(\log w)^2}+\frac{L^7}{w(\log w)^2}.
$$
The small-squarefree-part **first** partners contribute
$(R/w)\mathcal S_3\ll RL^5/(w(\log w)^3)$. These are the same partner
classes as in (33)–(34), with (38) substituted for (16)–(17).

Use the complete positive cover of Section 9, (30), (40) and (41).
With $R=L^{10}$ and $w=L^{100}$,
$$
\begin{split}
\|b\|^2\ll{}&\mu+L^2+\frac{L^3}{(\log w)^2}+Lw^{-1/4}
+\frac{L^3\log(2L)}{(\log w)^2}\\
&+\frac{L^6}{R(\log w)^2}+\frac{L^7}{w(\log w)^2}
+\frac{RL^5}{w(\log w)^3}=O(\mu).
\end{split} \tag{42}
$$
Equation (21) already gives $\|t\|^2=O(\mu)$. Therefore (20) and the
norm-square inequality used in Section 9 give $\Delta=O(\mu)$,
completing the proposed proof of Proposition 5.

Finally (8) gives $v=O(\mu)$, so (10) costs
$O(H/\mu+Y^2)$ instead of $O(H(\log L)^3/L^3+Y^2)$.
The same choice $Y=N^{1/3}$ and dyadic summation prove (36).
The proposed improvement is a factor $(\log\log N)^2$ in the
exception bound, not a higher typical exponent or a universal assertion.
No full-period exponential no-hit theorem or exponential interval
admission statement is needed or claimed by this strengthening. $\square$

## 11. Verification, provenance, and limitations

The mathematics above is the basis of the claim, not agreement among
reviewers. AI systems were used substantially in developing arguments,
checking identities, exploring counterexamples, reviewing drafts and
sources, and implementing partial Lean formalizations. The project has
used OpenAI Codex models and Anthropic Claude models. Such assistance and
internal cross-checking do not constitute independent human peer review.
No AI system is listed as an author. Brian Akaka is the sole author and
is responsible for the manuscript's public claims.

### 11.1. Scope of the Lean formalizations

There are two complementary formal artifacts. The earlier finite artifact
checks a concrete witness-to-abundance implication for the Section 2 packet
family and includes the composite quadratic-root and interval helpers
described below. A separate analytic artifact now gives an end-to-end proof
of the prime exceptional-set lower bound and its relative-density conclusion.
The latter uses a genuine restricted subfamily of the Section 2 witnesses,
not an abstract mean or overlap hypothesis.

In the end-to-end artifact, put $B=2^n$. The selected parameters satisfy
$$
K\le a<b\le B,\qquad (a,b)=1,\qquad B^4<u\le B^6,
$$
and define
$$
M=3abu,\qquad s=3a^2u,\qquad Q=12abu-1.
$$
The actual roughness cutoff is
$\lfloor(\log(B^8))^{100}\rfloor$. These are valid members of the broader
family in Section 2. The formal proof establishes, eventually,
$$
\mu(2^n)\ge \frac{n^3}{A\log(n+1)},\qquad
\Delta(2^n)\le Dn^3
$$
for explicit positive constants $A,D$. These weaker sufficient estimates
imply the original prime exceptional-set rate; no upper mean estimate,
Henriot theorem, prime number theorem, or unproved analytic interface is
assumed.

For natural $Y,A,H,r$, assume $\mu_Y>0$, $12Y<A$ and $r\le\mu_Y/2$.
Let $\mathcal B_{\mathrm{II}}(A,H;r)$ consist of primes in $[A,A+H)$
which do not admit $r$ distinct strictly ordered Type-II solutions. The
finite formal theorem establishes
$$
|\mathcal B_{\mathrm{II}}(A,H;r)|
\le4\left[
\frac{H(\mu_Y+2\Delta_Y)}{\mu_Y^2}+(1+12Y)^2
\right]. \tag{43}
$$
In Lean, having at least $r$ solutions is expressed by an injective map
from $\operatorname{Fin}(r)$ to the type of strict solutions, with the
Type-II conditions on every image. Thus (43) counts failure of distinct
solutions, not failure of distinct parameter descriptions. Its declaration
is `interval_prime_typeII_bad_card_le` in `Conditional.lean`.

The checked chain includes decoder integrality and strict order, prime
Type-II conditions and injectivity, exact single/pair CRT probabilities,
the factor-two passage from the unordered overlap to the variance budget,
two-sided residue-count endpoint bounds, and the full endpoint term in
(43). The theorem assumes no analytic bound on $\mu_Y$ or $\Delta_Y$.
The positivity assumption is explicitly satisfiable: a checked example
has $\mu_1>0$. This example does not establish an admissible positive
threshold $r$ or an informative numerical instance of (43); eventual
usefulness still depends on the analytic estimates.

Supporting checked lemmas include positive full-divisor expansion,
primitive-ray determinant bounds, squarefree-scale uniqueness, at most
two unit square roots of a unit modulo an odd prime power, and
arithmetic-progression reciprocal sums. The two independently developed
packet models and their mean/overlap definitions are also proved equal.

The composite quadratic-root step is now checked as well. Write
$\rho(q,u)=\#\{x\in\mathbb Z/q\mathbb Z:x^2=u\}$. For every positive
$q$ and integer target $a$, the formalization proves the exact product
$$
\rho(q,a)=\prod_{p\mid q}\rho(p^{v_p(q)},a).
$$
Every local modulus is the full prime power, not its radical. For odd
$q>0$ and a unit $u$, the checked cardinality is either $0$ or
$2^{\omega(q)}$, and hence at most $2^{\omega(q)}$. Solubility is not
assumed merely from unitness. The modulus $q=1$ is included: its unique
residue contributes one root and the prime-factor product is empty.

For natural $A,H$ the checked interval corollary is
$$
\#\{0\le k<H:(A+k)^2\equiv u\pmod q\}
\le \rho(q,u)\bigl(\lfloor H/q\rfloor+1\bigr).
$$
It requires only $q>0$; the odd-unit case replaces $\rho(q,u)$ by
$2^{\omega(q)}$. Thus the endpoint allowance is per root class, not one
for the entire congruence. The empty interval is separately checked to
have zero hits. These declarations are in `CompositeQuadraticRoots.lean`
and `IntervalQuadraticRoots.lean`; this elementary finite-interval fact
is not the outstanding analytic interval theorem for ESC exceptions.

An earlier formal lower-sieve interface incorrectly quantified an
arbitrary roughness cutoff. Its falsity is now proved in Lean, and it is
not an assumption of (43). The replacement fixes the cutoff as a function
of $Y$, explicitly quantifies all $Y\ge Y_0$ for a uniform threshold
$Y_0$, and retains the ranges in Section 5.2; its analytic lower bound is
still an unproved proposition. This corrects a formal-interface error,
not a counterexample to the manuscript's restricted sieve application.

The end-to-end declaration is
`PrimeAbundance.prime_abundance : PrimeAbundance.PrimeAbundanceClaim`.
It proves the quantitative prime exceptional-set bound at the rate in (2)
and proves that the exceptional primes have relative density zero. Its
solution multiplicity is an injection into strictly ordered Type-II
solutions. The proof contains concrete derivations of its lower mean,
upper overlap, finite transfer, global asymptotic comparison and elementary
prime-count denominator.

The verified implementation uses Lean 4.27.0 and mathlib commit
`a3a10db0e9d66acbebf76c5e6a135066525ac900`. The fresh-source verifier
compiled all 24 local source files in the final import closure into a new
temporary object directory; the ordinary project build completed 7,909
jobs. Axiom audits of the final theorem, analytic bound, quantitative bound,
relative-density theorem and finite transfer report only `propext`,
`Classical.choice` and `Quot.sound`; no `sorryAx` or project-specific axiom
is used. The source and verifier are under
`formalization/abundance-2026-09-05/coordination/external-6pro-analytic/`
`prime-abundance-analytic-local/`. Running `bash verify.sh` there reproduces
the guarded fresh-source check against the pinned mathlib cache. This is not
a source rebuild of all mathlib dependencies.

**Remaining formal boundary.** The certificate proves the prime lower-bound
and relative-density portion, but it does not formalize the all-integer bound
in (1), Proposition 3 exactly as stated for the full Section 2 family, or
the Elsholtz--Tao upper-bound argument used in Corollary 2. Thus the matching
prime exponent three follows by combining the new certified lower side with
the cited published upper side, rather than from one end-to-end Lean theorem.
The specific derivation in Sections 5--9 and the stronger $O(\mu)$ estimate
of Section 10 remain outside the completed certificate. The earlier root
helpers likewise do not certify estimates (27)--(29) for the full family.

### 11.2. Remaining mathematical review

This draft claims a complete Lean proof only for the prime exceptional-set
lower bound and relative-density statement just specified. It does not claim
a Lean proof of every manuscript assertion, a verified asymptotic leading
constant, an effective numerical onset, a new zero-solution exception record,
or a solution for every prime. It also makes no claim to literature-wide
priority.

The highest-priority external checks are the uniform import (12)–(13),
the lower-sieve application (15), the full-prime-power and endpoint
accounting in Section 7, and the completeness of the positive cover in
Section 9. Section 10 additionally requires scrutiny of the rough divisor
moment (37), the averaged coefficient correction and the exceptional
equal-slope range; the review status of the shorter route does not certify
these additional steps. A submission version should include a frozen source archive,
exact build instructions for whatever formal components are offered,
and an explicit list of any analytic premises left unformalized.

## References

**[ET]** C. Elsholtz and T. Tao, *Counting the number of solutions to the
Erdős–Straus equation on unit fractions*, Journal of the Australian
Mathematical Society **94** (2013), 50–105.
[Journal article](https://doi.org/10.1017/S1446788712000468).
The relevant locations are Theorem 1.1 and equation (1.4), pp. 53–54,
and Theorem 1.8, p. 56.

**[H]** K. Henriot, *Nair–Tenenbaum bounds uniform with respect to the
discriminant*, Mathematical Proceedings of the Cambridge Philosophical
Society **152** (2012), 405–424.
[Article](https://doi.org/10.1017/S0305004111000752).
Read together with [HE].

**[HE]** K. Henriot, *Nair–Tenenbaum uniform with respect to the
discriminant—ERRATUM*, Mathematical Proceedings of the Cambridge
Philosophical Society **157** (2014), 375–377.
[Erratum](https://doi.org/10.1017/S0305004114000280).
The corrected New Theorem 5 on p. 377 is the imported upper theorem.

**[HR]** H. Halberstam and H.-E. Richert, *Sieve Methods*, London
Mathematical Society Monographs **4**, Academic Press, 1974.
General source for the fundamental lemma; the exact edition-specific
theorem/page for Section 5.2 remains a submission checklist item.

**[EP]** C. Elsholtz and S. Planitzer, *The number of solutions of the
Erdős–Straus Equation and sums of $k$ unit fractions*.
[arXiv:1805.02945](https://arxiv.org/abs/1805.02945).
Cited for related solution-count questions, not as a premise of our lower bound.

**[D]** B. Dahan, *Sieve dimension and search depth for the Erdős–Straus
conjecture, $n\equiv1\pmod{24}$*, 25 August 2026.
[arXiv:2608.24035v1](https://arxiv.org/html/2608.24035v1), Sections 4.1–4.4.
Cited as related work requiring a complete priority comparison, not as a
premise of Proposition 3.
