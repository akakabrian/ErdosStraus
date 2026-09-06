# Independent review packet: finite Lean milestone for prime abundance

Brian Akaka, 5 September 2026. This is a review request, not a certification.

## Requested review

Please adversarially assess the exact finite theorem below and the proposed
description of its verification scope. Look for a mismatch between the
formal statement and the claimed mathematics, a hidden/vacuous premise,
lost prime powers, ordered/unordered counting errors, incorrect endpoint
costs, or loss of distinctness/strict ordering. Do not infer correctness
from earlier model agreement. Do not claim to have compiled source unless
you actually have the files and have run Lean.

Return: (1) any fatal or material findings, with an exact counterexample or
missing implication; (2) safe preprint wording; (3) the single next useful
formal milestone. Full analytic estimates and literature-wide priority are
outside this bounded review. A clean finite review does not certify them.

## Exact objects

For a natural cutoff Y define w=floor((log Y)^100). A packet is a pair
(M,s) with 1<=M<=3Y, 3|M, 0<s<M and s|M^2, retained when
minFac(Q)>w, Q=4M-1. All prime and composite rough Q are included. No
authentic packet has Q=1. A packet fires at n if Q divides n+4s.

T_Y(n) is the number of firing packets; mu_Y=sum_packets 1/Q.
Delta_Y is the sum over packets a,b with Q_a<Q_b, g=gcd(Q_a,Q_b)>1,
s_a=s_b mod g, of g/(Q_a Q_b). Thus Delta is an UNORDERED distinct-row
sum, retaining every prime power in the gcd. Same-row distinct labels do
not contribute to Delta.

Let StrictTriple(n) be the type of positive natural triples x<y<z with
the exact rational identity 4/n=1/x+1/y+1/z. A triple is Type II when
n|y, n|z and gcd(n,x)=1. HasAtLeastTypeIISolutions(n,r) means an
injection from Fin(r) into StrictTriple(n) with all images Type II.
This avoids assuming the total solution set is finite and still expresses
at least r distinct strict solutions, not a count of parametrizations.

## Finite statement being checked

For all natural Y,A,H,r, if mu_Y>0, 12Y<A and r<=mu_Y/2, then

    #{0<=k<H : A+k is prime and NOT HasAtLeastTypeIISolutions(A+k,r)}
      <= 4 [ H (mu_Y+2 Delta_Y)/mu_Y^2 + (1+12Y)^2 ].

The constants and endpoint cost are literal, not asymptotic. No lower
bound on mu or upper bound on Delta is a premise of this finite theorem.
The lower-tail bound for T_Y itself does not require 12Y<A. H=0 is
allowed; mu=0 is explicitly excluded. A compiled example establishes
mu_1>0, so this positivity condition is not inherently contradictory.
The bound need not be numerically informative for small Y.

## Mathematical proof of the finite statement

1. Authentic packets have Q odd, gcd(Q,s)=gcd(Q,M)=1 and 0<s<M<Q.
   For n>Q a firing gives integers

       x=(nM+s)/Q, y=nM, z=nMx/s.

   The identity QMx=nM^2+Ms and s|M^2 prove s|Mx. Thus z is an
   integer divisible by n. The inequalities x>M>s and x<n<=y prove
   x<y<z. Expanding Q=4M-1 gives the Egyptian-fraction identity.
   At prime n=p, p cannot divide x: otherwise Qx=pM+s forces p|s,
   contrary to 0<s<M<Q<p. Distinct packets give distinct triples:
   recover M=y/n, Q=4M-1 and s=Qx-nM.

2. For single packets the exact residue probability is 1/Q. For pairs it
   is zero if incompatible, and 1/lcm(Q,Q')=g/(QQ') if compatible.
   Compatibility of the actual phases -4s mod Q is equivalent to
   s=s' mod g because all row moduli are odd. Distinct labels on the same
   row are incompatible since 0<s,s'<Q.

3. Expand the finite second moment using these exact pair probabilities.
   Coprime pairs have zero covariance. Drop negative covariance from
   incompatible pairs. The diagonal is at most mu. Each compatible pair
   of different noncoprime rows appears twice, so

       v <= mu + 2 Delta.

4. In any H consecutive integers a single residue count differs from H/q
   by at most 1. Compatible packet pairs also form one residue class,
   now modulo the full lcm. Incompatible pairs never fire together.
   Expand (1-T/mu)^2 and use the lower error bound for the negative linear
   term and upper error bound for the positive quadratic term. Writing m
   for the number of packets yields

       sum_{k<H} (1-T_Y(A+k)/mu)^2
          <= H v/mu^2 + (1+m/mu)^2.

   Every Q<12Y gives mu>=m/(12Y), hence m/mu<=12Y when mu>0.
   Therefore the right side is at most
   H(mu+2Delta)/mu^2+(1+12Y)^2.

5. T<=mu/2 forces (1-T/mu)^2>=1/4; summing proves the finite lower-tail
   bound with factor 4. At A+k>12Y every firing packet decodes injectively
   to a strict solution, Type II when A+k is prime. If T>mu/2>=r, restricting
   the injection to Fin(r) gives r distinct Type-II solutions. Therefore
   primes without r such solutions are contained in the lower-tail set.

## Supporting analytic lemmas, not the analytic theorem

The two lanes also formalize elementary support:

- Positive full-divisor totient expansion, with sum_{d|g,d>1} phi(d)=g-1.
- Primitive-ray congruence and determinant divisibility/lower bounds.
- Uniqueness of r*l^2 for positive squarefree r and positive l, including
  cancellation of a fixed positive coefficient on a fixed cofactor/ray.
- At most two UNIT square roots of a UNIT modulo an odd prime power p^e.
  This is not yet a CRT theorem over a general composite modulus.
- Arithmetic-progression reciprocal-tail bounds.
- Exact equality of the two concrete packet, mean and Delta definitions,
  and equivalence of their named mean/overlap premises.

An old proposed formal input quantified an arbitrary roughness cutoff w
and was false: a=1, T>=max(T0,2), w=24T gives no surviving 12m-1 for
T<m<=2T but a positive asserted lower bound cT/log w. Lean verifies its
negation. That old input is not assumed by the finite theorem.

Its replacement fixes w=cutoff(Y) and uses the manuscript's ranges
a^3<=Y^2, Y<=a*T^2, 2aT<=Y, a>=1, gcd(a,6)=1, T>=2, cutoff(Y)>=2.
The lower bound is STILL AN UNPROVED PROPOSITION, not an axiom or a result.
The elementary range conditions imply Y<=T^6 for Y>0. For an arbitrary
cutoff function the proposition can of course fail; only the intended
polylogarithmic cutoff is proposed for the analytic application.

## What the proposed preprint still needs

The preprint proposes mu asymp (log Y)^3/log w and
Delta=O((log Y)^3 log(2log Y)). These are NOT supplied by the finite Lean
theorem, by declaring interfaces, or by the elementary helper modules.
The remaining formal work includes the complete first/tail positive cover,
product-shell ray cardinality and summation, CRT multiplication of local
root counts, uniform lower-sieve and corrected Henriot applications,
Mertens/divisor estimates, and assembling the asymptotic interval and
prime-density conclusions. A logarithmic algebraic squeeze is not itself
a proved density-one statement.

If the analytic estimates hold, choosing Y on the order of N^(1/3) gives
the proposed bad-count O(N(loglog N)^3/(log N)^3) and threshold
c(log p)^3/loglog p. The stronger separate Delta=O(mu) proposal is not
formalized here. Neither estimate settles all primes or proves ESC.

Safe proposed wording: "An accompanying partial Lean formalization checks
the finite witness-to-abundance implication, including strict Type-II
decoding and an explicit finite exceptional-set bound in terms of the
concrete mean and overlap. The analytic estimates and final asymptotic
theorem remain unformalized."

## Source access, if available

Canonical checkout:
`/Users/brian/Documents/Codex/2026-07-28/continue-the-erd-s-straus-conjecture/work/ErdosStraus`.
Do not claim local access if reviewing this packet in a browser-only chat.

Within the checkout, the source is in
`formalization/abundance-2026-09-05/`:

- `biz1/ErdosStrausAbundance/{Packets,Decoder,CRT,Covariance,Interval,SquareTransfer,Conditional,Examples}.lean`;
- `biz2/ErdosStrausAbundance/{SquarefreeScale,QuadraticRoots,AnalyticInterfaces,InterfaceDefect}.lean`;
- `coordination/{Integration,CombinedAxioms}.lean`;
- `coordination/rebuild-combined.sh` and `coordination/combined-source-build.log`.

The combined script recompiles local sources into a new temporary directory;
it uses the installed Lean 4.27.0/mathlib v4.27.0 cache. It is not a
cache-free rebuild of all mathlib. Check its final output and exit status
before accepting any compilation claim. The source preprint is
`docs/prime-abundance-preprint-draft.md`; Sections 5-10 contain the
unformalized proposed arithmetic argument.
