# Fixed-`a` Type-I gates: a global divisor parameterization

## Status

The certificate theorem in Sections 1–2 is rigorous and is formalized in
`TypeIFactorPair.lean`. The numerical coverage in Section 5 is finite exact
computation and is not a proof of the universal Erdős–Straus theorem.

The exact target remains

```text
For every n>2, find natural numbers 1≤x<y<z with
4/n=1/x+1/y+1/z.
```

## 1. The fixed-`a`, unit-`b` certificate

The Type-I factor-pair equations are

```text
p+d=4abc,
a+p*b=d*s.
```

Set `b=1`. If positive integers `a,c,d,s` satisfy

```text
p+a=d*s,
p+d=4*a*c,
1≤a<p,
0<d<p,
```

then

```text
X=a*c,
Y=a*c*s,
Z=p*c*s
```

satisfy

```text
1≤X<Y<Z,
4XYZ=p(XY+XZ+YZ).
```

The identity is the Type-I polynomial identity. Strictness follows from the
proved offset lemma: `d<p` implies `1<s`, hence `X<Y`, while `a<p` gives
`Y<Z`.

This theorem is formalized as

```text
ErdosStraus.fixedA_typeI_gate_hasDistinctDecomposition
```

on the formal branch `agent/erdos-242-consecutive-offsets`.

## 2. Divisor formulation

For fixed `p` and `a`, factor `p+a`. Every proper divisor `d<p` satisfying

```text
p+d≡0 mod 4a
```

produces the certificate by setting

```text
s=(p+a)/d,
c=(p+d)/(4a).
```

Thus a hypothetical residual-prime counterexample must satisfy the infinite
local-global obstruction

> For every `1≤a<p`, no proper divisor `d` of `p+a` lies in the residue class
> `-p mod 4a`.

The unit `p+1` gate is exactly the case `a=1`. The parameter `a` reorganizes
the complete offset sequence globally: successful offsets `d` may be very
large even when the first successful `a` is small.

## 3. Equivalent three-factor form

Assume `p` is prime and the fixed-`a` equations hold with `a,d<p`. Then
`gcd(a,d)=1`: a common divisor divides

```text
p=d*s-a,
```

and cannot equal the prime `p` because it is at most `a<p`.

Subtracting the two defining equations gives

```text
d*(s+1)=a*(4c+1).
```

Coprimality therefore gives a positive integer `t` with

```text
s+1=a*t,
4c+1=d*t.
```

Equivalently,

```text
p=a*d*t-a-d,
p*t+1=4*c*s.
```

For a residual prime `p≡1 mod4`, the offset has `d≡3 mod4`; because
`d*t=4c+1`, one also has `t≡3 mod4`.

This exposes a possible descent/local-global variable that is absent from the
fixed-`k` architecture. No monotone descent in `a,d,t` has yet been proved.

## 4. First splitting consequences

### `a=1`

Failure means `p+1` has no divisor `3 mod4`. In particular every odd prime
factor of `p+1` is `1 mod4`. This obstruction is formalized in
`ConsecutiveOffsets.lean`.

### `a=2`

For `p≡1 mod8`, a successful divisor must satisfy

```text
d|p+2,
d≡7 mod8.
```

Consequently, if the `a=2` gate fails, every prime factor of `p+2` is
congruent to `1` or `3 mod8`:

- a prime factor `7 mod8` is itself a successful divisor;
- if a prime factor is `5 mod8`, its complementary divisor is `7 mod8`
  because `p+2≡3 mod8`.

This illustrates the new local-global program: simultaneous failure for small
`a` forces compatible splitting restrictions on the additive shifts
`p+1,p+2,p+3,...`.

## 5. Exact finite profiling

### All residual primes through `10^8`

Command:

```bash
python scripts/fixed_a_typei_profiler.py \
  --limit 100000000 \
  --max-a 1000 \
  --json data/fixed-a-typei-summary-100m.json
```

Results:

```text
primes p≤10^8, p≡1 mod24: 719,781
resolved with a≤1000:      719,781
unresolved:                      0
largest first a:               890
```

Cumulative first-`a` coverage:

```text
a≤1:       398,283
a≤2:       610,630
a≤3:       669,162
a≤5:       708,311
a≤10:      717,853
a≤20:      719,570
a≤50:      719,760
a≤100:     719,776
a≤200:     719,779
a≤500:     719,780
a≤1000:    719,781
```

The isolated record is

```text
p=5,101,441
a=890
d=39
c=1,433
s=130,829
t=147
X=1,275,370
Y=166,855,381,730
Z=956,407,736,436,037.
```

### Mordell-residual primes from `10^8` to `10^9`

Nine disjoint segmented runs checked the six rigorously relevant Mordell
classes modulo `840`:

```text
primes checked:             1,408,113
resolved with a≤2000:       1,408,113
unresolved:                         0
largest first a in range:         146
```

The largest global first-`a` value observed through these ranges remains the
`a=890` record below `10^8`. This does not establish any universal bound.

Reproducible summaries:

```text
data/fixed-a-typei-summary-100m.json
data/fixed-a-typei-mordell-1b.json
```

Integrity hashes:

```text
scripts/fixed_a_typei_profiler.py
 a6b0c7b18e066c2be8b06fdbf0df97d8f9d27158f36108223c74d1457030371c

data/fixed-a-typei-summary-100m.json
 df44194f53e24cbf90898951f16a3411576445a257c6d80815b74a6d712110ee

data/fixed-a-typei-mordell-1b.json
 9be0c229b0ad9ceff77bf296747530026e26033e0189887ecfe6c401b3e1551c
```

## 6. Deductive edge and blocker

This parameterization is materially stronger than adding more fixed Type-II
offsets:

1. it is a proved strict certificate family;
2. it ranges over the complete offset sequence through divisors of `p+a`;
3. failure gives a hierarchy of exact splitting obstructions on consecutive
   additive shifts;
4. it covers every tested residual prime through `10^8` and every tested
   Mordell-residual prime through `10^9` with a small first parameter.

The exact missing theorem is still infinite:

> Prove that every residual prime has some `1≤a<p` and proper divisor
> `d|p+a` with `p+d≡0 mod4a`, or prove that failure of this condition forces
> another already-proved gate or a strict descent.

Neither the observed `a≤890` ceiling nor any other finite bound is currently
proved.
