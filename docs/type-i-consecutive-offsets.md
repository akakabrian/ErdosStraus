# Type-I factor pairs and the complete consecutive-offset sequence

## Status

The algebraic Type-I identities in this note are universal arithmetic facts.
The finite counts are exact experiments and are not a proof of the
Erdős–Straus conjecture.

The strict target remains:

```text
For every n > 2, find natural numbers 1 ≤ x < y < z with
4/n = 1/x + 1/y + 1/z.
```

## 1. Complete factorization after fixing the first denominator

For a residual prime `p ≡ 1 mod 24`, write

```text
m   = (p+3)/4,
x_k = m+k,
d_k = 4k+3.
```

Then

```text
p+d_k = 4*x_k
```

for every `k`. After choosing `x=x_k`, the remaining two fractions must
satisfy

```text
d/(p*x) = 1/y + 1/z.
```

This is equivalent to the exact factorization

```text
(d*y-p*x)(d*z-p*x) = p²*x².
```

Put

```text
u = d*y-p*x,
v = d*z-p*x.
```

For `0<d<p`, strict order is represented by positive factors

```text
u*v = p²*x²,
u < p*x < v,
u ≡ -p*x (mod d).
```

Because `p` is prime and `gcd(p,x)=1`, the exponent of `p` in `u` is
`0`, `1`, or `2`. The existing divisor-square Type-II search is the
middle case. The exponent-zero case gives a complementary Type-I
parameterization.

## 2. Strict Type-I factor-pair lemma

### Statement

Let `p,a,b,c,s,d` be positive natural numbers satisfying

```text
p+d   = 4*a*b*c,
a+p*b = d*s.
```

Then the denominators

```text
X = a*b*c,
Y = a*c*s,
Z = p*b*c*s
```

satisfy the Erdős–Straus polynomial identity.

If additionally

```text
b < s,
a < p*b,
```

then

```text
1 ≤ X < Y < Z.
```

The first strict inequality is automatic from `0<d<p`: multiplying
`d<p` by `b`, then using `p*b < a+p*b=d*s`, gives `d*b<d*s`, hence
`b<s`.

### Proof of the identity

The difference between the two sides factors as

```text
4*X*Y*Z - p*(X*Y+X*Z+Y*Z)
  = -a*b*c²*p*s * (-4*a*b*c*s + a+p*b+p*s).
```

The parenthesized term vanishes because

```text
4*a*b*c*s = (p+d)*s
          = p*s + d*s
          = p*s + a+p*b.
```

No approximation or finite computation enters this proof.

### Divisor-square normalization

In the exponent-zero factorization case, let `q | x²`,
`q < p*x`, and

```text
d | q+p*x.
```

Writing

```text
g = gcd(x,q),
a = q/g,
b = x/g,
c = g/a
```

gives

```text
q = a²*c,
x = a*b*c.
```

For a prime offset, `gcd(d,x)=1`; therefore `gcd(d,a*c)=1`, and
cancellation in

```text
d | a*c*(a+p*b)
```

gives `d | a+p*b`. The bound `q<p*x` becomes `a<p*b`. This is the
Type-I analogue of the committed Type-II divisor-square normalization.

## 3. A global gate from divisors of `p+1`

Set

```text
a=b=1,
c=x.
```

The Type-I equations reduce to

```text
p+d = 4*x,
p+1 = d*s.
```

Therefore:

> If `0<d<p`, `d≡3 mod 4`, and `d | p+1`, then the offset
> `k=(d-3)/4` gives the strict decomposition
>
> ```text
> 4/p = 1/x_k + 1/(x_k*s) + 1/(p*x_k*s),
> s=(p+1)/d.
> ```

Strictness is immediate: `d<p` forces `s>1`, so

```text
x_k < x_k*s < p*x_k*s.
```

This is an unbounded-offset theorem across the complete sequence, not a
fixed finite gate.

### Consequence for a hypothetical counterexample

Let `p≡1 mod24` be prime. If an odd prime `r | p+1` satisfies
`r≡3 mod4`, then `r=4k+3`. Since `2r | p+1`, one has `r<p`, and the
unit Type-I gate applies.

Hence a hypothetical prime counterexample must satisfy:

> Every odd prime divisor of `p+1` is congruent to `1 mod4`.

This is a new global splitting restriction. It can be combined with the
existing consequences of early Type-II gate failure:

```text
all prime factors of (p+3)/4 are 1 mod3,
all prime factors of (p+7)/4 are quadratic residues mod7.
```

The current proof obligation is to show that these and later restrictions
cannot persist, or to extract a descent/local-global contradiction from
them.

## 4. Exact falsification and profiling through `10^8`

Reproduction:

```bash
python scripts/consecutive_gate_profiler.py \
  --limit 100000000 \
  --max-k 40 \
  --json data/consecutive-offset-summary-100m.json
```

Population:

```text
719,781 primes p≤10^8 with p≡1 mod24.
```

Results:

```text
Type-II bounded search unresolved through k=40:       0
Complete two-fraction search unresolved through k=40: 0
Primes whose first witness moved earlier:             1,590
Largest observed improvement:                         15 offsets
Unit Type-I p+1 gate covered:                         398,283
Unit Type-I p+1 gate not covered:                     321,498
```

The largest improvement occurred at

```text
p = 1,430,641
Type-II first witness k = 17
complete factorization first witness k = 2
d = 11, q = 17
a = 1, b = 21,039, c = 17, s = 2,736,296,000.
```

The unit gate needed offsets far beyond the old fixed search window. The
largest observed unit-gate offset was

```text
p = 99,207,697
d = 7,043
k = 1,760.
```

This is useful evidence against organizing the proof around a universal
small bound on `k`. It is not evidence that every prime has a unit gate.

## 5. Deductive edge

The Type-I extension contributes three things that the fixed Type-II
architecture did not provide:

1. It completes the `p`-adic split of the exact two-fraction
   factorization after choosing `x_k`.
2. It supplies a universal unbounded-offset family controlled by the
   factorization of `p+1`.
3. It turns simultaneous failure into a new global condition on an
   integer adjacent to the complete offset sequence.

The universal theorem is still open. The highest-value next question is
whether

```text
all odd prime factors of p+1 are 1 mod4,
all prime factors of x_0 are 1 mod3,
all prime factors of x_1 are quadratic residues mod7,
...
```

can hold indefinitely for a prime `p`, or whether the combined splitting
conditions force a gate, descent, or contradiction.
