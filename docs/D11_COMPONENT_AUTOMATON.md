# Corrected exact `d=11` prime-power exponent automaton

## Status and correction

The former version of this note and `scripts/d11_component_automaton.py`
claimed that an exact gate search could assign each entire prime-power
component `q^e` to the left divisor, the right divisor, or neither.

That claim is **false**. For arbitrary divisors `a,b | x` with
`gcd(a,b)=1`, a prime power

```text
q^e || x
```

may contribute any exponent `q^j`, `1≤j≤e`, to at most one side. In
addition, either divisor is allowed to equal `1`; an empty prime support is
valid.

The exact fixed-gate automaton was already implemented correctly in
`scripts/fixed_gate_automaton.py`. The specialized `d=11` script now delegates
to that semantics and retains the former model only as a regression oracle.

## Exact criterion

Let

```text
x = product q_i^e_i,
gcd(x,11)=1.
```

Start from the residue state `(1,1)`. For each distinct prime `q_i`, and for
each current state `(A,B)`, make the following choices:

1. assign no power of `q_i`;
2. assign `q_i^j` to the left side for one `1≤j≤e_i`;
3. assign `q_i^j` to the right side for one `1≤j≤e_i`.

No prime may be assigned to both sides. A state succeeds exactly when

```text
A+B = 0 mod11.
```

The reconstructed integers are automatically coprime divisors of `x`.
Because `11` is odd and coprime to `x`, a successful pair cannot have equal
values, so it can be ordered as `a<b`.

This is the same exact criterion recorded in
`docs/fixed-gate-automaton.md`.

## Explicit counterexamples to the former model

### Divisor `1` and a partial exponent

Take

```text
x = 1849 = 43^2.
```

Since `43≡10 mod11`, the pair

```text
(a,b)=(1,43)
```

satisfies `11 | a+b`. The former model sees only the entire component
`43^2≡1 mod11` and requires both sides to be nonempty, so it incorrectly
returns failure.

### A genuine consecutive-gate example

Take the residual prime

```text
p = 4201.
```

The first two exact gates fail, while

```text
x_2 = (p+11)/4 = 1053 = 3^4*13.
```

At `d=11`, the pair

```text
(a,b)=(9,13)
```

is valid because `9+13=22`. It uses `3^2` from the available `3^4`
factor. The former full-component model sees only `3^4` and `13` and
incorrectly declares the gate closed.

## Finite audit through `10^7`

Reproduction:

```bash
python scripts/d11_component_automaton.py \
  --audit-limit 10000000 \
  --json data/d11-legacy-audit-10m.json
```

Among the residual primes `p≤10^7`:

```text
d=3 success:                            47,137
d=7 success after d=3 failure:          28,606
reached d=11:                            7,144
exact d=11 success:                      4,419
exact d=11 failure:                      2,725
legacy full-component success:           3,295
legacy full-component failure:           3,849
legacy false negatives:                  1,124
```

There were no legacy successes rejected by the exact automaton, as expected:
the legacy assignments form only a subset of the valid exact assignments.

The earlier check restricted to rows whose committed first witness had
`k≥3` did not reveal the defect. Those rows are already known to fail the
exact `d=11` gate, so any weaker subsearch must also fail. It was not an
independent validation of exact gate semantics.

## Consequences for prior conclusions

The following former claims must not be used as exact mathematics:

- full `q^e` components are the only atomic choices;
- both divisor supports must be nonempty;
- minimal success patterns of full component residues classify the gate;
- the full-component state graph is an exact `d=11` obstruction.

Support-only subgroup arguments remain valid when proved independently.
In particular, if every prime divisor of `x` lies in the quadratic-residue
subgroup `{1,3,4,5,9}` modulo 11, then every divisor lies there and no
opposite pair exists. What fails is the assertion that arbitrary inputs can
be classified by entire component residues alone.

## Current research direction

The corrected automaton reinforces the complete-sequence strategy:

1. use exact prime-power exponent states at every fixed gate;
2. retain the proved `d=3` and `d=7` prime-factor characterizations;
3. combine exact later-gate failure with the new Type-I condition on `p+1`;
4. seek a finite quotient or local-global invariant that couples several
   consecutive offsets.

Finite automaton output remains a falsification and discovery tool. It does
not prove universal coverage.
