# Exact finite-state criterion for a fixed opposite-divisor gate

## Status

Established as an elementary equivalence. A reproducible implementation is in
`scripts/fixed_gate_automaton.py`. This is a structural tool, not a proof of the
Erdős–Straus conjecture.

## Statement

Let `d > 1` be odd and let `x > 0` satisfy `gcd(x,d)=1`. Write

```text
x = ∏ᵢ qᵢ^eᵢ
```

with distinct primes `qᵢ`. For each `i`, choose one of the following:

1. assign no power of `qᵢ`;
2. assign `qᵢ^αᵢ` to `a`, where `1 ≤ αᵢ ≤ eᵢ`;
3. assign `qᵢ^βᵢ` to `b`, where `1 ≤ βᵢ ≤ eᵢ`.

No prime is assigned to both sides. Then the following are equivalent:

1. there exist coprime divisors `a,b | x` such that `d | a+b`;
2. one of these disjoint assignments produces residues
   `(A,B) ∈ (Z/dZ)^× × (Z/dZ)^×` with `A+B=0`.

For odd `d`, such a pair automatically has `a ≠ b`: equality would imply
`d | 2a`, contradicting `gcd(a,d)=1`. Hence the pair can be ordered to satisfy
`a < b`, giving `HasOppositeCoprimeDivisors x d`.

## Proof

Forward direction: factor the coprime divisors `a` and `b`. Since both divide
`x` and `gcd(a,b)=1`, each prime factor of `x` occurs in at most one of them,
with exponent at most its exponent in `x`. Their residues therefore arise from
a disjoint assignment.

Reverse direction: multiply the prime powers assigned to each side. The
resulting positive integers divide `x`, are coprime because their prime
supports are disjoint, and have residue sum zero modulo `d`. Oddness and
`gcd(x,d)=1` rule out equality, so the two values can be ordered.

## Finite-state formulation

The state space contains at most `φ(d)^2` residue pairs. Start with `(1,1)`.
For each factor `q^e`, retain every current state and add states obtained by
multiplying exactly one coordinate by `q^j mod d`, for `1 ≤ j ≤ e`.

Thus each fixed `(x,d)` gate is decidable by a terminating exact computation.
The computation is not by itself a universal proof because the number and
residue pattern of prime factors of `x=(p+d)/4` are not bounded uniformly.

## Falsified shortcut at `d=11`

A search of residue signatures shows that “five distinct prime factors force
the `d=11` gate” is false. For example, five distinct primes all congruent to
`1 mod 11` produce only residue `1` on each side, so no pair can sum to zero
modulo `11`.

This identifies the relevant variable: not the number of distinct prime
factors alone, but the finite-state closure of their prime-power residues.

## Lean-friendly decomposition

Suggested reusable definitions and lemmas:

```lean
structure DisjointPrimePowerAssignment ...

def ReachableResiduePair (x d A B : ℕ) : Prop := ...

 theorem reachableResiduePair_iff_coprime_divisors ...

 theorem hasOppositeCoprimeDivisors_iff_reachable_opposites ...
```

Arithmetic side conditions should be kept explicit:

- `1 < d`;
- `Odd d`;
- `0 < x`;
- `Nat.Coprime x d`;
- bounds on selected exponents;
- disjoint support.

The theorem supports the divisor/finite-obstruction route. It does not enter
the main proof map until a universal argument constrains the reachable state
for every residual prime.
