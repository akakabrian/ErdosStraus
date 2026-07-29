# Decisions

This file records durable research and engineering decisions. Append new decisions; do not silently rewrite history.

## 2026-07-22 — Preserve the exact strict target

The project targets the Formal Conjectures statement with natural denominators satisfying:

```text
1 ≤ x < y < z.
```

A proof with repeated or unordered denominators is not accepted as a proof of Erdős Problem 242 in this repository.

## 2026-07-22 — Use polynomial certificates internally

Formal helper lemmas use:

```text
4xyz = n(xy + xz + yz)
```

with explicit positivity/order hypotheses, then bridge to the rational equation. This avoids hidden division-by-zero obligations while preserving the exact target.

## 2026-07-22 — Separate research and integration repositories

`akakabrian/ErdosStraus` is the canonical research record. The Formal Conjectures fork is an integration target, not the sole archive of derivations, computation, failures, or decisions.

## 2026-07-22 — Prime `1 mod 24` reduction is Phase 1

Elementary strict families plus divisor scaling should establish:

> If any counterexample exists, then a prime counterexample congruent to `1 mod 24` exists.

This is a helper theorem only. It does not solve the conjecture.

## 2026-07-22 — Primary structural route is Type-II divisor structure

The main research route is the factor-pair condition

```text
p + d = 4abc,
a + b = ds,
```

and its divisor-residue normalizations. Affine Egyptian-fraction identities remain useful for discovery but are not the default proof strategy.

## 2026-07-22 — Finite evidence must be reproducible and labeled

Numerical coverage is recorded only with exact arithmetic, source code, parameters, result summaries, and checksums. No finite bound is promoted to a universal claim.

## 2026-07-22 — CI and kernel evidence gate completion

A formal phase is complete only after targeted build, full build, warnings-as-errors where applicable, axiom audit, and forbidden-token audit. Passing a subset of files is not sufficient.

## 2026-07-28 — Complete the `p`-adic factorization split

The fixed Type-II architecture covers only the case in which one factor of

```text
(dy-px)(dz-px)=p²x²
```

contains exactly one factor of `p`. Research on the complete offset sequence must also track exponent-zero and exponent-two cases. The exponent-zero case is represented by the Type-I factor-pair equations

```text
p+d=4abc,
a+p*b=d*s.
```

Type-II remains core infrastructure, but it is no longer treated as the only structural language for the two remaining unit fractions.

## 2026-07-28 — Use unbounded sequence gates when they yield global restrictions

The unit Type-I gate `d_k | p+1` can occur at offsets much larger than every tested fixed Type-II window. It is retained because failure across the complete sequence forces every odd prime divisor of `p+1` to be `1 mod4`, a genuine global condition on a hypothetical counterexample.

A family is valuable for its deductive restriction even when it does not cover every prime and its successful offset is unbounded.

## 2026-07-28 — Exact divisor automata allow `1` and partial exponents

For `x=∏q_i^{e_i}`, an exact coprime-divisor automaton must allow, for each prime, no assignment or one exponent `q_i^j` with `1≤j≤e_i` on exactly one side. Either divisor may equal `1`.

Automata that assign only the entire `q_i^{e_i}` component or require both supports to be nonempty are labeled legacy under-approximations and may be used only for regression comparison, never as exact gate classifiers.

## 2026-07-28 — Audit scripts must fail closed on missing tools

A forbidden-token or axiom scan cannot report success after its search executable is missing. Targeted workflows should use runner-standard tools or install explicit dependencies, and each diagnostic step must propagate tool failures after preserving logs.

## 2026-07-28 — Promote the fixed-`a` Type-I divisor hierarchy

Setting `b=1` in the Type-I identity gives the global family

```text
p+a=d*s,
p+d=4*a*c,
1≤a<p,
0<d<p.
```

Equivalently, one factors the consecutive additive shifts `p+a` and seeks a proper divisor `d≡-p mod 4a`. This is now the primary new global mechanism because failure gives an infinite hierarchy of exact splitting obstructions on `p+1,p+2,…`, rather than merely excluding one fixed offset.

Type-II, fixed-gate, Mordell, modulo-9240, and automaton results remain infrastructure and may be combined with this hierarchy. They are not discarded.

## 2026-07-28 — Separate dynamic divisor mechanisms from affine residue covers

The strength of the fixed-`a` family comes from the actual factorization of `p+a`. Restricting to fixed pairs `(a,d)` whose moduli divide a finite master modulus produces only an affine congruence sieve.

At modulus `9240`, that sieve leaves every one of the existing 34 Type-II residual classes. Therefore no fixed finite residue cover is inferred from the strong finite fixed-`a` data. Future work should target a local-global incompatibility, a finite-obstruction theorem, or descent in the dynamic divisor data.
