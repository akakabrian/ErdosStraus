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
