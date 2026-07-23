# Project State

Last updated: 2026-07-22 (Pacific/Honolulu)

## Overall

- The main Erdős–Straus theorem remains open.
- The exact target requires `1 ≤ x < y < z`; no weakening is permitted.
- Phase 1 helper modules are implemented in the Formal Conjectures fork.
- The known `MinimalCounterexample.lean` lower-bound failure has been patched and is under CI verification.

## Lean integration

Repository: `akakabrian/formal-conjectures`

Branch: `erdos-242-phase1`

Current head: `e63496b0bd64b9383df186e09a9999940d623f66`

Draft PR: https://github.com/akakabrian/formal-conjectures/pull/2

Patch at current head:

```lean
have hpTwo : 2 ≤ p := hpCounter.1.le
rw [Nat.prime_iff_not_exists_mul_eq]
refine ⟨hpTwo, ?_⟩
```

This replaces an opaque `omega` attempt to establish `2 ≤ p`.

## CI runs for current head

- Targeted Erdős 242 check: run `29975162859`
- Full Lean build/docs: run `29975162879`
- Copyright check: run `29975162925`

At the time of this update, copyright had passed and both Lean runs were still executing. Final conclusions must be recorded in this file and issue #1.

## Phase 1 theorem inventory

Implemented helper modules:

- `Basic.lean`
- `ElementaryFamilies.lean`
- `Scaling.lean`
- `Reduction.lean`
- `MinimalCounterexample.lean`
- `TypeIIFactorPair.lean`
- `DivisorResidues.lean`
- `SmallGates.lean`

Intended kernel-checked results include:

- strict polynomial certificate and rational bridge;
- even, `2 mod 3`, `3 mod 4`, and `5 mod 8` strict families;
- divisor scaling;
- reduction of a counterexample to `1 mod 24`;
- existence of a prime `1 mod 24` counterexample if any counterexample exists;
- Type-II factor-pair identity and strict certificate;
- opposite-coprime-divisor conversion;
- the first `d = 3` divisor gate.

## Computational evidence

Reported finite profiling through primes `p ≤ 100,000,000`, `p ≡ 1 mod 24` found Type-II witnesses for all 719,781 tested primes. This result has not yet been reproduced from committed scripts and data in this repository and is not a universal proof.

## Current blocker

The immediate blocker is obtaining green targeted and full Lean CI for commit `e63496b0...`, followed by an explicit axiom and forbidden-token audit.

## Next

1. Inspect the CI result and repair any subsequent Lean error.
2. Add warnings-as-errors and axiom-audit evidence.
3. Update issue #1 and this state file with immutable run IDs and conclusions.
4. Begin the original `q ∣ x²` divisor-certificate normalization only after Phase 1 is clean.
