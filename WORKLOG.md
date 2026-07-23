# Worklog

Append-only project log. Dates use Pacific/Honolulu unless noted.

## 2026-07-22 — Phase 1 CI repair

### Inspected

- Research issues #1–#5.
- Formal Conjectures draft PR #2 and branch `erdos-242-phase1`.
- All eight Erdős–Straus helper modules.
- Exact Formal Conjectures target `FormalConjectures/ErdosProblems/242.lean`.
- Previous workflow runs at head `b7f3ea006a06ca61f28a4a4c8f482996501f8d7f`.

### Confirmed previous state

- Copyright workflow passed.
- Full repository workflow passed at the previous head.
- Targeted Erdős 242 workflow failed only in `MinimalCounterexample.lean` at the attempted `omega` proof of `2 ≤ p`.

### Changed

Formal Conjectures branch commit:

```text
e63496b0bd64b9383df186e09a9999940d623f66
```

Change:

```lean
have hpTwo : 2 ≤ p := hpCounter.1.le
rw [Nat.prime_iff_not_exists_mul_eq]
refine ⟨hpTwo, ?_⟩
```

Reopened draft PR #2 to trigger pull-request CI and updated its description to state explicitly that the main conjecture remains open.

### CI triggered

- `29975162859` — Erdős 242 targeted Lean check.
- `29975162879` — full Lean project/docs build.
- `29975162925` — copyright check.

At log creation, copyright passed and both Lean runs remained in progress.

### Environment limitation

The local execution container could not resolve `github.com`, so it could not clone the repository or run `lake` locally. GitHub connector writes and GitHub Actions are being used for source changes and kernel verification. This limitation must remain explicit in final reporting.

### Next

Inspect CI, repair any subsequent error, then add warnings-as-errors, axiom, and forbidden-token audit evidence.

## 2026-07-22 — Phase 1 completion gates

### Verified

At Phase 1 head:

```text
56ebdc61140eff1ab2166f9715b3af3283874106
```

Targeted run `29975624155` passed:

- all eight helper modules with `lake --wfail build`;
- forbidden-token scan for `sorry`, `admit`, `native_decide`, and added axioms;
- standalone `#print axioms` audit with no `sorryAx`.

Copyright run `29975624160` passed. The full repository workflow `29975624182` passed its `Build project` step and remained in long-running documentation generation.

## 2026-07-22 — Divisor-square normalization

### Formalized

Created branch `erdos-242-typeii-equivalence` and draft PR #9.

Kernel-checked theorems at head

```text
fb81c29d727068efc89ebb9be56a23818fc5e924
```

include:

- normalization of `q∣x²` by `gcd(x,q)` to coprime divisors;
- cancellation of the gcd under `Coprime d x`;
- direct bridge to a strict decomposition;
- automatic offset coprimality for prime targets;
- a prime-specific strict Bradford certificate.

Targeted run `29977268341` and copyright run `29977268327` passed. The full workflow `29977268329` passed its Lean project build step.

## 2026-07-22 — Exact computation through 100 million

### Reproduced

Rebuilt the exact profiler and checked every prime

```text
p≤100,000,000,
p≡1 mod24.
```

Exact result:

```text
primes checked: 719,781
unresolved: 0
largest k: 26
largest d: 107
a=1: 669,859
nontrivial a: 49,922
```

The prior handoff statistics were reproduced digit for digit. Code, commands, compact data, checksums, and the record certificate were committed.

## 2026-07-22 — Mordell reduction architecture

### Derived

Explicit `d=3` and `d=7` factor-pair families reduce a hypothetical prime counterexample from `1 mod24` to the six classical residues

```text
{1,121,169,289,361,529} mod840.
```

Created branch `erdos-242-mordell-reduction` and draft PR #10 with the family and reduction modules. Current targeted run `29977589520` is queued.

## 2026-07-22 — The k≤26 hypothesis fails

### Extended search

Added a segmented exact profiler for primes in Mordell's six classes and searched through `10^9`, with `k≤80`.

```text
primes checked: 1,587,581
unresolved: 0
largest first-witness k: 31
largest d: 127
```

New record:

```text
p=153633769
x=38408474
k=31
d=127
q=2821949
a=113
b=1538
c=221
s=13
```

The strict certificate was independently verified with exact integers and exact rational arithmetic. This refutes the empirical bounds `k≤26` and `d≤107`; it does not prove or disprove universal Type-II coverage.

## 2026-07-22 — Exact first-gate residue structure

### Mathematical derivation

Established the exact characterizations:

- `d=3` fails exactly when every prime factor of `x₀=(p+3)/4` is `1 mod3`;
- for even `x₁=(p+7)/4` coprime to 7, `d=7` fails exactly when every prime factor is in `{1,2,4} mod7`.

Re-analysis of the exact `10^8` data found zero violations among:

```text
289,372 d=3 failures
54,226 d=7 failures
19,190 d=11 failures of the fixed prime-factor triggers
```

Created branch `erdos-242-small-gate-residues` and draft PR #11. The branch contains explicit `d=7` constructions and attempted exact converses, awaiting CI.
