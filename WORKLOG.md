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
