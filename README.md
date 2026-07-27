# Erdős–Straus / Erdős Problem 242

A rigorous research and formalization project for the conjecture

\[
\frac{4}{n}=\frac1x+\frac1y+\frac1z \qquad (n>2),
\]

using the exact Formal Conjectures target with **strictly ordered natural-number denominators**:

```text
1 ≤ x < y < z.
```

## Integrity status

The universal conjecture remains **open**. This repository distinguishes:

- kernel-checked Lean lemmas;
- exact finite computation;
- mathematical derivations awaiting formalization;
- heuristics and failed approaches.

Finite verification, Type-II certificates, and coverage through a numerical bound are not a proof of the universal theorem.

## Repositories

- Research record: `akakabrian/ErdosStraus`
- Lean integration fork: `akakabrian/formal-conjectures`
- Formal target: `FormalConjectures/ErdosProblems/242.lean`

## Current strategy

1. Kernel-check elementary strict-denominator families and reduction of a least counterexample to a prime `p ≡ 1 (mod 24)`.
2. Develop Type-II factor-pair and divisor-residue certificates.
3. Reproduce exact computational evidence and mine structural invariants.
4. Audit claimed proofs by locating the final universal coverage obligation.
5. Integrate only proven universal lemmas into the final theorem architecture.

## Project files

- `HANDOFF.md` — detailed agent mandate and current handoff.
- `STATE.md` — exact branch, commit, CI, and blocker state.
- `DECISIONS.md` — durable research and architecture decisions.
- `WORKLOG.md` — dated append-only progress.
- `docs/` — derivations, theorem audits, and research notes.
- `formal/` — provenance manifests and formalization handoffs.
- `scripts/` — exact search and certificate-generation code.
- `data/` — compact result summaries, schemas, and checksums.

## Proof-integrity rule

Do not claim Erdős–Straus proved unless the exact universal theorem is complete with no `sorry`, `admit`, added axioms, unsafe computation, or weakened denominator conditions.
