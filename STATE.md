# Project State

Last updated: 2026-07-25 (Pacific/Honolulu)

## Overall

- The main Erdős–Straus theorem remains **open**.
- The Formal Conjectures target is the strict statement for `n > 2`, requiring `1 ≤ x < y < z`.
- The ordinary conjecture for `n ≥ 2` handles the endpoint `n=2` separately with `(1,2,2)`; strict ordering is impossible at that endpoint.
- Phase 1's strict-denominator foundation is kernel checked.
- The divisor-square normalization and prime-specific strict bridge are kernel checked.
- Mordell's modulo-840 reduction and the exact `d=3`/`d=7` gate characterizations have passed targeted Lean checks.
- Exact finite Type-II evidence has been independently reproduced through `10^8` for all residual primes and extended through `10^9` for all primes in Mordell's six classes.

## Formal Conjectures integration

Repository: `akakabrian/formal-conjectures`

### Phase 1

```text
branch: erdos-242-phase1
head:   56ebdc61140eff1ab2166f9715b3af3283874106
PR:     https://github.com/akakabrian/formal-conjectures/pull/2
```

Evidence:

- targeted warnings-as-errors, forbidden-token, and axiom audit: run `29975624155`, success;
- copyright: run `29975624160`, success;
- full repository workflow: run `29975624182`, success.

The standalone axiom log reports only standard foundational axioms such as
`propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.

### Divisor-square normalization

```text
branch: erdos-242-typeii-equivalence
head:   fb81c29d727068efc89ebb9be56a23818fc5e924
PR:     https://github.com/akakabrian/formal-conjectures/pull/9
```

Kernel-checked theorems:

- `divisorSquare_hasOppositeCoprimeDivisors`;
- `divisorSquare_hasDistinctDecomposition`;
- `coprime_offset_of_prime`;
- `prime_divisorSquare_hasDistinctDecomposition`.

Evidence:

- targeted audit run `29977268341`, success;
- copyright run `29977268327`, success;
- full repository workflow `29977268329`, success.

### Mordell reduction

```text
branch: erdos-242-mordell-reduction
PR:     https://github.com/akakabrian/formal-conjectures/pull/10
```

Implemented and targeted-check successful:

- six explicit strict `d=3`/`d=7` families;
- modulo-120 prime-counterexample reduction;
- modulo-168 prime-counterexample reduction;
- CRT intersection to `{1,121,169,289,361,529} mod 840`;
- conditional existence of a prime counterexample in a Mordell class.

Latest audited targeted run in this workstream: `30046653186`, success.

### Exact small-gate residues

```text
branch: erdos-242-small-gate-residues
PR:     https://github.com/akakabrian/formal-conjectures/pull/11
```

Implemented and targeted-check successful:

- explicit `d=7` prime-factor triggers for residues `3,5,6 mod 7`;
- multiplicative closure lemmas for prime-factor residue conditions;
- exact `d=3` characterization;
- exact `d=7` characterization for even `x` coprime to 7.

Latest audited targeted run in this workstream: `30046674630`, success.

### Modulo-11 and corrected modulo-9240 reduction

```text
branch: erdos-242-mod-eleven-reduction
PR:     https://github.com/akakabrian/formal-conjectures/pull/12
```

Implemented:

- eight strict modulo-11 Type-II families;
- reduction to twelve classes modulo `1320`;
- corrected `1201 mod 9240` family;
- strict `6001 mod 9240` family;
- reduction to 34 classes modulo `9240`.

The previous targeted failure was proof-engineering only: the large CRT theorem exceeded the default heartbeat budget and then encountered a misplaced local `set_option`. The option placement has been repaired. The newest head still requires a fresh successful targeted audit before these additions are called kernel checked.

### Final architecture and new residue tools

```text
branch: erdos-242-final-architecture
PR:     https://github.com/akakabrian/formal-conjectures/pull/13
```

Added, pending fresh CI:

- `ResidualPrimeCoverage`, explicitly marked as the remaining unproved universal obligation;
- a conditional strict theorem for every `n > 2`;
- a conditional ordinary theorem for every `n ≥ 2`, with `n=2` handled explicitly;
- product-divisor normalization for automaton-generated certificates;
- a generic multiplicatively closed residue obstruction theorem;
- `d=11` prime-factor triggers using the automatic divisor `3 | (p+11)/4`;
- a quadratic-residue obstruction modulo `11`.

No claim of Lean verification is made for these newest files until the targeted branch build and axiom audit pass.

## Canonical research repository

Repository: `akakabrian/ErdosStraus`

Branch: `formal/phase1-minimal-counterexample`

Draft PR: https://github.com/akakabrian/ErdosStraus/pull/6

The repository contains planning, state, decisions, worklog, proof map, failed-approach registry, formal provenance, derivations, literature audits, exact profilers, compact data summaries, and certificate fixtures.

## Exact finite computation

### All residual primes through `10^8`

```text
population: p ≤ 100,000,000, p ≡ 1 mod 24
primes checked: 719,781
unresolved: 0
largest first-witness k: 26
largest d: 107
```

This run is committed and independently reproducible with `scripts/typeii_profiler.py`.

### Mordell-residue primes through `10^9`

```text
population: primes p ≤ 1,000,000,000 with
            p mod 840 ∈ {1,121,169,289,361,529}
primes checked: 1,587,581
unresolved with k ≤ 80: 0
largest first-witness k: 31
largest d: 127
```

Record certificate:

```text
p=153633769
x=38408474
k=31
d=127
q=2821949
a=113, b=1538, c=221, s=13
```

This refutes the empirical hypotheses `k≤26` and `d≤107`. It does not refute Type-II coverage or prove Erdős–Straus.

## Structural results

- Outside Mordell's six modulo-840 classes, the `d=3` and `d=7` families give a universal reduction.
- Failure of `d=3` is exactly the condition that every prime factor of `x_0=(p+3)/4` is `1 mod 3`.
- For even `x_1=(p+7)/4` coprime to 7, failure of `d=7` is exactly the condition that every prime factor lies in `{1,2,4} mod 7`.
- For `p ≡ 1 mod 24`, `x_2=(p+11)/4` is divisible by `3`.
- A prime factor of `x_2` in residue `7`, `8`, or `10 mod 11` gives an explicit `d=11` gate certificate.
- If every prime factor of an integer lies in `{1,3,4,5,9} mod 11`, the `d=11` gate fails.
- The exact fixed-gate condition is a finite-state search over disjoint prime-power residue assignments. This is exact for each fixed integer but is not a universal proof.

## Current blockers

1. The newest final-architecture files need a fresh successful Lean targeted build and axiom audit.
2. Mixed `d=11` residue signatures are not characterized by a simple subgroup condition; factor count alone is insufficient.
3. The universal coverage obligation remains mathematically open: no argument yet forces one Type-II gate or another construction to succeed for every residual prime.

## Next

1. Repair all diagnostics from the next targeted run until the newest modules compile with warnings as errors and no `sorryAx`.
2. Use the fixed-gate automaton to classify minimal mixed-residue obstructions at `d=11` and search for interactions with `d=3`, `d=7`, and later offsets.
3. Formalize only classifications that survive exact falsification tests and provide a genuine deductive edge.
4. Keep non-divisor approaches active; do not let modular reduction become a substitute for universal coverage.
