# Project State

Last updated: 2026-07-22 (Pacific/Honolulu)

## Overall

- The main Erdős–Straus theorem remains **open**.
- The exact Formal Conjectures target requires `1 ≤ x < y < z`; no weakening is permitted.
- Phase 1's strict-denominator foundation is kernel checked.
- The Bradford-style `q ∣ x²` normalization and prime-specific strict bridge are kernel checked.
- Mordell's modulo-840 reduction and exact `d=3`/`d=7` gate characterizations are active formalization work.
- Exact finite Type-II evidence has been independently reproduced through `10^8` for all residual primes and extended through `10^9` for all primes in Mordell's six classes.

## Formal Conjectures integration

Repository: `akakabrian/formal-conjectures`

### Phase 1

```text
branch: erdos-242-phase1
head:   56ebdc61140eff1ab2166f9715b3af3283874106
PR:     https://github.com/akakabrian/formal-conjectures/pull/2
```

Kernel/build evidence:

- targeted warnings-as-errors, forbidden-token, and axiom audit: run `29975624155`, success;
- copyright: run `29975624160`, success;
- full repository workflow: run `29975624182`;
- the full workflow's `Build project` step passed; documentation generation remains in progress.

The standalone axiom log reports only:

```text
propext
Classical.choice
Quot.sound
```

for the audited helper theorems, with no `sorryAx`.

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
- full repository workflow `29977268329`: `Build project` passed; documentation generation remains in progress.

### Mordell reduction

```text
branch: erdos-242-mordell-reduction
head:   3f51c349306030081563331c51f8fcc01757de6a
PR:     https://github.com/akakabrian/formal-conjectures/pull/10
```

Implemented, awaiting current CI completion:

- six explicit strict `d=3`/`d=7` families;
- modulo-120 prime-counterexample reduction;
- modulo-168 prime-counterexample reduction;
- CRT intersection to `{1,121,169,289,361,529} mod 840`;
- conditional existence of a prime counterexample in a Mordell class.

Targeted workflow run `29977589520` is queued.

### Exact small-gate residues

```text
branch: erdos-242-small-gate-residues
head:   93e575c13b5a90c10e7c24f089d07d2e62d1cf8c
PR:     https://github.com/akakabrian/formal-conjectures/pull/11
```

Implemented, awaiting CI:

- explicit `d=7` prime-factor triggers for residues `3,5,6 mod 7`;
- multiplicative closure lemmas for prime-factor residue conditions;
- exact `d=3` characterization;
- exact `d=7` characterization for even `x` coprime to 7.

## Canonical research repository

Repository: `akakabrian/ErdosStraus`

Branch: `formal/phase1-minimal-counterexample`

Draft PR: https://github.com/akakabrian/ErdosStraus/pull/6

The repository now contains durable planning, state, decisions, worklog, formal provenance, derivations, literature audits, exact profilers, compact data summaries, and certificate fixtures.

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

New exact record:

```text
p=153633769
x=38408474
k=31
d=127
q=2821949
a=113, b=1538, c=221, s=13
```

This decisively refutes the empirical hypotheses `k≤26` and `d≤107`. It does not refute Type-II coverage or prove Erdős–Straus.

## Structural results

- Outside Mordell's six modulo-840 classes, the `d=3` and `d=7` families give a universal reduction.
- Failure of `d=3` is exactly the condition that every prime factor of `x_0=(p+3)/4` is `1 mod 3`.
- For even `x_1=(p+7)/4` coprime to 7, failure of `d=7` is exactly the condition that every prime factor lies in `{1,2,4} mod 7`.
- Failure of `d=11` necessarily avoids prime-factor residues `{7,8,10} mod 11`; this is not yet a sufficient characterization.

## Current blockers

1. GitHub Actions capacity has left the newest Mordell and small-gate targeted runs queued.
2. The full repository Lean build steps pass, but the shared documentation workflow remains long-running after the build step.
3. The universal coverage obligation remains mathematically open: no proof yet forces one of the Type-II gates to succeed for every Mordell-residue prime.

## Next

1. Repair and kernel-check the Mordell reduction and exact small-gate characterizations as soon as their targeted runs execute.
2. Add those theorems to the standalone axiom audit.
3. Formalize the general fixed-divisor trigger mechanism for later offsets.
4. Mine simultaneous subgroup avoidance in the new `k=31` record and the complete exact datasets.
