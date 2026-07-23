# Erdős–Straus Research Handoff

## Agent mandate

Continue the Erdős–Straus conjecture project rigorously and persist all useful work in:

- Research repository: https://github.com/akakabrian/ErdosStraus
- Lean integration repository: https://github.com/akakabrian/formal-conjectures
- Formal Conjectures target: `FormalConjectures/ErdosProblems/242.lean`

Work only on Erdős–Straus / Erdős Problem 242 unless the user explicitly redirects the project.

Do not merely discuss possible work. Inspect the repositories, run the Lean builds, repair failures, commit progress, update issues, and report exact status.

---

## Exact target

The existing Formal Conjectures theorem is:

```lean
namespace Erdos242

theorem erdos_242 (n : ℕ) (hn : 2 < n) :
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
      (4 / n : ℚ) = 1 / x + 1 / y + 1 / z := by
  sorry

end Erdos242
```

This is stronger than the commonly quoted version because the denominators must be strictly ordered and therefore distinct:

```text
1 ≤ x < y < z
```

Never silently replace this target with a non-distinct-denominator statement.

The conjecture is not currently solved. Computational coverage, valid infinite families, or successful Type-II certificates do not constitute a proof of the universal theorem.

---

# Current project state

## Canonical research repository

Use `akakabrian/ErdosStraus` as the canonical location for planning, issues, research notes, scripts, datasets, formalization handoffs, failed approaches, and reproducibility information.

Issues already created:

1. `Phase 1: Formalize elementary reductions`
2. `Phase 2: Type-II divisor certificate research`
3. `Phase 3: Computational invariant mining`
4. `Phase 4: Audit existing claimed proofs`
5. `Phase 5: Final proof architecture`

At the time of this handoff, the repository itself was otherwise essentially empty. Populate it rather than leaving progress only in chat or in the Formal Conjectures fork.

## Lean integration branch

Repository: `akakabrian/formal-conjectures`

Branch: `erdos-242-phase1`

Latest known branch head:

```text
b7f3ea006a06ca61f28a4a4c8f482996501f8d7f
```

A draft PR existed at https://github.com/akakabrian/formal-conjectures/pull/2. It is currently **closed and unmerged**. Do not assume it is active. The branch still contains useful work. Continue on the branch or create a clean successor branch and open a fresh PR after CI is clean.

Changed files on that branch:

```text
.github/workflows/erdos-242-fast.yml

FormalConjecturesForMathlib/NumberTheory/ErdosStraus/Basic.lean
FormalConjecturesForMathlib/NumberTheory/ErdosStraus/ElementaryFamilies.lean
FormalConjecturesForMathlib/NumberTheory/ErdosStraus/Scaling.lean
FormalConjecturesForMathlib/NumberTheory/ErdosStraus/Reduction.lean
FormalConjecturesForMathlib/NumberTheory/ErdosStraus/MinimalCounterexample.lean
FormalConjecturesForMathlib/NumberTheory/ErdosStraus/TypeIIFactorPair.lean
FormalConjecturesForMathlib/NumberTheory/ErdosStraus/DivisorResidues.lean
FormalConjecturesForMathlib/NumberTheory/ErdosStraus/SmallGates.lean
```

---

# Formalized mathematical foundation

## Certificate definitions

The Lean development uses the polynomial form

```text
4xyz = n(xy + xz + yz)
```

over natural numbers. For positive denominators this is equivalent to

```text
4/n = 1/x + 1/y + 1/z.
```

The main predicates are:

```lean
def HasDecomposition (n : ℕ) : Prop :=
  ∃ x y z : ℕ,
    0 < x ∧ 0 < y ∧ 0 < z ∧
      4 * x * y * z = n * (x * y + x * z + y * z)

def HasDistinctDecomposition (n : ℕ) : Prop :=
  ∃ x y z : ℕ,
    1 ≤ x ∧ x < y ∧ y < z ∧
      4 * x * y * z = n * (x * y + x * z + y * z)
```

`Basic.lean` also contains a bridge from a strict polynomial certificate to the rational unit-fraction equality.

## Distinct-denominator elementary families

These identities are already represented in Lean.

### Even family

For `n = 2m`, with `m ≥ 2`:

```text
x = m
y = m + 1
z = m(m + 1)
```

### Class `2 mod 3`

For `n = 3k + 2`, with `k ≥ 1`:

```text
x = k + 1
y = 3k + 2
z = (3k + 2)(k + 1)
```

### Class `3 mod 4`

For `n = 4k + 3`, put `M = (4k + 3)(k + 1)` and use:

```text
x = k + 1
y = M + 1
z = M(M + 1)
```

### Class `5 mod 8`

For `n = 8k + 5`:

```text
x = 2(k + 1)
y = (8k + 5)(k + 1)
z = 2(8k + 5)(k + 1)
```

These families preserve strict ordering.

## Divisor scaling

If `n = b*a`, `b > 0`, and `a` has a strict decomposition, multiplying all three denominators by `b` produces a strict decomposition for `n`.

This is the key argument for reducing a least counterexample to a prime.

## Residue reduction

The elementary families imply:

```text
If n > 2 and n has no strict decomposition, then n ≡ 1 (mod 24).
```

This reduction is in `Reduction.lean`.

## Minimal-counterexample theorem

The intended theorem in `MinimalCounterexample.lean` is:

```lean
theorem exists_prime_counterexample_one_mod_twenty_four
    (h : ∃ n : ℕ, IsCounterexample n) :
    ∃ p : ℕ, p.Prime ∧ p % 24 = 1 ∧
      ¬ HasDistinctDecomposition p
```

The proof chooses the least counterexample with `Nat.find`, applies scaling to rule out a proper factorization, and applies the residue reduction.

This theorem is **not yet compiling**. It is the immediate blocker described below.

---

# Type-II structural certificate

## Factor-pair identity

If positive integers satisfy

```text
p + d = 4abc
a + b = ds,
```

then

```text
4/p = 1/(abc) + 1/(pacs) + 1/(pbcs).
```

The candidate denominators are:

```text
x = abc
y = pacs
z = pbcs.
```

With the additional inequalities `a < b < ps`, the denominators are strictly ordered.

The polynomial identity and the positive/strict certificate theorems are in `TypeIIFactorPair.lean`.

## Opposite coprime divisor form

`DivisorResidues.lean` defines a condition resembling:

```text
a | x
b | x
gcd(a,b) = 1
d | a+b
p+d = 4x.
```

A coprime pair of opposite divisor residues can be converted into a Type-II factor-pair certificate.

This is a central structural route. Extend it rather than returning immediately to blind searches for arbitrary Egyptian-fraction identities.

## Small gates

`SmallGates.lean` contains early low-`d` or low-offset structural gates. Inspect it before duplicating work.

---

# Computational evidence already obtained

An exact-integer Type-II profiler was previously run for every prime

```text
p ≤ 100,000,000
p ≡ 1 (mod 24).
```

Recorded result:

```text
Primes checked:                         719,781
Unresolved primes:                      0
Largest first-witness offset k:         26
Largest d = 4k+3:                       107
Witnesses using the simpler a=1 form:   669,859
Witnesses needing nontrivial a:         49,922
```

Coverage by maximum offset:

```text
k ≤ 0:   59.7972%
k ≤ 1:   92.4663%
k ≤ 2:   97.3339%
k ≤ 5:   99.7095%
k ≤ 10:  99.9733%
k ≤ 15:  99.9986%
k ≤ 26:  100% of tested primes
```

The hardest recorded prime below `10^8` was:

```text
p = 8,803,369
x = 2,200,869
d = 107
q = 121
```

One factor-pair certificate was:

```text
a = 1
b = 18,189
c = 121
s = 170
```

This gives:

```text
4/8,803,369
  = 1/2,200,869
  + 1/181,085,300,330
  + 1/3,293,760,527,702,370.
```

Every computational certificate was intended to be checked by exact integer cross-multiplication, not floating point.

These observations are finite evidence only. They do **not** prove that `k ≤ 26` universally, `d ≤ 107` universally, every prime has a Type-II solution, or the conjecture is true.

Reproduce or recover the scripts and datasets in `akakabrian/ErdosStraus`; do not rely only on this prose summary.

---

# Immediate CI blocker

At branch head `b7f3ea006a06ca61f28a4a4c8f482996501f8d7f`, the normal repository workflow and copyright check passed.

The targeted Erdős 242 workflow failed because `MinimalCounterexample.lean` did not compile.

All of these targeted modules compiled successfully:

```text
Basic
Scaling
TypeIIFactorPair
ElementaryFamilies
DivisorResidues
Reduction
SmallGates
```

The only failing target was `MinimalCounterexample`.

The build error was:

```text
MinimalCounterexample.lean:52:15:
omega could not prove the goal:
No usable constraints found.
```

The relevant proof begins:

```lean
have hpPrime : p.Prime := by
  rw [Nat.prime_iff_not_exists_mul_eq]
  refine ⟨by omega, ?_⟩
```

Likely repair:

```lean
have hpTwo : 2 ≤ p := hpCounter.1.le
rw [Nat.prime_iff_not_exists_mul_eq]
refine ⟨hpTwo, ?_⟩
```

If projection through `IsCounterexample` is opaque to tactics, explicitly expose it with `rcases hpCounter with ⟨hp_gt_two, hp_no_decomp⟩` or `dsimp [IsCounterexample] at hpCounter`, then use `exact hp_gt_two.le`.

Do not assume this is the only remaining issue; rerun the targeted build after the first repair and continue until clean.

Targeted command:

```bash
lake build \
  FormalConjecturesForMathlib.NumberTheory.ErdosStraus.Basic \
  FormalConjecturesForMathlib.NumberTheory.ErdosStraus.ElementaryFamilies \
  FormalConjecturesForMathlib.NumberTheory.ErdosStraus.Scaling \
  FormalConjecturesForMathlib.NumberTheory.ErdosStraus.Reduction \
  FormalConjecturesForMathlib.NumberTheory.ErdosStraus.MinimalCounterexample \
  FormalConjecturesForMathlib.NumberTheory.ErdosStraus.TypeIIFactorPair \
  FormalConjecturesForMathlib.NumberTheory.ErdosStraus.DivisorResidues \
  FormalConjecturesForMathlib.NumberTheory.ErdosStraus.SmallGates
```

After it succeeds, run warning-as-error checks and the full repository build.

---

# Required next actions

## Priority 1 — Repair and verify Phase 1 Lean code

1. Clone the Formal Conjectures fork.
2. Fetch and check out `erdos-242-phase1`.
3. Fix `MinimalCounterexample.lean`.
4. Run the targeted build until all modules compile.
5. Run each new file with warnings as errors.
6. Run the complete repository build.
7. Run `#print axioms` or a dedicated audit file on important theorems.
8. Confirm no `sorry`, `admit`, `native_decide`, unsafe axioms, or hidden unverified computation.
9. Commit the fix.
10. Open a fresh draft PR if the closed PR cannot appropriately be reopened.

Phase 1 is complete only when the exact strict-denominator reductions are kernel checked.

## Priority 2 — Populate the canonical research repo

Add:

```text
README.md
HANDOFF.md
STATE.md
DECISIONS.md
WORKLOG.md
docs/
formal/
scripts/
data/
```

Suggested responsibilities:

```text
README.md       public project overview
HANDOFF.md      current agent handoff
STATE.md        exact current status and blockers
DECISIONS.md    research and architecture decisions
WORKLOG.md      dated, append-only progress
docs/           derivations, audits, literature notes
formal/         standalone Lean or port manifests
scripts/        exact search and certificate code
data/           compressed result summaries and checksums
```

Do not commit enormous raw datasets without considering Git LFS or compressed summaries.

## Priority 3 — Link the formal foundation to the exact theorem

After the polynomial certificate library is stable:

1. Import the proof module from the Erdős 242 target or create an upstream-compatible proof module.
2. Use the rational bridge theorem.
3. Preserve the exact target `1 ≤ x ∧ x < y ∧ y < z`.
4. Do not replace the final `sorry` until a universal proof exists.

At this stage only helper lemmas should be marked solved. The main theorem remains open.

## Priority 4 — Formalize the divisor-to-factor-pair equivalence

Prove rigorously that the divisor certificate used in the Type-II search yields the normalized factor-pair parameters.

The target mathematical route is roughly:

1. Start from `q | x²`.
2. Let `g = gcd(x,q)`.
3. Set `a = q/g` and `b = x/g`.
4. Use coprimality to derive `ab | x`.
5. Write `x = abc`.
6. Relate `q = a²c`.
7. Translate the residue condition into `d | a+b`.
8. Apply `TypeIIFactorPair`.

State every divisibility and positivity hypothesis precisely. Do not rely on informal cancellation in `ℕ`.

## Priority 5 — Prove and study small gates

The first structural candidate is the `d=3` / `k=0` gate.

For prime `p ≡ 1 (mod 24)`, put `x₀ = (p+3)/4`.

Investigate and formalize the condition that the first candidate succeeds exactly when `x₀` has a prime factor congruent to `2 mod 3`.

Then continue with `d = 7, 11, 15, 19, ...`.

The aim is not merely to collect identities. The aim is to understand why small offsets cover almost all primes and what a prime avoiding the first several gates must look like.

## Priority 6 — Computational invariant mining

Rebuild the exact profiler in the canonical repo. For every successful prime, record at minimum:

```text
p
x
k
d = 4x-p
a
b
c
s
q, when using the divisor certificate
factorization of x
factorization of d
whether a=1
residue class modulo selected moduli
```

Research questions:

- What constraints characterize primes needing `a > 1`?
- Do record-holder offsets correspond to a finite modular obstruction?
- Can avoiding gates through `d ≤ D` force a contradiction in the factorization of several shifted values?
- Is the observed `k ≤ 26` phenomenon a bounded-cover artifact or only a low-range coincidence?
- Can a finite set of exact Type-II gates cover the Mordell exceptional residue classes?
- Can an uncovered congruence class be constructed for every finite gate set?

Emit certificates that Lean can check independently.

## Priority 7 — Audit recent claimed proofs

A February 2026 preprint claims a full solution but appears to leave the essential congruence-covering step unproved.

A June 2026 divisor-parametrization paper gives useful certificate machinery and large finite evidence but does not establish universal coverage.

For every paper:

1. Record exact bibliographic information.
2. Extract exact theorem statements.
3. Verify every algebraic identity independently.
4. Check positivity and integrality.
5. Identify the final universal quantifier or coverage obligation.
6. Distinguish proved lemma, computational observation, heuristic, and unsupported global claim.
7. Formalize valid pieces even when the claimed full proof fails.

---

# Research strategy

The primary strategy is:

> Treat Erdős–Straus as a divisor-structure and factor-pair problem, with covering systems as a secondary tool.

Do not default to enumerating arbitrary affine denominator identities. That approach is useful for discovering families, but it has been heavily explored and may obscure the deeper obstruction.

The key structural question is:

> For every prime `p ≡ 1 mod 24`, can one find a small odd `d`, a factorization `(p+d)/4 = abc`, and coprime factors `a<b` such that `d | a+b` and `b < ps`?

A possible proof might arise from a universal Type-II coverage theorem, a finite modular gate system, a contradiction from simultaneous avoidance of many small gates, a new divisor-distribution theorem, or a different parametrization that contains all residual cases.

Keep multiple routes alive, but require each route to produce exact lemmas.

---

# Proof-integrity rules

1. **Never claim the conjecture is proved without a complete universal proof.**
2. Preserve the exact strict-denominator target.
3. No `sorry`, `admit`, `axiom`, or `native_decide` in completed proof claims.
4. `by decide` or computation is acceptable only for appropriately small decidable facts, not for smuggling in the universal theorem.
5. Separate finite computation from proof.
6. Verify certificates using exact integers or exact rationals.
7. Check positivity, nonzero denominators, integrality, and strict ordering.
8. Do not infer universal boundedness from the `10^8` experiment.
9. Keep theorem provenance and source citations.
10. Run independent checks when possible.
11. Record failed approaches; do not erase them from the research history.
12. Do not edit the main Formal Conjectures theorem to weaken it.
13. Before upstream submission, verify in a pristine checkout at an immutable commit.

---

# Suggested Git workflow

## Research repository

Use small focused branches such as:

```text
formal/phase1-minimal-counterexample
formal/typeii-equivalence
research/small-gates
compute/typeii-profiler
audit/bradford-2026
```

Use issues as work packages. Update an issue with `STATUS / PROVEN / OPEN / NEXT` before stopping.

## Formal Conjectures fork

Do not use the fork as the only project record. It is an integration target.

```bash
git clone https://github.com/akakabrian/formal-conjectures.git
cd formal-conjectures
git fetch origin erdos-242-phase1
git switch erdos-242-phase1
lake exe cache get
# repair MinimalCounterexample.lean
lake build <target modules>
lake --wfail build
```

After clean verification, open a new draft PR in the fork and preserve immutable commit hashes in `STATE.md`.

---

# First-session checklist for the next agent

Start immediately:

1. Inspect `akakabrian/ErdosStraus` issues 1–5.
2. Commit this handoff into the research repo if it is not already present.
3. Clone `akakabrian/formal-conjectures`.
4. Check out `erdos-242-phase1`.
5. Read every file in `FormalConjecturesForMathlib/NumberTheory/ErdosStraus/`.
6. Fix `MinimalCounterexample.lean`.
7. Run the targeted Lean build.
8. Repair subsequent errors until the entire target list succeeds.
9. Commit the verified fix.
10. Mirror the current formal code or a provenance manifest into `akakabrian/ErdosStraus`.
11. Update issue #1 with exact proof and CI status.
12. Continue to the divisor-to-factor-pair equivalence only after Phase 1 is clean.

Do not stop after merely describing these steps. Execute as many as the environment permits.

---

# Required stopping report

Whenever stopping, report exactly:

```text
STATUS
- Current overall state.

PROVEN
- Kernel-checked theorems and exact CI/build evidence.
- Computational results clearly labeled as finite evidence.

OPEN
- Remaining mathematical and engineering obligations.
- Exact failing theorem, file, line, or command.

NEXT
- The single highest-priority next action.
- Then the next one or two actions after it.
```

Include repository, branch, commit hash, PR or issue links, workflow run IDs, commands run, whether the full build passed, and whether the main conjecture remains open.

---

# Current stop-state summary

```text
STATUS
- Formal foundation substantially implemented.
- Seven targeted modules compile.
- MinimalCounterexample.lean remains the only known targeted Lean failure.
- Formal Conjectures draft PR #2 is closed and unmerged.
- Canonical research repo and issues exist but need files and continuing updates.

PROVEN
- Strict polynomial certificate framework.
- Strict elementary families: even, 2 mod 3, 3 mod 4, 5 mod 8.
- Divisor scaling.
- Counterexample residue reduction to 1 mod 24.
- Type-II factor-pair identity and ordered certificate theorem.
- Opposite-coprime-divisor conversion theorem.
- Several small structural gates, subject to inspection of the latest branch.
- Exact finite Type-II coverage through 10^8 was reported, but must remain labeled computational evidence.

OPEN
- Compile MinimalCounterexample.lean.
- Kernel-check the prime minimal-counterexample theorem.
- Reproduce and commit computational scripts/data.
- Prove divisor-to-factor-pair equivalence from the original q | x² certificate.
- Find a universal coverage argument or a decisive obstruction.
- The Erdős–Straus conjecture itself remains open.

NEXT
- Replace the opaque omega step establishing 2 ≤ p with an explicit proof from hpCounter, rerun the targeted build, and continue until all modules compile.
```
