# Prime abundance: verified analytic Lean formalization

**Status: verified.** On 6 September 2026, the guarded fresh-source verifier
compiled all 24 local source files in the final import closure and accepted the
required axiom reports. The ordinary project build also completed 7,909 jobs.
See `FINAL_VERIFICATION.json` in the published source package and
`../../FINAL_ANALYTIC_VERIFICATION.md` in the research tree.

The final declaration is present:

```lean
PrimeAbundance.prime_abundance : PrimeAbundance.PrimeAbundanceClaim
```

It is in `PrimeAbundance/Main.lean`. It does **not** accept mean estimates, overlap estimates, a sieve theorem, or the final conclusion as hypotheses. The imported source chain contains the proposed derivations of those ingredients.

This package supersedes `prime-abundance-formal-work.zip`. Use a new directory rather than merging it into the earlier partial directory. It does not use the earlier composite-root-count draft.

## Second-pass revision

This revision fixes an undefined determinant helper, two incorrect mathlib namespaces, a mismatched totient-sum rewrite, and several other proof-body steps. It also repairs reproduced false accepts in the axiom-name and Lean-version guards and isolates future local compilation in fresh staged source/object trees. The target and `GoalCheck.lean` are unchanged.

Read `REVIEW_FINDINGS.md` and `CHANGES.patch` for the exact historical findings,
changes, and limitations. Those documents describe the state before the final
Lean run; their pre-run warnings are retained as provenance, not current status.

## Additional source review (v2)

This revision supersedes **`prime-abundance-analytic-reviewed.zip`**. Use a fresh
output directory. `REVIEW2_FINDINGS.md` documents further source-level corrections
in the finite product moments, prime-tuple reindexing, different-ray overlap sum,
and second-moment aggregation. All 279 pre-existing theorem/lemma signatures are
unchanged; `Target.lean`, `Packets.lean`, `Main.lean`, and `GoalCheck.lean` remain
byte-for-byte unchanged. `REVIEW_FINDINGS.md` and `CHANGES.patch` are the earlier
review history, not a report of this revision.

The source-review changes are in `REVIEW2_CHANGES.patch`, with preparation logs
under `logs/review2/`. Later statement-preserving proof-body repairs were checked
by the final Lean run. The theorem statements and hypotheses were not weakened.

Run the new finite-identity/known-pattern checks separately with:

```bash
python3 review2_tests.py --json logs/review2/new-local-run.json
```

Those Python checks do not execute Lean or validate the asymptotic proof.

## What statement is being implemented?

The final verifier locks `PrimeAbundance/Target.lean`. Its SHA-256 is:

```
f75f42dda13a48390f253fcd16ff40a01b22bbd61b067f759dd4516b1d0ae0dc
```

The statement asserts the existence of positive constants `c,C` and a natural threshold `N₀`, such that, for all `N ≥ N₀`, the number of primes `2 ≤ p ≤ N` lacking

```
floor(c * (log p)^3 / log(log p))
```

distinct strictly ordered Type-II solutions is bounded by

```
C * N * (log(log N))^3 / (log N)^3.
```

It also asserts that the ratio of this exceptional count to the number of primes up to `N` tends to zero. A strict solution has positive natural denominators `x < y < z`, the exact rational Egyptian-fraction identity, divisibility of `y,z` by `p`, and `gcd(p,x)=1`. Multiplicity is an injection from `Fin r`, not a count of parameter names or an assumption of finiteness of all solutions.

This is **not** the assertion that every prime has a solution, and it is not ESC. The bound for the original full-family overlap `Delta_Y` remains outside this implementation.

## Proof route

The selected packets are the same genuine subfamily as in the replacement paper argument:

```
B = 2^n
K = floor((log B)^2) + 2
K ≤ a < b ≤ B,  gcd(a,b)=1,  B^4 < u ≤ B^6
M = 3*a*b*u,  s = 3*a^2*u,  Q = 12*a*b*u - 1
minFac(Q) > floor((log(B^8))^100).
```

Rough composite moduli are retained. Parameter injectivity, strictness, and the full-gcd compatibility identity are implemented in source.

To prove the **original** final rate, the implementation deliberately establishes only the estimates it needs:

```
mean(2^n) ≥ n^3 / (A * log(n+1))          eventually
0 < mean(2^n)                            eventually
overlap(2^n) ≤ D * n^3                    for n ≥ 3
```

Here `A,D` are explicit positive real constants. This is weaker than the draft's stronger overlap claim `O(1/log B)`, but sufficient for the unchanged theorem. No upper mean estimate is required. The public combined result is `PrimeAbundance.Analytic.analytic_bounds`.

The source uses a finite geometric-product version of Bonferroni, a finite-exponent-tuple weak Mertens argument, a divisor-moment estimate, a delayed gcd kernel, the exact finite second-moment bound, and an elementary prime-count lower bound. It does not import an unproved analytic interface, a PNT assumption, a Henriot estimate, or a composite square-root-count assumption. Ordinary proved mathlib results remain dependencies, including the Chebyshev *upper* bound used in the prime-product argument.

See `PROOF_MAP.md` for the module chain and exact estimates. See `REVIEW_BOUNDARY.md` before interpreting the preparation checks.

## Reproduce verification

Pinned versions:

```
Lean:    leanprover/lean4:v4.27.0
mathlib: a3a10db0e9d66acbebf76c5e6a135066525ac900  (v4.27.0)
```

With an already initialized matching Lake workspace and mathlib cache:

```bash
bash verify.sh /absolute/path/to/the/matching/lake-workspace
```

For a new environment, from this package directory after installing the pinned Lean toolchain:

```bash
lake update
lake exe cache get
bash verify.sh
```

The verifier checks the exact release token and mathlib revision, checks that tracked mathlib sources are unmodified, locks the target and `GoalCheck.lean` hashes, records execution-support hashes, and computes the local import order. It copies only the audited Lean sources to a clean temporary staging tree and recompiles every local source in the final goal's import closure into a **separate new temporary object directory**. Relative Lake search paths are resolved against the matching workspace before entering the staging tree. It does not count old local `.olean` files as success. Cached upstream mathlib dependencies are allowed; this is not a source rebuild of all of mathlib.

`GoalCheck.lean` checks the final declaration's type and prints axiom dependencies for the final theorem, both analytic/density outputs, and the finite transfer. The audit allows only `propext`, `Classical.choice`, and `Quot.sound`, and rejects missing/duplicate reports, `sorryAx`, or other axioms. A partial module build cannot satisfy the final-goal gate.

Each run has a separate directory under `logs/lean-run-*`. A successful run
writes `verification-result.json` there. The published source package includes
the successful result as `FINAL_VERIFICATION.json`; its reported status is
`FINAL_GOAL_ELABORATED_AND_REQUIRED_AXIOM_REPORTS_ACCEPTED`.

On errors, repair the earliest failed source module in the reported dependency order and run the verifier again. Do not weaken `Target.lean`, replace estimates with hypotheses, insert admitted proofs, or accept a check of an unrelated declaration. No claim is made that required repairs will be limited to API spelling or syntax.

## What was actually run during preparation?

Only these non-Lean checks:

```bash
python3 static_audit.py --json logs/static-audit.json
python3 regression_tests.py --json logs/finite-regression.json
python3 check_axioms.py --self-test
python3 review_tests.py --json logs/review-regressions.json
bash -n verify.sh
```

The static audit checks source hygiene, declaration-body presence, target/check-file integrity, local-import closure, selected qualified-local-name availability, and limited delimiter consistency. It is **not** a Lean parser or proof checker.

The finite regression tests use exact Python integers and fractions. They test residue errors, Bonferroni remainders, the long-interval sieve, divisor inequalities, harmonic ray mass, gcd kernels, determinant identities, and strict prime Type-II decoding. They use auxiliary finite cutoffs rather than pretending to sample the enormous eventual actual-cutoff regime. They do not prove an asymptotic result.

The final v0.5 paper and source package are published at
<https://github.com/akakabrian/ErdosStraus/releases/tag/prime-abundance-v0.5>.

## Reference text

`reference/` preserves the original review packet and the earlier restricted-family paper proposal. These are reference documents, not verification reports. The source implements the unchanged final target with the weaker sufficient intermediate estimates documented above; it does not certify every stronger assertion in the reference proposal.
