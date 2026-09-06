# Final analytic prime-abundance verification

Date: 2026-09-06 HST  
Claim: `LCM-DOWNSET-INTEGRATION-001` / `EVD-249`  
Outcome: `R` (formal verification and documentation refinement)

## Locked target

The verified declaration is

```lean
PrimeAbundance.prime_abundance : PrimeAbundance.PrimeAbundanceClaim
```

No theorem statement or hypothesis was weakened during the final repairs.
The locked target hash is
`f75f42dda13a48390f253fcd16ff40a01b22bbd61b067f759dd4516b1d0ae0dc`.

## Verification

From
`coordination/external-6pro-analytic/prime-abundance-analytic-local/`,
`bash verify.sh` compiled all 24 local Lean source files in the final import
closure into a new temporary object directory. The result is recorded in
`logs/lean-run-20260906T211440Z-IDQL8t/verification-result.json`.

- Lean: 4.27.0, commit `db93fe1608548721853390a10cd40580fe7d22ae`
- mathlib: `a3a10db0e9d66acbebf76c5e6a135066525ac900`
- final status: `FINAL_GOAL_ELABORATED_AND_REQUIRED_AXIOM_REPORTS_ACCEPTED`
- ordinary project build: 7,909 jobs completed
- audited declarations: final theorem, analytic bounds, quantitative bound,
  relative-density theorem, and finite transfer
- reported axioms only: `propext`, `Classical.choice`, `Quot.sound`

The verification is a guarded fresh build of the local source closure against
the pinned mathlib cache, not a from-source rebuild of all mathlib dependencies.

## Mathematical scope

The theorem proves the quantitative exceptional-set lower bound for strictly
ordered Type-II solutions on primes and proves that the exceptional primes have
relative density zero. It uses a genuine restricted witness subfamily and
concrete mean and overlap derivations rather than assuming those estimates.

It does not formalize the all-integer assertion, Proposition 3 exactly for the
full manuscript family, the published Elsholtz--Tao upper-bound argument used
to conclude the matching exponent three, or the sharper Section 10
`O(mu)` refinement. It is not a proof of the Erdős--Straus conjecture.

## Preprint release

The synchronized v0.5 Markdown, LaTeX, and 16-page PDF were published at
<https://github.com/akakabrian/ErdosStraus/releases/tag/prime-abundance-v0.5>
from commit `941c55c` on branch `release/prime-abundance-v0.5`.

SHA-256:

- Markdown: `62ee30a33388a931ba858f293531193a9a583ce84906e0894dac99931e3b8c19`
- LaTeX: `eef2cb5f1d246441551e4ed1253d635f2b5713cc90a92fd91be27aa2e444a9ad`
- PDF: `1157446713334d79cea4e8fabc74ec0562e2078c9a38c49ab007a1bdc01ebcb1`
