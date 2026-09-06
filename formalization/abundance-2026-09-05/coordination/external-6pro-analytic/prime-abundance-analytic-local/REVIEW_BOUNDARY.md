# Review and verification boundary

## What exists

There are proposed source bodies, rather than just signatures, for the finite sieve, weak prime-product bound, harmonic ray mass, divisor-moment argument, same/different-ray overlap bounds, concrete eventual analytic estimates, strict decoding, finite transfer, elementary prime count, and final quantitative/density declarations.

The final target file has not been changed. The final theorem does not take the desired analytic bounds as assumptions. The original full-family overlap estimate is not imported under another name.

The prior repairs are documented in `REVIEW_FINDINGS.md`; the additional v2 corrections and actual preparation-test results are in `REVIEW2_FINDINGS.md`. The newly added qualified-local-reference check catches more defects than the first audit, but does not replace elaboration.

## What is not established yet

This package has not been parsed, elaborated, compiled, or checked by Lean. Therefore the existence of source bodies and the lack of an admission marker are **not** a certificate that those bodies solve their goals. Tactic scripts may fail, coercions or library signatures may require repair, and the source or mathematical argument may contain more substantive errors. There is no basis for promising that all repairs will be mechanical.

The static audit is intentionally labeled source hygiene. It checks a limited lexical model, not the Lean grammar or theorem semantics. The axiom parser's preparation tests use synthetic example logs and do not constitute real axiom reports. Python regression tests are finite, exact-arithmetic spot checks and do not prove the asymptotic estimates.

There is no claim of an independently audited new mathematical result, no priority claim, no proof of the original full-family Delta estimate, no proof for every prime, and no proof of ESC.

## Important checks for the later source run

1. Keep `Target.lean` byte-for-byte fixed. Verify `PrimeAbundance.prime_abundance` has that exact type, not a new conditional version.
2. Compile the complete local dependency closure freshly, then check the actual printed transitive axioms. Admitted proofs and extra analytic axioms are disallowed.
3. Preserve the actual packet/roughness definitions, injective strict Type-II counting, full prime powers, unordered-row overlap, one diagonal contribution, and literal endpoint term.
4. Do not use an empty finite family or only-zero integer threshold to replace the eventual positive mean argument.
5. Keep the revised, weaker intermediate estimates distinct from the stronger paper proposal. They are chosen because they suffice for the unchanged original conclusion, not because the original full-family estimate has been established.

`verify.sh` automates the source/version/type/axiom checks that are available to an actual Lean run. It cannot replace a review of whether the fixed target is the intended mathematical statement.
