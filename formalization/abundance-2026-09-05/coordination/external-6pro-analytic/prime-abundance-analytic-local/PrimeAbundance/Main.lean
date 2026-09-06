/- The final claim is the original target, not an analytic implication.
STATUS: complete proof-source candidate; not elaborated or compiled in this conversation. -/
import PrimeAbundance.GlobalAbundance

set_option autoImplicit false
open scoped Classical

namespace PrimeAbundance

/-- Quantitative strict Type-II prime abundance and relative prime density.
The proof uses a restricted family of genuine packets. It does not assert the
unproved full-family overlap estimate and does not assert ESC for every prime. -/
theorem prime_abundance : PrimeAbundanceClaim := by
  obtain ⟨N₀,hN₀,hbound⟩ := Analytic.quantitative_abundance
  refine ⟨Analytic.abundanceCoefficient,Analytic.abundanceBoundConstant,
    Analytic.abundanceCoefficient_pos,Analytic.abundanceBoundConstant_pos,
    N₀,by omega,hbound,Analytic.relative_density⟩

end PrimeAbundance
