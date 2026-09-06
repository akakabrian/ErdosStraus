import PrimeAbundance

-- These exact type checks fail if the final theorem is changed into a conditional interface.
example : PrimeAbundance.PrimeAbundanceClaim := PrimeAbundance.prime_abundance
#check PrimeAbundance.prime_abundance
#print axioms PrimeAbundance.prime_abundance
#print axioms PrimeAbundance.Analytic.analytic_bounds
#print axioms PrimeAbundance.Analytic.quantitative_abundance
#print axioms PrimeAbundance.Analytic.relative_density
#print axioms PrimeAbundance.Late.finite_exceptional_bound
