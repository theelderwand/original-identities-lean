import Mathlib.NumberTheory.ZetaValues

/-- The Basel problem: the sum of the reciprocals of the squares is π²/6.

Mathlib proves this as `hasSum_zeta_two`, via the Fourier-series / Bernoulli-polynomial
formula for ζ(2k) (`hasSum_zeta_nat`); we convert the `HasSum` statement to an
equation about `∑'`. -/
theorem basel_problem : ∑' n : ℕ, 1 / (n : ℝ) ^ 2 = Real.pi ^ 2 / 6 :=
  hasSum_zeta_two.tsum_eq

#print axioms basel_problem
