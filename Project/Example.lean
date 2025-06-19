import Mathlib.NumberTheory.ArithmeticFunction

open Nat

open ArithmeticFunction Finset

/-- `σ k n` is the sum of the `k`th powers of the divisors of `n` -/
def sigma_div (k : ℕ) : ArithmeticFunction ℕ :=
  ⟨fun n => ∑ d ∈ divisors n, d ^ k, by simp⟩

#check sigma_div

theorem isMultiplicative_sigma {k : ℕ} : IsMultiplicative (σ k) := by
  rw [← zeta_mul_pow_eq_sigma]
  apply isMultiplicative_zeta.mul isMultiplicative_pow

--#min_imports
