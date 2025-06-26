import Mathlib.NumberTheory.ArithmeticFunction
-- import Mathlib.NumberTheory.LucasLehmer
-- import Mathlib.Tactic.NormNum.Prime

open Nat

open ArithmeticFunction Finset

def sigma_div (k : ℕ) : ArithmeticFunction ℕ :=
  ⟨fun n => ∑ d ∈ divisors n, d ^ k, by simp⟩

-- #check sigma_div

-- theorem isMultiplicative_sigma {k : ℕ} : IsMultiplicative (σ k) := by
--   rw [← zeta_mul_pow_eq_sigma]
--   apply isMultiplicative_zeta.mul isMultiplicative_pow

-- theorem sigma_two_pow_eq_mersenne_succ (k : ℕ) : σ 1 (2 ^ k) = mersenne (k + 1) := by
--   rw [sigma_one_apply]
--   rw [mersenne]
--   rw [show 2 = 1 + 1 from rfl]
--   rw [← geom_sum_mul_add 1 (k + 1)]
--   norm_num

#min_imports
