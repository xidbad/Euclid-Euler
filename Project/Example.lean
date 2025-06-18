import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.Algebra.GeomSum
import Mathlib.RingTheory.Multiplicity
import Mathlib.Tactic.NormNum.Prime

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.BigOperators
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Tactic.ArithMult

open Finset

open Nat

open ArithmeticFunction Finset

/-- `σ k n` is the sum of the `k`th powers of the divisors of `n` -/
def morishitasigma (k : ℕ) : ArithmeticFunction ℕ :=
  ⟨fun n => ∑ d ∈ divisors n, d ^ k, by simp⟩

#check morishitasigma

theorem sigma_apply1 {k n : ℕ} : σ k n = ∑ d ∈ divisors n, d ^ k :=
  rfl

theorem sigma_one_apply (n : ℕ) : σ 1 n = ∑ d ∈ divisors n, d := by simp [sigma_apply1]

theorem isMultiplicative_sigma {k : ℕ} : IsMultiplicative (σ k) := by
  rw [← zeta_mul_pow_eq_sigma]
  apply isMultiplicative_zeta.mul isMultiplicative_pow
