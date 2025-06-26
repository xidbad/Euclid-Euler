import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.Tactic.NormNum.Prime

open Nat

open ArithmeticFunction Finset

def sigma_div (k : ℕ) : ArithmeticFunction ℕ :=
  ⟨fun n => ∑ d ∈ divisors n, d ^ k, by simp⟩

-- theorem isMultiplicative_sigma {k : ℕ} : IsMultiplicative (σ k) := by
--   rw [← zeta_mul_pow_eq_sigma]
--   apply isMultiplicative_zeta.mul isMultiplicative_pow

-- 1 から 2 ^ k までの和 = 2 ^ (k + 1) - 1 = mersenne (k + 1)
-- σ k n = nの約数のk乗の和 → σ 1 (2 ^ k) = 2 ^ k の約数の1乗の和 = 1 + 2 + 2 ^ 2 + ⋯ + 2 ^ k
theorem sigma_two_pow_eq_mersenne_succ (k : ℕ) : σ 1 (2 ^ k) = mersenne (k + 1) := by
  rw [sigma_one_apply]               -- 2 ^ k の約数の1乗の和 = 2 ^ k の約数dの和
  rw [mersenne]                      -- mersenne (k + 1) = 2 ^ (k + 1) - 1
  rw [show 2 = 1 + 1 from rfl]       -- 2 = (1 + 1)
  rw [← geom_sum_mul_add 1 (k + 1)]  -- (x + 1) ^ n　= ((x + 1) ^ 0 + (x + 1) ^ 1 + ⋯ + (x + 1) ^ (n - 1)) * x + 1  (x = 1, n = k + 1, range n = [0, n - 1])
  norm_num

-- ユークリッドの十分条件Ⅰ
-- mersenne (k + 1) が素数ならば、2 ^ k * mersenne (k + 1) は完全数
theorem perfect_two_pow_mul_mersenne_of_prime (k : ℕ) (pr : (mersenne (k + 1)).Prime) :
    Nat.Perfect (2 ^ k * mersenne (k + 1)) := by
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul]                                                    -- nが完全数 ↔ nの約数の和 = 2 * n ∧ 0 < n
  rw [← mul_assoc, ← pow_succ']                                                                   -- 2 * (2 ^ k * mersenne (k + 1)) = 2 ^ (k + 1) * mersenne (k + 1)
  rw [← sigma_one_apply]                                                                          -- 2 ^ k * mersenne (k + 1)の約数iの和 = 2 ^ k * mersenne (k + 1)の約数の1乗の和
  rw [mul_comm]                                                                                   -- 2 ^ k * mersenne (k + 1) = mersenne (k + 1) * 2 ^ k
  rw [isMultiplicative_sigma.map_mul_of_coprime ((Odd.coprime_two_right (by simp)).pow_right _)]  -- (σ 1) (mersenne (k + 1) * 2 ^ k) = (σ 1) (mersenne (k + 1)) * (σ 1) (2 ^ k) → σ は乗法的関数
  rw [sigma_two_pow_eq_mersenne_succ]                                                             -- (σ 1) (2 ^ k) = mersenne (k + 1)
  · rw [sigma_one_apply]                                                                          -- ∑ d ∈ Prime.(mersenne (k + 1)).divisors, d * mersenne (k + 1) = 2 ^ (k + 1) * mersenne (k + 1)
    simp [pr]
  · positivity                                                                                    -- 0 < 2 ^ k * mersenne (k + 1), norm_num

-- mersenne (k + 1) が素数のとき、k ≠ 0 (k ≥ 1)
theorem ne_zero_of_prime_mersenne (k : ℕ) (pr : (mersenne (k + 1)).Prime) : k ≠ 0 := by
  intro h                        -- h : k = 0 → False
  rw [h, zero_add] at pr         -- pr : Nat.prime (mersenne (k + 1)) → Nat.prime (mersenne (0 + 1)) → Nat.prime (mersenne 1)
  apply Nat.not_prime_one at pr  -- mersenne 1 = 1, ¬Nat.Prime 1
  exact pr

-- ユークリッドの十分条件Ⅱ
-- mersenne (k + 1) が素数ならば、2 ^ k * mersenne (k + 1) は偶数
theorem even_two_pow_mul_mersenne_of_prime (k : ℕ) (pr : (mersenne (k + 1)).Prime) :
    Even (2 ^ k * mersenne (k + 1)) := by
  apply ne_zero_of_prime_mersenne at pr  -- pr : Nat.prime (mersenne (k + 1)) → k ≠ 0
  simp [parity_simps]                    -- Even (2 ^ k * mersenne (k + 1)) → ¬k = 0 ∨ Even (mersenne (k + 1))
  left; exact pr                         -- k ≠ 0 → ¬k = 0

-- 任意の自然数nは、ある奇数mを使って、n = 2 ^ k * m と表せる
theorem eq_two_pow_mul_odd {n : ℕ} (hpos : 0 < n) : ∃ k m : ℕ, n = 2 ^ k * m ∧ ¬Even m := by
  have h := Nat.finiteMultiplicity_iff.mpr ⟨Nat.prime_two.ne_one, hpos⟩  -- FiniteMultiplicity 2 n ↔ 2 ≠ 1 ∧ 0 < n, 有限重複 → nの中に2は有限個しかない?
  obtain ⟨m, hm⟩ := pow_multiplicity_dvd 2 n                             -- 2 ^ multiplicity 2 n ∣ n → n = 2 ^ multiplicity 2 n * m
  use multiplicity 2 n, m                                               -- k = 2 ^ multiplicity 2 n, m = m
  use hm                                                                -- left だけ示す
  rw [even_iff_two_dvd]                                                 -- Even a ↔ 2 ∣ a
  have hg := h.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self _)      -- multiplicity 2 n < (multiplicity 2 n).succ → ¬2 ^ (multiplicity 2 n).succ ∣ n
  contrapose! hg                                                        -- hg : 2 ∣ m → 2 ^ (multiplicity 2 n).succ ∣ n
  rcases hg with ⟨k, rfl⟩                                                -- m = 2 * k, hmに代入
  apply Dvd.intro k                                                     -- 2 ^ (multiplicity 2 n).succ ∣ n → 2 ^ (multiplicity 2 n).succ * k = n
  rw [pow_succ]                                                         -- 2 ^ (multiplicity 2 n).succ * k = 2 ^ multiplicity 2 n * 2 * k
  rw [mul_assoc]                                                        -- _ = 2 ^ multiplicity 2 n * (2 * k)
  rw [← hm]

theorem eq_two_pow_mul_prime_mersenne_of_even_perfect {n : ℕ} (ev : Even n) (perf : Nat.Perfect n) :
    ∃ k : ℕ, Nat.Prime (mersenne (k + 1)) ∧ n = 2 ^ k * mersenne (k + 1) := by
  have hpos := perf.right                                                                                   -- hpos : 0 < n (∵ n.perfect)
  rcases eq_two_pow_mul_odd hpos with ⟨k, m, rfl, hm⟩                                                        -- 任意の自然数nは、ある奇数mを使って、n = 2 ^ k * m と表せる
  use k                                                                                                     -- k : ℕ を適用
  rw [even_iff_two_dvd] at hm                                                                               -- ¬Even m ↔ ¬2 ∣ m
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul hpos] at perf                                                 -- 完全数の定義
  rw [← sigma_one_apply] at perf                                                                            -- 2 ^ k * mの約数の和 = (σ 1) (2 ^ k * m)
  rw [isMultiplicative_sigma.map_mul_of_coprime (Nat.prime_two.coprime_pow_of_not_dvd hm).symm] at perf     -- (σ 1) (2 ^ k * m) = (σ 1) (2 ^ k) * (σ 1) m, (2 ^ k).coprime m
  rw [sigma_two_pow_eq_mersenne_succ] at perf                                                               -- (σ 1) (2 ^ k) = mersenne (k + 1)
  rw [← mul_assoc, ← pow_succ'] at perf                                                                     -- 2 * (2 ^ k * m) = 2 ^ (k + 1) * m
  obtain ⟨j, rfl⟩ := ((Odd.coprime_two_right (by simp)).pow_right _).dvd_of_dvd_mul_left (Dvd.intro _ perf)  -- m = mersenne (k + 1) * j (∵ mersenne(k+1).coprime 2 → mersenne(k+1).coprime 2^(k+1) → mersenne(k+1) ∣ 2^(k+1)*m → mersenne(k+1) ∣ m)
  rw [← mul_assoc, mul_comm _ (mersenne _), mul_assoc] at perf                                              -- 2 ^ (k + 1) * (mersenne (k + 1) * j) = mersenne (k + 1) * (2 ^ (k + 1) * j)
  have h := mul_left_cancel₀ (by positivity) perf                                                           -- h : (σ 1) (mersenne (k + 1) * j) = 2 ^ (k + 1) * j
  rw [sigma_one_apply] at h                                                                                 -- (σ 1) (mersenne (k + 1)) = ∑ d ∈ (mersenne (k + 1) * j).divisors, d
  rw [Nat.sum_divisors_eq_sum_properDivisors_add_self] at h                                                 -- nの約数iの和 = nの真の約数iの和 + n自身
  rw [← succ_mersenne] at h                                                                                 -- 2 ^ (k + 1) = mersenne (k + 1) + 1
  rw [add_mul, one_mul] at h                                                                                -- (mersenne (k + 1) + 1) * j = mersenne (k + 1) * j + j
  rw [add_comm] at h                                                                                        -- a + b = b + a
  have hj := add_left_cancel h                                                                              -- hj : ∑ i ∈ (mersenne (k + 1) * j).properDivisors, i = j
  cases Nat.sum_properDivisors_dvd (by rw [hj]; apply Dvd.intro_left (mersenne (k + 1)) rfl) with           -- nの真の約数xの和がnを割り切る → その和 = 1 ∨ n, j ∣ mersenne (k + 1) * j (∵ mersenne(k+1) * jの真の約数の和 = j ∣ mersenne(k+1)*j)
  | inl h_1 =>                                                                                              -- mersenne (k + 1) * jの真の約数の和 = 1 のとき
    have j1 : j = 1 := Eq.trans hj.symm h_1                                                                 -- j1 : j = 1
    rw [j1, mul_one] at h_1                                                                                 -- h_1 : ∑ x ∈ (mersenne (k + 1) * j).properDivisors, x = ∑ x ∈ (mersenne (k + 1)).properDivisors, x = 1
    rw [Nat.sum_properDivisors_eq_one_iff_prime] at h_1                                                     -- nの真の約数xの和 = 1 ↔ n : Prime
    simp [h_1, j1]                                                                                          -- mersenne (k + 1) : Prime ∧ 2 ^ k * (mersenne (k + 1) * 1) = 2 ^ k * mersenne (k + 1)
  | inr h_1 =>                                                                                              -- mersenne (k + 1) * jの真の約数の和 = mersenne (k + 1) * j のとき
    have jcon := Eq.trans hj.symm h_1                                                                       -- jcon : j = mersenne (k + 1) * j
    nth_rewrite 1 [← one_mul j] at jcon                                                                     -- jcon : 1 * j = mersenne (k + 1) * j
    have jcon2 := mul_right_cancel₀ ?_ jcon                                                                 -- jcon2 : j ≠ 0 → 1 = mersenne (k + 1)
    · exfalso                                                                                               -- 爆発律 (仮定の矛盾を示す)
      match k with                                                                                          -- k = 0, succ k で場合分け, 全ての自然数は 0 or succ k
      | 0 =>                                                                                                -- k = 0 のとき
        apply hm                                                                                            -- False に hm を適用
        rw [← jcon2, pow_zero, one_mul, one_mul] at ev                                                      -- ev : j : Even
        rw [← jcon2, one_mul]                                                                               -- goal : 2 ∣ j
        exact even_iff_two_dvd.mp ev                                                                        -- j : Even → 2 ∣ j
      | .succ k =>                                                                                          -- k = succ k のとき
        apply Nat.ne_of_lt _ jcon2                                                                              -- ¬(1 = mersenne (k.succ + 1)) → 1 < mersenne (k.succ + 1)
        rw [mersenne]                                                                                       -- 1 < 2 ^ (k.succ + 1) - 1
        rw [← Nat.pred_eq_sub_one]                                                                          -- n.pred = n - 1
        rw [Nat.lt_pred_iff]                                                                                -- a < b.pred ↔ a.succ < b
        rw [← pow_one (Nat.succ 1)]                                                                         -- Nat.succ 1 = Nat.succ 1 ^ 1
        apply pow_lt_pow_right₀ (Nat.lt_succ_self 1) (Nat.succ_lt_succ k.succ_pos)                          -- 1 < sccc.1 = 2 → 1 < k.succ + 1 (∵ 0 < k.succ → 1 = 0.succ < k.succ.succ = k.succ + 1) → goal
    · contrapose! hm                                                                                          -- hm : j = 0 → 2 ∣ mersenne (k + 1) * j
      simp [hm]

theorem even_and_perfect_iff {n : ℕ} :
    Even n ∧ Nat.Perfect n ↔ ∃ k : ℕ, Nat.Prime (mersenne (k + 1)) ∧ n = 2 ^ k * mersenne (k + 1) := by
  constructor                                                  -- → ∧ ←
  · rintro ⟨h₁, h₂⟩                                             -- →, h₁ : Even n, h₂ : n.perfect
    exact eq_two_pow_mul_prime_mersenne_of_even_perfect h₁ h₂  -- h₁ ∧ h₂ → goal
  · rintro ⟨k, h₁, rfl⟩                                         -- ←, k : ℕ, h₁ : Nat.prime (mersenne (k + 1)), n = 2 ^ k * mersenne (k + 1) を代入
    constructor                                                -- left ∧ right
    · exact even_two_pow_mul_mersenne_of_prime k h₁            -- mersenne (k + 1) : prime → Even n
    · exact perfect_two_pow_mul_mersenne_of_prime k h₁

#min_imports
