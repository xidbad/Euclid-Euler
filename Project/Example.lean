import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.Tactic.NormNum.Prime

open Nat

open ArithmeticFunction Finset

-- 約数関数の定義
def sigma_div (k : ℕ) : ArithmeticFunction ℕ :=
  ⟨fun n => ∑ d ∈ divisors n, d ^ k, by simp⟩

-- 乗法的関数であること
theorem isMultiplicative_sigma {k : ℕ} : IsMultiplicative (σ k) := by
  rw [← zeta_mul_pow_eq_sigma]
  apply isMultiplicative_zeta.mul isMultiplicative_pow

-- 完全数の定義
def Perfect (n : ℕ) : Prop :=
  ∑ i ∈ properDivisors n, i = n ∧ 0 < n

-- 1 から 2 ^ k までの和 = 2 ^ (k + 1) - 1 = mersenne (k + 1)
-- σ k n = nの約数のk乗の和 → σ 1 (2 ^ k) = 2 ^ k の約数の1乗の和 = 1 + 2 + 2 ^ 2 + ⋯ + 2 ^ k
theorem sigma_two_pow_eq_mersenne_succ (k : ℕ) : σ 1 (2 ^ k) = mersenne (k + 1) := by
  -- 2 ^ k の約数の1乗の和 = 2 ^ k の約数dの和
  rw [sigma_one_apply]
  -- mersenne (k + 1) = 2 ^ (k + 1) - 1
  rw [mersenne]
  -- 2 = (1 + 1)
  rw [show 2 = 1 + 1 from rfl]
  -- (x + 1) ^ n　= ((x + 1) ^ 0 + (x + 1) ^ 1 + ⋯ + (x + 1) ^ (n - 1)) * x + 1  (x = 1, n = k + 1, range n = [0, n - 1])
  rw [← geom_sum_mul_add 1 (k + 1)]
  norm_num

-- ユークリッドの十分条件Ⅰ
-- mersenne (k + 1) が素数ならば、2 ^ k * mersenne (k + 1) は完全数
theorem perfect_two_pow_mul_mersenne_of_prime (k : ℕ) (pr : (mersenne (k + 1)).Prime) :
    Nat.Perfect (2 ^ k * mersenne (k + 1)) := by
  -- nが完全数 ↔ nの約数の和 = 2 * n ∧ 0 < n
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul]
  -- 2 * (2 ^ k * mersenne (k + 1)) = 2 ^ (k + 1) * mersenne (k + 1)
  rw [← mul_assoc, ← pow_succ']
  -- 2 ^ k * mersenne (k + 1)の約数iの和 = 2 ^ k * mersenne (k + 1)の約数の1乗の和
  rw [← sigma_one_apply]
  -- 2 ^ k * mersenne (k + 1) = mersenne (k + 1) * 2 ^ k
  rw [mul_comm]
  -- (σ 1) (mersenne (k + 1) * 2 ^ k) = (σ 1) (mersenne (k + 1)) * (σ 1) (2 ^ k) → σ は乗法的関数
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime ((Odd.coprime_two_right (by simp)).pow_right _)]
   -- (σ 1) (2 ^ k) = mersenne (k + 1)
  rw [sigma_two_pow_eq_mersenne_succ]
  -- ∑ d ∈ Prime.(mersenne (k + 1)).divisors, d * mersenne (k + 1) = 2 ^ (k + 1) * mersenne (k + 1)
  · rw [sigma_one_apply]
    simp [pr]
  -- 0 < 2 ^ k * mersenne (k + 1), norm_num
  · positivity

-- mersenne (k + 1) が素数のとき、k ≠ 0 (k ≥ 1)
theorem ne_zero_of_prime_mersenne (k : ℕ) (pr : (mersenne (k + 1)).Prime) : k ≠ 0 := by
  -- h : k = 0 → False
  intro h
  -- pr : Nat.prime (mersenne (k + 1)) → Nat.prime (mersenne (0 + 1)) → Nat.prime (mersenne 1)
  rw [h, zero_add] at pr
  -- mersenne 1 = 1, ¬Nat.Prime 1
  apply Nat.not_prime_one at pr
  exact pr

-- ユークリッドの十分条件Ⅱ
-- mersenne (k + 1) が素数ならば、2 ^ k * mersenne (k + 1) は偶数
theorem even_two_pow_mul_mersenne_of_prime (k : ℕ) (pr : (mersenne (k + 1)).Prime) :
    Even (2 ^ k * mersenne (k + 1)) := by
  -- pr : Nat.prime (mersenne (k + 1)) → k ≠ 0
  apply ne_zero_of_prime_mersenne at pr
  -- Even (2 ^ k * mersenne (k + 1)) → ¬k = 0 ∨ Even (mersenne (k + 1))
  simp [parity_simps]
  -- k ≠ 0 → ¬k = 0
  left; exact pr

-- 任意の自然数nは、ある奇数mを使って、n = 2 ^ k * m と表せる
theorem eq_two_pow_mul_odd {n : ℕ} (hpos : 0 < n) : ∃ k m : ℕ, n = 2 ^ k * m ∧ ¬Even m := by
  -- FiniteMultiplicity 2 n ↔ 2 ≠ 1 ∧ 0 < n, 有限重複 → nの中に2は有限個しかない?
  have h := Nat.finiteMultiplicity_iff.mpr ⟨Nat.prime_two.ne_one, hpos⟩
  -- 2 ^ multiplicity 2 n ∣ n → n = 2 ^ multiplicity 2 n * m
  obtain ⟨m, hm⟩ := pow_multiplicity_dvd 2 n
   -- k = 2 ^ multiplicity 2 n, m = m
  use multiplicity 2 n, m
  -- left だけ示す
  use hm
  -- Even a ↔ 2 ∣ a
  rw [even_iff_two_dvd]
  -- multiplicity 2 n < (multiplicity 2 n).succ → ¬2 ^ (multiplicity 2 n).succ ∣ n
  have hg := h.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self _)
  -- hg : 2 ∣ m → 2 ^ (multiplicity 2 n).succ ∣ n
  contrapose! hg
  -- m = 2 * k, hmに代入
  rcases hg with ⟨k, rfl⟩
  -- 2 ^ (multiplicity 2 n).succ ∣ n → 2 ^ (multiplicity 2 n).succ * k = n
  apply Dvd.intro k
  -- 2 ^ (multiplicity 2 n).succ * k = 2 ^ multiplicity 2 n * 2 * k
  rw [pow_succ]
  -- _ = 2 ^ multiplicity 2 n * (2 * k)
  rw [mul_assoc]
  -- _ = n
  rw [← hm]

-- オイラーの必要条件
-- n が偶数かつ完全数ならば、mersenne (k + 1) は素数 かつ n = 2 ^ k * mersenne (k + 1) と表せる
theorem eq_two_pow_mul_prime_mersenne_of_even_perfect {n : ℕ} (ev : Even n) (perf : Nat.Perfect n) :
    ∃ k : ℕ, Nat.Prime (mersenne (k + 1)) ∧ n = 2 ^ k * mersenne (k + 1) := by
  -- hpos : 0 < n (∵ n.perfect)
  have hpos := perf.right
  -- 任意の自然数nは、ある奇数mを使って、n = 2 ^ k * m と表せる
  rcases eq_two_pow_mul_odd hpos with ⟨k, m, rfl, hm⟩
  -- k : ℕ を適用
  use k
  -- ¬Even m ↔ ¬2 ∣ m
  rw [even_iff_two_dvd] at hm
  -- 完全数の定義
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul hpos] at perf
  -- 2 ^ k * mの約数の和 = (σ 1) (2 ^ k * m)
  rw [← sigma_one_apply] at perf
  -- (σ 1) (2 ^ k * m) = (σ 1) (2 ^ k) * (σ 1) m, (2 ^ k).coprime m
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (Nat.prime_two.coprime_pow_of_not_dvd hm).symm] at perf
  -- (σ 1) (2 ^ k) = mersenne (k + 1)
  rw [sigma_two_pow_eq_mersenne_succ] at perf
  -- 2 * (2 ^ k * m) = 2 ^ (k + 1) * m
  rw [← mul_assoc, ← pow_succ'] at perf
  -- m = mersenne (k + 1) * j (∵ mersenne(k+1).coprime 2 → mersenne(k+1).coprime 2^(k+1) → mersenne(k+1) ∣ 2^(k+1)*m → mersenne(k+1) ∣ m)
  obtain ⟨j, rfl⟩ := ((Odd.coprime_two_right (by simp)).pow_right _).dvd_of_dvd_mul_left (Dvd.intro _ perf)
  -- 2 ^ (k + 1) * (mersenne (k + 1) * j) = mersenne (k + 1) * (2 ^ (k + 1) * j)
  rw [← mul_assoc, mul_comm _ (mersenne _), mul_assoc] at perf
  -- h : (σ 1) (mersenne (k + 1) * j) = 2 ^ (k + 1) * j
  have h := mul_left_cancel₀ (by positivity) perf
  -- (σ 1) (mersenne (k + 1)) = ∑ d ∈ (mersenne (k + 1) * j).divisors, d
  rw [sigma_one_apply] at h
  -- nの約数iの和 = nの真の約数iの和 + n自身
  rw [Nat.sum_divisors_eq_sum_properDivisors_add_self] at h
  -- 2 ^ (k + 1) = mersenne (k + 1) + 1
  rw [← succ_mersenne] at h
  -- (mersenne (k + 1) + 1) * j = mersenne (k + 1) * j + j
  rw [add_mul, one_mul] at h
  -- a + b = b + a
  rw [add_comm] at h
  -- hj : ∑ i ∈ (mersenne (k + 1) * j).properDivisors, i = j
  have hj := add_left_cancel h
  -- nの真の約数xの和がnを割り切る → その和 = 1 ∨ n, j ∣ mersenne (k + 1) * j (∵ mersenne(k+1) * jの真の約数の和 = j ∣ mersenne(k+1)*j)
  cases Nat.sum_properDivisors_dvd (by rw [hj]; apply Dvd.intro_left (mersenne (k + 1)) rfl) with
  -- mersenne (k + 1) * jの真の約数の和 = 1 のとき
  | inl h_1 =>
  -- j1 : j = 1
    have j1 : j = 1 := Eq.trans hj.symm h_1
  -- h_1 : ∑ x ∈ (mersenne (k + 1) * j).properDivisors, x = ∑ x ∈ (mersenne (k + 1)).properDivisors, x = 1
    rw [j1, mul_one] at h_1
  -- nの真の約数xの和 = 1 ↔ n : Prime
    rw [Nat.sum_properDivisors_eq_one_iff_prime] at h_1
  -- mersenne (k + 1) : Prime ∧ 2 ^ k * (mersenne (k + 1) * 1) = 2 ^ k * mersenne (k + 1)
    simp [h_1, j1]
  -- mersenne (k + 1) * jの真の約数の和 = mersenne (k + 1) * j のとき
  | inr h_1 =>
  -- jcon : j = mersenne (k + 1) * j
    have jcon := Eq.trans hj.symm h_1
  -- jcon : 1 * j = mersenne (k + 1) * j
    nth_rewrite 1 [← one_mul j] at jcon
  -- jcon2 : j ≠ 0 → 1 = mersenne (k + 1)
    have jcon2 := mul_right_cancel₀ ?_ jcon
  -- 爆発律 (仮定の矛盾を示す)
    · exfalso
  -- k = 0, succ k で場合分け, 全ての自然数は 0 or succ k
      match k with
  -- k = 0 のとき
      | 0 =>
  -- False に hm を適用
        apply hm
  -- ev : j : Even
        rw [← jcon2, pow_zero, one_mul, one_mul] at ev
  -- goal : 2 ∣ j
        rw [← jcon2, one_mul]
  -- j : Even → 2 ∣ j
        exact even_iff_two_dvd.mp ev
  -- k = succ k のとき
      | .succ k =>
  -- ¬(1 = mersenne (k.succ + 1)) → 1 < mersenne (k.succ + 1)
        apply Nat.ne_of_lt _ jcon2
  -- 1 < 2 ^ (k.succ + 1) - 1
        rw [mersenne]
  -- n.pred = n - 1
        rw [← Nat.pred_eq_sub_one]
  -- a < b.pred ↔ a.succ < b
        rw [Nat.lt_pred_iff]
  -- Nat.succ 1 = Nat.succ 1 ^ 1
        rw [← pow_one (Nat.succ 1)]
  -- 1 < sccc.1 = 2 → 1 < k.succ + 1 (∵ 0 < k.succ → 1 = 0.succ < k.succ.succ = k.succ + 1) → goal
        apply pow_lt_pow_right₀ (Nat.lt_succ_self 1) (Nat.succ_lt_succ k.succ_pos)
  -- hm : j = 0 → 2 ∣ mersenne (k + 1) * j
    · contrapose! hm
  -- 2 ∣ 0 (rw [hm, mul_zero]; exact dvd_zero 2)
      simp [hm]

-- Euclid-Euler theorem
-- n が偶数かつ完全数 ↔ mersenne (k + 1) が素数かつ n = 2 ^ k * mersenne (k + 1)
theorem even_and_perfect_iff {n : ℕ} :
    Even n ∧ Nat.Perfect n ↔ ∃ k : ℕ, Nat.Prime (mersenne (k + 1)) ∧ n = 2 ^ k * mersenne (k + 1) := by
  -- → ∧ ←
  constructor
  -- →, h₁ : Even n, h₂ : n.perfect
  · rintro ⟨h₁, h₂⟩
  -- h₁ ∧ h₂ → goal
    exact eq_two_pow_mul_prime_mersenne_of_even_perfect h₁ h₂
  -- ←, k : ℕ, h₁ : Nat.prime (mersenne (k + 1)), n = 2 ^ k * mersenne (k + 1) を代入
  · rintro ⟨k, h₁, rfl⟩
  -- left ∧ right
    constructor
  -- mersenne (k + 1) : prime → Even n
    · exact even_two_pow_mul_mersenne_of_prime k h₁
  -- mersenne (k + 1) : prime → n.perfect
    · exact perfect_two_pow_mul_mersenne_of_prime k h₁

#min_imports
