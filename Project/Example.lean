import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.Tactic.NormNum.Prime

open Nat

open ArithmeticFunction Finset


-- 完全数の定義
def Perfect_ (n : ℕ) : Prop :=
  ∑ i ∈ properDivisors n, i = n ∧ 0 < n


-- 約数関数の定義
def sigma_div (k : ℕ) : ArithmeticFunction ℕ :=  -- 定義域がℕ; f(0) = 0
  ⟨fun n => ∑ d ∈ divisors n, d ^ k, by simp⟩


-- σ k n = nの約数のk乗の和
lemma sigma_apply_ {k n : ℕ} : σ k n = ∑ d ∈ divisors n, d ^ k :=
  rfl


-- k = 1 のとき、σ は約数の総和
lemma sigma_one_apply_ (n : ℕ) : σ 1 n = ∑ d ∈ divisors n, d := by simp [sigma_apply]


-- n = 1 ↔ ∑ d ∈ divisors n, d = 1
lemma one_iff_sum_divisors_eq_one (n : ℕ) : n = 1 ↔ ∑ d ∈ divisors n, d = 1 := by
  constructor <;> intro h                                         -- → (h : n = 1) ∧ ← (h : ∑ d ∈ divisors n, d = 1)
  · rw [h]                                                        -- → ∑ d ∈ divisors 1, d = 1
    rfl
  · by_contra h'                                                  -- h' : ¬n = 1 → False
    have h₁ : n ≠ 0 := by                                         -- h₁ : n ≠ 0
      by_contra h''                                               -- h'' : n = 0 → False
      rw [h''] at h                                               -- h : ∑ d ∈ divisors 0, d = 1
      simp [divisors_zero] at h                                   -- divisors 0 = ∅
    have h₂ : 1 < n := one_lt_iff_ne_zero_and_ne_one.mpr ⟨h₁, h'⟩  -- n ≠ 0 ∧ n ≠ 1 → 1 < n
    have h₃ : 1 + n ≤ ∑ d ∈ divisors n, d := by
      rw [sum_divisors_eq_sum_properDivisors_add_self]            -- 1 + n ≤ ∑ i ∈ n.properDivisors, i + n
      rw [add_le_add_iff_right]                                   -- _ → 1 ≤ ∑ i ∈ n.properDivisors, i
      apply one_le_iff_ne_zero.mpr                                -- _ → ∑ i ∈ n.properDivisors, i ≠ 0
      by_contra h₄                                                -- h₄ : ∑ i ∈ n.properDivisors, i = 0 → False
      apply h'                                                    -- False → n = 1
      rw [sum_divisors_eq_sum_properDivisors_add_self] at h       -- ∑ i ∈ n.properDivisors, i + n = 1
      rw [h₄, zero_add] at h                                      -- _ → 0 + n = 1
      exact h                                                     -- _ → n = 1
    rw [h] at h₃                                                  -- h₃ : 1 + n ≤ 1
    nth_rw 2 [← add_zero 1] at h₃                                 -- _ = 1 + 0
    rw [add_le_add_iff_left] at h₃                                -- h₃ : n ≤ 0
    have h₅ : 1 < 0 := lt_of_lt_of_le h₂ h₃                       -- h₅ : 1 < 0
    absurd h₅                                                     -- False → ¬1 < 0
    exact not_lt_zero 1                                           -- ¬1 < 0


-- ∑ divisors n = (∑ properDivisors n) + n
lemma sum_divisors_eq_sum_properDivisors_add_self_ (n : ℕ):
    ∑ i ∈ divisors n, i = (∑ i ∈ properDivisors n, i) + n := by  -- h : a ∉ s → cons a s h = {a} ∪ s
  rcases Decidable.eq_or_ne n 0 with (rfl | hn)  -- n = 0 ∨ n ≠ 0 で場合分け
  · simp
  · rw [← cons_self_properDivisors hn]           -- n ≠ 0 → {n} ∪ n.properDivisors = n.divisors
    rw [Finset.sum_cons, add_comm]               -- ∑ i ∈ {n} ∪ n.properDivisors, i = n + ∑ i ∈ n.properDivisors, i


-- n : 完全数 ↔ σ(n) = 2n
lemma perfect_iff_sum_divisors_eq_two_mul (n : ℕ) (h : 0 < n) :
    Perfect n ↔ ∑ i ∈ divisors n, i = 2 * n := by
  rw [perfect_iff_sum_properDivisors h, sum_divisors_eq_sum_properDivisors_add_self, two_mul]  -- n : Perfect ↔ ∑ i ∈ n.properDivisors, i = n, ∑ i ∈ n.divisors, i = ∑ i ∈ n.properDivisors, i + n
  constructor <;> intro h                                                                      -- → (h : ∑ i ∈ n.properDivisors, i = n) ∧ ← (h : ∑ i ∈ divisors n, i + n = n + n)
  · rw [h]                                                                                     -- →
  · apply add_right_cancel h                                                                   -- ←, a + b = c + b → a = c


-- n : 素数 ↔ ∑ d ∈ divisors n, d = 1 + n
lemma prime_iff_sum_divisors_eq_succ (n : ℕ) : n.Prime ↔ ∑ i ∈ divisors n, i = 1 + n := by
  constructor <;> intro h'                                     -- → (h' : n.Prime) ∧ ← (h' : ∑ i ∈ n.divisors, i = 1 + n)
  · rw [sum_divisors_eq_sum_properDivisors_add_self_ n]        -- ∑ i ∈ n.divisors, i = ∑ i ∈ n.properDivisors, i + n
    rw [sum_properDivisors_eq_one_iff_prime.mpr h']            -- n.Prime → ∑ i ∈ n.properDivisors, i = 1
  · rw [sum_divisors_eq_sum_properDivisors_add_self_ n] at h'  -- ∑ i ∈ n.divisors, i = ∑ i ∈ n.properDivisors, i + n
    apply add_right_cancel at h'                               -- a + b = c + b → a = c
    rw [sum_properDivisors_eq_one_iff_prime] at h'             -- ∑ i ∈ n.properDivisors, i = 1 ↔ Nat.Prime n
    exact h'


-- ζ(0) = 0, ζ(x) = 1 (x ≠ 0)
def zeta : ArithmeticFunction ℕ :=
  ⟨fun x => ite (x = 0) 0 1, rfl⟩


-- ArithmeticFunction同士の掛け算はディリクレ積で定義
-- (ζ * f)(x) = ∑ d ∈ divisors x, ζ(d) * f(x/d); ζ(d) = 1
theorem zeta_mul_apply_ {f : ArithmeticFunction ℕ} {x : ℕ} :
    (ζ * f) x = ∑ i ∈ divisors x, f i := by
  rw [← natCoe_nat ζ, coe_zeta_mul_apply]


-- pow k n = n ^ k, pow 0 0 = 0
def pow_ (k : ℕ) : ArithmeticFunction ℕ :=
  id.ppow k


-- (ζ * pow k) = ∑ d ∈ divisors x, d ^ k
theorem zeta_mul_pow_eq_sigma_ {k : ℕ} : ζ * pow k = σ k := by
  ext x                                   -- xを導入
  rw [sigma, zeta_mul_apply]              -- sigmaの定義展開; (ζ * pow)の計算
  apply sum_congr rfl                     -- s₁.sum f = s₂.sum g → ∀ x ∈ s₂, f(x) = g(x); f = pow k, g = d^k
  intro x' hx                             -- x'を導入
  rw [pow_apply]                          -- powの展開
  rw [if_neg (not_and_of_not_right _ _)]  -- (if c then t else e) = e → ¬c = ¬(k = 0 ∧ x' = 0)を示す → ¬x' = 0
  contrapose! hx                          -- 対偶
  simp [hx]                               -- 0は約数でない


-- 乗法的関数であること
lemma isMultiplicative_sigma {k : ℕ} : IsMultiplicative (σ k) := by
  rw [← zeta_mul_pow_eq_sigma]                          -- σ k = ζ * pow k
  apply isMultiplicative_zeta.mul isMultiplicative_pow  -- ζ.IsMultiplicative, (pow k).IsMultiplicative → (ζ * pow k).IsMultiplicative


-- メルセンヌ数の定義
def Mersenne (p : ℕ) : ℕ := 2 ^ p - 1


-- 1 から 2 ^ k までの和 = 2 ^ (k + 1) - 1 = mersenne (k + 1)
-- σ k n = nの約数のk乗の和 → σ 1 (2 ^ k) = 2 ^ k の約数の1乗の和 = 1 + 2 + 2 ^ 2 + ⋯ + 2 ^ k
lemma sigma_two_pow_eq_mersenne_succ (k : ℕ) : σ 1 (2 ^ k) = mersenne (k + 1) := by
  rw [sigma_one_apply]               -- 2 ^ k の約数の1乗の和 = 2 ^ k の約数dの和
  rw [mersenne]                      -- mersenne (k + 1) = 2 ^ (k + 1) - 1
  rw [show 2 = 1 + 1 from rfl]       -- 2 = (1 + 1)
  rw [← geom_sum_mul_add 1 (k + 1)]  -- (x + 1) ^ n = (∑ i ∈ range n, (x + 1) ^ i) * x + 1
  norm_num


-- ユークリッドの十分条件Ⅰ
-- mersenne (k + 1) が素数ならば、2 ^ k * mersenne (k + 1) は完全数
theorem perfect_two_pow_mul_mersenne_of_prime (k : ℕ) (pr : (mersenne (k + 1)).Prime) :
    Nat.Perfect (2 ^ k * mersenne (k + 1)) := by
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul]  -- nが完全数 ↔ nの約数の和 = 2 * n ∧ 0 < n
  rw [← mul_assoc, ← pow_succ']                 -- 2 * (2 ^ k * mersenne (k + 1)) = 2 ^ (k + 1) * mersenne (k + 1)
  rw [← sigma_one_apply]                        -- 2 ^ k * mersenne (k + 1)の約数iの和 = 2 ^ k * mersenne (k + 1)の約数の1乗の和
  rw [mul_comm]                                 -- 2 ^ k * mersenne (k + 1) = mersenne (k + 1) * 2 ^ k
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime ((Odd.coprime_two_right (by simp)).pow_right _)]
  -- (σ 1) (mersenne (k + 1) * 2 ^ k) = (σ 1) (mersenne (k + 1)) * (σ 1) (2 ^ k) → σ は乗法的関数
  rw [sigma_two_pow_eq_mersenne_succ]           -- (σ 1) (2 ^ k) = mersenne (k + 1)
  · rw [sigma_one_apply]                        -- ∑ d ∈ Prime.(mersenne (k + 1)).divisors, d * mersenne (k + 1) = 2 ^ (k + 1) * mersenne (k + 1)
    simp [pr]
  · positivity                                  -- 0 < 2 ^ k * mersenne (k + 1), norm_num


-- mersenne (k + 1) が素数のとき、k ≠ 0 (k ≥ 1)
lemma ne_zero_of_prime_mersenne (k : ℕ) (pr : (mersenne (k + 1)).Prime) : k ≠ 0 := by
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


-- 任意の自然数nは、自然数kとある奇数mを使って、n = 2 ^ k * m と表せる
lemma eq_two_pow_mul_odd {n : ℕ} (hpos : 0 < n) : ∃ k m : ℕ, n = 2 ^ k * m ∧ ¬Even m := by
  have h := Nat.finiteMultiplicity_iff.mpr ⟨Nat.prime_two.ne_one, hpos⟩  -- FiniteMultiplicity 2 n ↔ 2 ≠ 1 ∧ 0 < n, 有限重複 → nの中に2は有限個しかない
  obtain ⟨m, hm⟩ := pow_multiplicity_dvd 2 n                             -- 2 ^ multiplicity 2 n ∣ n → n = 2 ^ multiplicity 2 n * m
  use multiplicity 2 n, m                                               -- k = 2 ^ multiplicity 2 n, m = m を代入
  use hm                                                                -- left だけ示す
  rw [even_iff_two_dvd]                                                 -- Even m ↔ 2 ∣ m
  have hg := h.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self _)      -- multiplicity 2 n < (multiplicity 2 n).succ → ¬2 ^ (multiplicity 2 n).succ ∣ n
  contrapose! hg                                                        -- hg : 2 ∣ m → 2 ^ (multiplicity 2 n).succ ∣ n
  rcases hg with ⟨a, rfl⟩                                                -- m = 2 * a, hmに代入
  apply Dvd.intro a                                                     -- 2 ^ (multiplicity 2 n).succ ∣ n → 2 ^ (multiplicity 2 n).succ * a = n
  rw [pow_succ, mul_assoc]                                              -- 2 ^ (multiplicity 2 n).succ * a = 2 ^ multiplicity 2 n * (2 * a)
  rw [← hm]                                                             -- _ = n


-- nの真の約数xの和がnを割り切る → その和 = 1 ∨ n
theorem sum_properDivisors_dvd (n : ℕ) (h : (∑ x ∈ n.properDivisors, x) ∣ n) :
    ∑ x ∈ n.properDivisors, x = 1 ∨ ∑ x ∈ n.properDivisors, x = n := by
  rcases n with _ | n                                       -- n = 0 ∨ n = succ n で場合分け
  · simp                                                    -- n = 0 のときはok
  · rcases n with _ | n                                     -- n = succ n のとき, n = 0 ∨ n = succ n で場合分け
    · simp at h                                             -- n = 0 のときはok
    · rw [or_iff_not_imp_right]                             -- a ∨ b ↔ ¬b → a
      intro h'                                              -- h' : ¬∑ x ∈ (n + 1 + 1).properDivisors, x = n + 1 + 1
      have hlt : ∑ x ∈ n.succ.succ.properDivisors, x < n.succ.succ := lt_of_le_of_ne (Nat.le_of_dvd (Nat.succ_pos _) h) h'
      -- a < b → a ≤ b ∧ a ≠ b; (0 < n) → m ∣ n → m ≤ n
      symm                                                  -- 1 = ∑ x ∈ (n + 1 + 1).properDivisors, x
      rw [← mem_singleton]                                  -- b ∈ {a} ↔ b = a
      have h₁ : {∑ x ∈ (n + 1 + 1).properDivisors, x} ⊆ (n + 1 + 1).properDivisors := by
        apply singleton_subset_iff.mpr                      -- {a} ⊆ s ↔ a ∈ s
        exact mem_properDivisors.mpr ⟨h, hlt⟩                -- n ∈ m.properDivisors ↔ n ∣ m ∧ n < m
      have h₂ : ∑ x ∈ {∑ x ∈ (n + 1 + 1).properDivisors, x}, x = ∑ x ∈ (n + 1 + 1).properDivisors, x := by
        exact sum_singleton _ _                             -- ∑ x ∈ {a}, f x = f a
      rw [eq_properDivisors_of_subset_of_sum_eq_sum h₁ h₂]  -- h₁ → h₂ → {∑ x ∈ (n + 1 + 1).properDivisors, x} = (n + 1 + 1).properDivisors
      rw [mem_properDivisors]                               -- 1 ∈ (n + 1 + 1).properDivisors ↔ 1 ∣ n + 1 + 1 ∧ 1 < n + 1 + 1
      exact ⟨one_dvd _, Nat.succ_lt_succ (Nat.succ_pos _)⟩   -- ∀ a → 1 ∣ a ∧ (0 < succ n) → succ 0 < succ(succ n)


-- オイラーの必要条件
-- n が偶数かつ完全数ならば、mersenne (k + 1) は素数 かつ n = 2 ^ k * mersenne (k + 1) と表せる
theorem eq_two_pow_mul_prime_mersenne_of_even_perfect {n : ℕ} (ev : Even n) (perf : Nat.Perfect n) :
    ∃ k : ℕ, Nat.Prime (mersenne (k + 1)) ∧ n = 2 ^ k * mersenne (k + 1) := by
  have hpos := perf.right                                       -- hpos : 0 < n (∵ n.perfect)
  rcases eq_two_pow_mul_odd hpos with ⟨k, m, rfl, hm⟩            -- 任意の自然数nは、ある奇数mを使って、n = 2 ^ k * m と表せる
  use k                                                         -- k : ℕ を適用
  rw [even_iff_two_dvd] at hm                                   -- ¬Even m ↔ ¬2 ∣ m
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul hpos] at perf     -- 完全数の定義
  rw [← sigma_one_apply] at perf                                -- 2 ^ k * mの約数の和 = (σ 1) (2 ^ k * m)
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (Nat.prime_two.coprime_pow_of_not_dvd hm).symm] at perf
  -- (σ 1) (2 ^ k * m) = (σ 1) (2 ^ k) * (σ 1) m, (2 ^ k).coprime m
  rw [sigma_two_pow_eq_mersenne_succ] at perf                   -- (σ 1) (2 ^ k) = mersenne (k + 1)
  rw [← mul_assoc, ← pow_succ'] at perf                         -- 2 * (2 ^ k * m) = 2 ^ (k + 1) * m
  obtain ⟨j, rfl⟩ := ((Odd.coprime_two_right (by simp)).pow_right _).dvd_of_dvd_mul_left (Dvd.intro _ perf)
  -- m = mersenne (k + 1) * j (∵ mersenne(k+1).coprime 2 → mersenne(k+1).coprime 2^(k+1) → mersenne(k+1) ∣ 2^(k+1)*m → mersenne(k+1) ∣ m)
  rw [← mul_assoc, mul_comm _ (mersenne _), mul_assoc] at perf  -- 2 ^ (k + 1) * (mersenne (k + 1) * j) = mersenne (k + 1) * (2 ^ (k + 1) * j)
  have h := mul_left_cancel₀ (by positivity) perf               -- h : (σ 1) (mersenne (k + 1) * j) = 2 ^ (k + 1) * j
  rw [sigma_one_apply] at h                                     -- (σ 1) (mersenne (k + 1)) = ∑ d ∈ (mersenne (k + 1) * j).divisors, d
  rw [Nat.sum_divisors_eq_sum_properDivisors_add_self] at h     -- nの約数iの和 = nの真の約数iの和 + n自身
  rw [← succ_mersenne] at h                                     -- 2 ^ (k + 1) = mersenne (k + 1) + 1
  rw [add_mul, one_mul] at h                                    -- (mersenne (k + 1) + 1) * j = mersenne (k + 1) * j + j
  rw [add_comm] at h                                            -- a + b = b + a
  have hj := add_left_cancel h                                  -- hj : ∑ i ∈ (mersenne (k + 1) * j).properDivisors, i = j
  cases Nat.sum_properDivisors_dvd (by rw [hj]; apply Dvd.intro_left (mersenne (k + 1)) rfl) with
  -- nの真の約数xの和がnを割り切る → その和 = 1 ∨ n, j ∣ mersenne (k + 1) * j (∵ mersenne(k+1) * jの真の約数の和 = j ∣ mersenne(k+1)*j)
  | inl h_1 =>                                                  -- mersenne (k + 1) * jの真の約数の和 = 1 のとき
    have j1 : j = 1 := Eq.trans hj.symm h_1                     -- j1 : j = 1
    rw [j1, mul_one] at h_1                                     -- h_1 : ∑ x ∈ (mersenne (k + 1) * j).properDivisors, x = ∑ x ∈ (mersenne (k + 1)).properDivisors, x = 1
    rw [Nat.sum_properDivisors_eq_one_iff_prime] at h_1         -- nの真の約数xの和 = 1 ↔ n : Prime
    simp [h_1, j1]                                              -- mersenne (k + 1) : Prime ∧ 2 ^ k * (mersenne (k + 1) * 1) = 2 ^ k * mersenne (k + 1)
  | inr h_j =>                                                  -- mersenne (k + 1) * jの真の約数の和 = mersenne (k + 1) * j のとき
    have jcon := Eq.trans hj.symm h_j                           -- jcon : j = mersenne (k + 1) * j
    nth_rw 1 [← one_mul j] at jcon                              -- jcon : 1 * j = mersenne (k + 1) * j
    have jcon2 := mul_right_cancel₀ ?_ jcon                     -- jcon2 : j ≠ 0 → 1 = mersenne (k + 1)
    · exfalso                                                   -- 爆発律 (仮定の矛盾を示す)
      match k with                                              -- k = 0, succ k で場合分け, 全ての自然数は 0 or succ k
      | 0 =>                                                    -- k = 0 のとき
        apply hm                                                -- False に hm を適用
        rw [← jcon2, pow_zero, one_mul, one_mul] at ev          -- ev : j : Even
        rw [← jcon2, one_mul]                                   -- goal : 2 ∣ j
        exact even_iff_two_dvd.mp ev                            -- j : Even → 2 ∣ j
      | .succ k =>                                              -- k = succ k のとき
        apply Nat.ne_of_lt _ jcon2                              -- ¬(1 = mersenne (k.succ + 1)) → 1 < mersenne (k.succ + 1)
        rw [mersenne]                                           -- 1 < 2 ^ (k.succ + 1) - 1
        rw [← Nat.pred_eq_sub_one]                              -- n.pred = n - 1
        rw [Nat.lt_pred_iff]                                    -- a < b.pred ↔ a.succ < b
        rw [← pow_one (Nat.succ 1)]                             -- Nat.succ 1 = Nat.succ 1 ^ 1
        apply pow_lt_pow_right₀ (Nat.lt_succ_self 1) (Nat.succ_lt_succ k.succ_pos)
        -- 1 < sccc.1 = 2 → 1 < k.succ + 1 (∵ 0 < k.succ → 1 = 0.succ < k.succ.succ = k.succ + 1) → goal
    · contrapose! hm                                            -- hm : j = 0 → 2 ∣ mersenne (k + 1) * j
      simp [hm]                                                 -- 2 ∣ 0 (rw [hm, mul_zero]; exact dvd_zero 2)


-- Euclid-Euler theorem
-- n が偶数かつ完全数 ↔ mersenne (k + 1) が素数かつ n = 2 ^ k * mersenne (k + 1)
theorem even_and_perfect_iff {n : ℕ} :
    Even n ∧ Nat.Perfect n ↔ ∃ k : ℕ, Nat.Prime (mersenne (k + 1)) ∧ n = 2 ^ k * mersenne (k + 1) := by
  constructor                                                  -- → ∧ ←
  · rintro ⟨h₁, h₂⟩                                             -- →, h₁ : Even n, h₂ : n.perfect
    exact eq_two_pow_mul_prime_mersenne_of_even_perfect h₁ h₂  -- h₁ ∧ h₂ → goal
  · rintro ⟨k, h₁, rfl⟩                                         -- ←, k : ℕ, h₁ : Nat.prime (mersenne (k + 1)), n = 2 ^ k * mersenne (k + 1) を代入
    constructor                                                -- left ∧ right
    · exact even_two_pow_mul_mersenne_of_prime k h₁            -- mersenne (k + 1) : prime → Even n
    · exact perfect_two_pow_mul_mersenne_of_prime k h₁         -- mersenne (k + 1) : prime → n.perfect

#min_imports
