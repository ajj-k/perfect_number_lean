import Mathlib.Data.Nat.Basic
-- 約数のパッケージ
import Mathlib.NumberTheory.Divisors
-- 素数のパッケージ
-- coprimeはGCDで定義され、インポートされている
import Mathlib.Data.Nat.Prime
-- 集合のパッケージ
-- import Mathlib.Data.Finset.Basic

open Nat

-- Def 1: 約数の総和の定義
def divisors_sum (n : ℕ) : ℕ :=
  (divisors n).sum id

-- 具体例 2の約数の総和は3
#guard coprime 1 2
#check gcd 1 3

-- 全ての自然数は1を約数に持つ （使わなくても証明できた）
-- lemma divisor_one : ∀ (n : ℕ), (1 ∣ n) := by
--   intro n
--   use n
--   simp

-- Lem 1: gcd a b = 1 なら、gcd a b は 1 のみで割り切られる
lemma gcd_one_only_divided_by_one : ∀ (a b : ℕ), (gcd a b = 1) → (1 ∣ gcd a b) ∧ (∀ k > 1, ¬ (k ∣ gcd a b)) := by
  intros a b h_gcd
  simp
  intro k
  intro k_ineq
  intro k_gcd
  rw [h_gcd] at k_gcd
  cases k
  {
    -- k_ineqで矛盾
    contradiction
  }
  {
    rw [gcd_eq_right_iff_dvd] at k_gcd
    rw [gcd_comm] at k_gcd
    rw [gcd_one_right] at k_gcd
    rw [←k_gcd] at k_ineq
    exact lt_irrefl 1 k_ineq
  }

-- Lem 2: 互いに素な二つの自然数について、約数関数は乗法的
lemma coprime_divisor : ∀ a b : ℕ, (coprime a b) → ∀ d : ℕ, (d ∣ a ∧ d ∣ b) → d = 1  := by
  intros a b h_coprime d h_div
  have h_gcd : gcd a b = 1 := h_coprime
  have p := gcd_one_only_divided_by_one a b h_gcd
  have p_left := p.left
  rw [←dvd_gcd_iff] at h_div
  rw [h_gcd] at h_div
  have d_eq_one : d = 1 := eq_one_of_dvd_one h_div
  assumption


-- Lem 3: 2の累乗 と 奇素数 は互いに素である（これは奇数と2が互いに素であることが言えるため、qが奇素数である条件はいらない）
lemma coprime_power_of_two_and_odd_prime_numbers : ∀ e q : ℕ, ((Nat.Prime q) ∧ (¬ 2 ∣ q)) → (coprime  (Nat.pow 2 e) q) := by
  intros e q
  simp
  intros h_prime_q h_not_divided_by_2
  rw [←Nat.Prime.coprime_iff_not_dvd] at h_not_divided_by_2
  have h_power_of_two : coprime (Nat.pow 2 e) q := coprime.pow_left e h_not_divided_by_2
  assumption
  exact prime_two
