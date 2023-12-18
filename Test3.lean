-- 約数
import Mathlib.NumberTheory.Divisors
-- 集合
import Mathlib.Data.Finset.Basic

-- 約数の総和の定義
def divisors_sum (n : ℕ) : ℕ :=
  (Nat.divisors n).sum id

-- 具体例 2の約数の総和は3
#guard divisors_sum 2 = 3
