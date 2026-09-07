import Mathlib.Data.Int.Basic

/-!
# Collatz3: 自然数差の符号付き表示

差の符号そのものが数学的情報になる量では `Nat.sub` を使わず、
最初から整数差として扱う。
-/

namespace Collatz3
namespace Arithmetic

/-- 自然数 `a,b` の情報を失わない符号付き差 `a-b`。 -/
def delta (a b : ℕ) : ℤ :=
  (a : ℤ) - (b : ℤ)

@[simp] theorem delta_self (a : ℕ) : delta a a = 0 := by
  simp [delta]

@[simp] theorem delta_pos_iff {a b : ℕ} :
    0 < delta a b ↔ b < a := by
  simp [delta]

@[simp] theorem delta_nonneg_iff {a b : ℕ} :
    0 ≤ delta a b ↔ b ≤ a := by
  simp [delta]

@[simp] theorem delta_neg_iff {a b : ℕ} :
    delta a b < 0 ↔ a < b := by
  simp [delta]
  omega

end Arithmetic
end Collatz3
