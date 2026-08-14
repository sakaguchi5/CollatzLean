import CollatzLean.Collatz2.Core.Word

/-!
# Collatz2 Arithmetic: contracting coefficient の初等 slope bound

固定比較

  2^19 < 3^12

だけから、contracting exponent pair

  3^p < 2^H

に対して

  19*p < 12*H

を得る。

外部入力を使わない純初等補題。
-/

namespace Collatz2
namespace Word

/--
`p > 0` かつ `3^p < 2^H` なら `19*p < 12*H`。
-/
theorem nineteen_mul_lt_twelve_mul_of_threePow_lt_twoPow
    {p H : ℕ}
    (hp : 0 < p)
    (hC : 3 ^ p < 2 ^ H) :
    19 * p < 12 * H := by
  have hbase : 2 ^ 19 < 3 ^ 12 := by
    decide
  have hbasePowRaw :=
    Nat.pow_lt_pow_left hbase (Nat.ne_of_gt hp)
  have hbasePow :
      2 ^ (19 * p) < 3 ^ (12 * p) := by
    calc
      2 ^ (19 * p) = (2 ^ 19) ^ p := by
        rw [pow_mul]
      _ < (3 ^ 12) ^ p := hbasePowRaw
      _ = 3 ^ (12 * p) := by
        rw [pow_mul]
  have hCPowRaw :=
    Nat.pow_lt_pow_left hC (by norm_num : (12 : ℕ) ≠ 0)
  have hCPow :
      3 ^ (12 * p) < 2 ^ (12 * H) := by
    calc
      3 ^ (12 * p) = 3 ^ (p * 12) := by
        congr 1
        omega
      _ = (3 ^ p) ^ 12 := by
        rw [pow_mul]
      _ < (2 ^ H) ^ 12 := hCPowRaw
      _ = 2 ^ (H * 12) := by
        rw [pow_mul]
      _ = 2 ^ (12 * H) := by
        congr 1
        omega
  by_contra hnot
  have hle : 12 * H ≤ 19 * p := by
    omega
  have htwo :
      2 ^ (12 * H) ≤ 2 ^ (19 * p) :=
    Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hle
  have hcontra :
      2 ^ (12 * H) < 2 ^ (12 * H) :=
    lt_of_le_of_lt htwo (lt_trans hbasePow hCPow)
  exact (Nat.lt_irrefl _ hcontra)

end Word
end Collatz2
