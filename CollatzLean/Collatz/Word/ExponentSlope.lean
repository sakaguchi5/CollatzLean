import CollatzLean.Collatz.Word.Geometry

/-!
# contracting coefficient の初等 slope bound

`2^19 < 3^12` を固定比較として使い、
`3^m < 2^J` を整数の線形不等式 `19*m < 12*J` へ落とす。
-/

namespace Collatz
namespace Word

/--
`m>0` かつ `3^m < 2^J` なら `19*m < 12*J`。
-/
theorem nineteen_mul_lt_twelve_mul_of_threePow_lt_twoPow
    {m J : ℕ}
    (hm : 0 < m)
    (hC : 3 ^ m < 2 ^ J) :
    19 * m < 12 * J := by
  have hbase : 2 ^ 19 < 3 ^ 12 := by
    norm_num
  have hbasePowRaw :=
    Nat.pow_lt_pow_left hbase (Nat.ne_of_gt hm)
  have hbasePow :
      2 ^ (19 * m) < 3 ^ (12 * m) := by
    calc
      2 ^ (19 * m) = (2 ^ 19) ^ m := by
        rw [pow_mul]
      _ < (3 ^ 12) ^ m := hbasePowRaw
      _ = 3 ^ (12 * m) := by
        rw [pow_mul]
  have hCPowRaw :=
    Nat.pow_lt_pow_left hC (by norm_num : (12 : ℕ) ≠ 0)
  have hCPow :
      3 ^ (12 * m) < 2 ^ (12 * J) := by
    calc
      3 ^ (12 * m) = 3 ^ (m * 12) := by
        congr 1
        omega
      _ = (3 ^ m) ^ 12 := by
        rw [pow_mul]
      _ < (2 ^ J) ^ 12 := hCPowRaw
      _ = 2 ^ (J * 12) := by
        rw [pow_mul]
      _ = 2 ^ (12 * J) := by
        congr 1
        omega
  by_contra hnot
  have hle : 12 * J ≤ 19 * m := by
    omega
  have htwo :
      2 ^ (12 * J) ≤ 2 ^ (19 * m) :=
    Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hle
  have hcontra :
      2 ^ (12 * J) < 2 ^ (12 * J) :=
    lt_of_le_of_lt htwo (lt_trans hbasePow hCPow)
  exact (Nat.lt_irrefl _ hcontra)

end Word
end Collatz
