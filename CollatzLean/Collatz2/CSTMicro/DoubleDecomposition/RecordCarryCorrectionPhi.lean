import CollatzLean.Collatz2.CSTMicro.DoubleDecomposition.RecordFerrersRowBandPhi

/-!
# Record carry correction = shifted Phi - origin Phi

Record 構成で切り出した区間を origin へ移したとき、critical roof の carry により
一般には同じ長さの origin block と重みが一致しない。

このファイルでは、その差を column ごとの差として定義し、exact に

  shifted Phi - origin Phi

へまとめる。ここでも二つの分解そのものを同一視しない。
-/

namespace Collatz2
namespace CSTMicro
namespace DoubleDecomposition

open scoped BigOperators

/-- 長さ `len` の origin `Phi`。 -/
def originCriticalPhiZ (len : ℕ) : ℤ :=
  criticalIntervalPhiZ 0 len

/-- 開始位置 `a` の shifted `Phi`。 -/
def shiftedCriticalPhiZ (a len : ℕ) : ℤ :=
  criticalIntervalPhiZ a len

/--
Record cut を origin へ移すことで生じる carry correction。
各 column の shifted term と origin term の差を直接足し上げる。
-/
def recordCriticalCarryCorrection (a len : ℕ) : ℤ :=
  Finset.sum (Finset.range len) (fun k =>
    ((2 : ℤ) ^ (Word.criticalHeight (a + k) - Word.criticalHeight a) *
        (3 : ℤ) ^ (len - (k + 1))) -
      ((2 : ℤ) ^ (Word.criticalHeight (0 + k) - Word.criticalHeight 0) *
        (3 : ℤ) ^ (len - (k + 1))))

/--
Record carry correction は shifted `Phi` と origin `Phi` の差そのもの。

この等式が「構成用 Record 分解」と「計算用 Ostrowski/Christoffel 分解」の
接続点であり、block の同一視ではなく評価値の transport を主張する。
-/
theorem recordCriticalCarryCorrection_eq_shiftedPhi_sub_originPhi
    (a len : ℕ) :
    recordCriticalCarryCorrection a len =
      shiftedCriticalPhiZ a len - originCriticalPhiZ len := by
  unfold recordCriticalCarryCorrection shiftedCriticalPhiZ originCriticalPhiZ
    criticalIntervalPhiZ
  rw [← Finset.sum_sub_distrib]

end DoubleDecomposition
end CSTMicro
end Collatz2
