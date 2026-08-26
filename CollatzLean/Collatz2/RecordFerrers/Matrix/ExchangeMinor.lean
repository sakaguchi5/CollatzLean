import CollatzLean.Collatz2.RecordFerrers.Matrix.TwoByTwoPlanarNetwork

/-!
# Record–Ferrers RF-C3: exchange determinant の 2×2 minor 化

RF-C2 の exchange 行列

  [ affineConst(u)   affineConst(v) ]
  [ gap(u)           gap(v)         ]

の determinant を計算する。

結果は exact に

`blockExchangeDeterminant u v`

となる。

これにより、これまで block swap の局所差として現れていた determinant を
行列論の 2×2 minor として既存数学へ接続できる。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-- 二ブロック exchange 行列の 2×2 minor。 -/
def exchangeMinor
    (u v : Word) : ℤ :=
  (exchangePathMatrix u v).det

/--
exchange 行列の determinant は block exchange determinant そのもの。
正因子すら不要な exact 同一視である。
-/
@[simp] theorem exchangePathMatrix_det
    (u v : Word) :
    (exchangePathMatrix u v).det =
      blockExchangeDeterminant u v := by
  rw [Matrix.det_fin_two]
  simp [exchangePathMatrix, blockExchangeDeterminant]

/-- `exchangeMinor` という行列側の名前でも同じ exact identity を得る。 -/
@[simp] theorem exchangeMinor_eq_blockExchangeDeterminant
    (u v : Word) :
    exchangeMinor u v = blockExchangeDeterminant u v := by
  simp [exchangeMinor]

/--
exchange determinant が非負であることは、
二つの列の cross product 順序と同値。

行列式の符号を純粋な整数不等式へ戻す受け口として使える。
-/
theorem blockExchangeDeterminant_nonneg_iff
    (u v : Word) :
    0 ≤ blockExchangeDeterminant u v ↔
      (affineConst v : ℤ) *
          coefficientGap (oddSteps u) (twoSteps u) ≤
        (affineConst u : ℤ) *
          coefficientGap (oddSteps v) (twoSteps v) := by
  unfold blockExchangeDeterminant
  exact sub_nonneg

/--
exchange determinant が負であることも cross product の strict 逆転と同値。
-/
theorem blockExchangeDeterminant_neg_iff
    (u v : Word) :
    blockExchangeDeterminant u v < 0 ↔
      (affineConst u : ℤ) *
          coefficientGap (oddSteps v) (twoSteps v) <
        (affineConst v : ℤ) *
          coefficientGap (oddSteps u) (twoSteps u) := by
  unfold blockExchangeDeterminant
  exact sub_neg

end RecordFerrers
end Collatz2
