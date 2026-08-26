import CollatzLean.Collatz2.RecordFerrers.Deformation.ThreeBlockBraid
import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyNonneg

/-!
# Record–Ferrers RF-C2: 2×2 平面経路行列の受け口

二ブロック `u,v` から、次の 2×2 行列を作る。

* 第0行: 各ブロックの `affineConst`
* 第1行: 各ブロックの `coefficientGap`

後段 RF-C3 で、この行列式が `blockExchangeDeterminant u v` そのものになる。

ここでは一般の有向平面グラフや LGV 補題そのものは formalize しない。
代わりに、非負重みの平面非交差経路網から得られる path matrix が満たす
「全ての小行列式が非負」という結論を受け取る薄い証明書を用意する。

したがって将来、具体的な Record–Ferrers network を構成した場合は、
その network からこの証明書を与えるだけで RF-C4 の符号障害へ接続できる。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/--
二ブロックの affine 値と coefficient gap を並べた 2×2 行列。

行列式が exchange determinant になる向きで列を `u,v` の順に置く。
-/
def exchangePathMatrix
    (u v : Word) : Matrix (Fin 2) (Fin 2) ℤ :=
  fun i j =>
    if i = 0 then
      if j = 0 then
        (affineConst u : ℤ)
      else
        (affineConst v : ℤ)
    else
      if j = 0 then
        coefficientGap (oddSteps u) (twoSteps u)
      else
        coefficientGap (oddSteps v) (twoSteps v)

@[simp] theorem exchangePathMatrix_zero_zero
    (u v : Word) :
    exchangePathMatrix u v 0 0 = (affineConst u : ℤ) := by
  simp [exchangePathMatrix]

@[simp] theorem exchangePathMatrix_zero_one
    (u v : Word) :
    exchangePathMatrix u v 0 1 = (affineConst v : ℤ) := by
  simp [exchangePathMatrix]

@[simp] theorem exchangePathMatrix_one_zero
    (u v : Word) :
    exchangePathMatrix u v 1 0 =
      coefficientGap (oddSteps u) (twoSteps u) := by
  simp [exchangePathMatrix]

@[simp] theorem exchangePathMatrix_one_one
    (u v : Word) :
    exchangePathMatrix u v 1 1 =
      coefficientGap (oddSteps v) (twoSteps v) := by
  simp [exchangePathMatrix]

/--
minimal FirstCrossing block の coefficient gap は正。

minimality そのものより、`FirstCrossing` の terminal contracting が本質である。
-/
theorem coefficientGap_pos_of_minimalBlock
    {w : Word}
    (M : MinimalBlock w) :
    0 < coefficientGap (oddSteps w) (twoSteps w) := by
  have hPow :
      3 ^ oddSteps w < 2 ^ twoSteps w :=
    (contracting_iff_threePow_lt_twoPow).1 M.firstCrossing.terminalContracting
  unfold coefficientGap
  exact sub_pos.mpr (by exact_mod_cast hPow)

/--
二つの minimal block から作った exchange 行列では、
四つの 1×1 成分はすべて非負である。

したがって、この 2×2 行列が全非負であることを妨げる最初の候補は
2×2 行列式の符号になる。
-/
theorem exchangePathMatrix_entries_nonneg_of_minimalBlocks
    {u v : Word}
    (hu : MinimalBlock u)
    (hv : MinimalBlock v) :
    0 ≤ exchangePathMatrix u v 0 0 ∧
      0 ≤ exchangePathMatrix u v 0 1 ∧
      0 ≤ exchangePathMatrix u v 1 0 ∧
      0 ≤ exchangePathMatrix u v 1 1 := by
  have hgu :
      0 ≤ coefficientGap (oddSteps u) (twoSteps u) :=
    le_of_lt (coefficientGap_pos_of_minimalBlock hu)
  have hgv :
      0 ≤ coefficientGap (oddSteps v) (twoSteps v) :=
    le_of_lt (coefficientGap_pos_of_minimalBlock hv)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [exchangePathMatrix]
  · simp [exchangePathMatrix]
  · simpa [exchangePathMatrix] using hgu
  · simpa [exchangePathMatrix] using hgv

/--
2×2 平面非交差経路網から得られる path matrix の代数的な受け口。

この段階では network のグラフ構造を保持せず、
LGV 型理論が最終的に与える「path matrix は全非負」という証明だけを保持する。
-/
structure TwoByTwoPlanarNetworkCertificate
    (M : Matrix (Fin 2) (Fin 2) ℤ) : Prop where
  totallyNonnegative : M.IsTotallyNonneg

/--
exchange 行列そのものが平面非交差経路網の path matrix として実現された、
という後続用の証明書型。
-/
abbrev ExchangePlanarNetworkCertificate
    (u v : Word) : Prop :=
  TwoByTwoPlanarNetworkCertificate (exchangePathMatrix u v)

end RecordFerrers
end Collatz2
