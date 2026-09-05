import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.GapOneSuffixHenselBridge
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleConvergent22Checkpoint
import CollatzLean.Collatz2.CSTMicro.DoubleDecomposition.ExactGapOneBeattyCertificate


/-!
# 第3例探索 1: endpoint / start の有限範囲 certificate

解析側で得る multiplier `m` の上界を、探索 hot path から分離する。
後段が必要とするのは

  m < 54_709_494_565_756_179_604

だけであり、この一つの不等式から

* endpoint `2m+1 < 3^42`
* start    `3m+1 < 2^68`

が純整数算術で従う。

このファイルは解析的上界そのものを公理化せず、proof-only な
`ThirdExampleRangeCertificate` に隔離する。将来 Denjoy--Koksma / 有理対数 bound を
形式化した時は、この structure の constructor を一つ与えれば後段は変更不要である。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

open DoubleDecomposition

/-- `m < cutoff` なら endpoint が `3^42` 未満になる最大の自然な cutoff。 -/
def thirdExampleEndpointMultiplierCutoff : ℕ :=
  54_709_494_565_756_179_604

/-- 固定 target に対する解析的有限範囲 certificate。 -/
structure ThirdExampleRangeCertificate : Prop where
  multiplier_lt :
    ∀ {w : Word} {deficit gap m : ℕ},
      ExactCriticalGapOneFerrersCertificate
        w thirdExampleTargetP thirdExampleTargetH deficit gap m →
      m < thirdExampleEndpointMultiplierCutoff

/-- `m < cutoff` の最大値 `cutoff-1` を endpoint に入れても `3^42` 未満。 -/
theorem thirdExampleEndpointMultiplierCutoff_spec :
    2 * (thirdExampleEndpointMultiplierCutoff - 1) + 1 < 3 ^ 42 := by
  norm_num [thirdExampleEndpointMultiplierCutoff]

/-- 同じ最大値を start に入れても `2^68` 未満。 -/
theorem thirdExampleStartCutoff_spec :
    3 * (thirdExampleEndpointMultiplierCutoff - 1) + 1 < 2 ^ 68 := by
  norm_num [thirdExampleEndpointMultiplierCutoff]

/-- 真の target candidate の endpoint は `3^42` 未満。 -/
theorem thirdExampleEndpoint_lt_threePow42
    (R : ThirdExampleRangeCertificate)
    {w : Word}
    {deficit gap m : ℕ}
    (C : ExactCriticalGapOneFerrersCertificate
      w thirdExampleTargetP thirdExampleTargetH deficit gap m) :
    gapOneEndpointValue m < thirdExampleRightModulus := by
  have hm : m < thirdExampleEndpointMultiplierCutoff := R.multiplier_lt C
  have hCut := thirdExampleEndpointMultiplierCutoff_spec
  unfold gapOneEndpointValue thirdExampleRightModulus
  omega

/-- 同じ range certificate から start は `2^68` 未満。 -/
theorem thirdExampleStart_lt_twoPow68
    (R : ThirdExampleRangeCertificate)
    {w : Word}
    {deficit gap m : ℕ}
    (C : ExactCriticalGapOneFerrersCertificate
      w thirdExampleTargetP thirdExampleTargetH deficit gap m) :
    gapOneStartValue m < thirdExampleLeftModulus := by
  have hm : m < thirdExampleEndpointMultiplierCutoff := R.multiplier_lt C
  have hCut := thirdExampleStartCutoff_spec
  unfold gapOneStartValue thirdExampleLeftModulus
  omega

/-- multiplier 自身も `2^68` 未満。ZMod 代表元一意性で使う。 -/
theorem thirdExampleMultiplier_lt_twoPow68
    (R : ThirdExampleRangeCertificate)
    {w : Word}
    {deficit gap m : ℕ}
    (C : ExactCriticalGapOneFerrersCertificate
      w thirdExampleTargetP thirdExampleTargetH deficit gap m) :
    m < thirdExampleLeftModulus := by
  have hm := R.multiplier_lt C
  have hCut := thirdExampleStartCutoff_spec
  unfold thirdExampleLeftModulus at *
  omega

end ThirdExampleSearch
end CSTMicro
end Collatz2
