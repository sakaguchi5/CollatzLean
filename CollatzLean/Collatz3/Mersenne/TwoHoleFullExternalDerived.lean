import CollatzLean.Collatz3.Mersenne.SourceSplitTwoHoleDeepClosure
import CollatzLean.Collatz3.Mersenne.AtMostTwoHoleExternalClosure

/-!
# Collatz3 Mersenne: 分解された深部算術から A2 を再構成する

一枚岩だった `TwoHoleFullExternalArithmetic` を、

* A1: 既存 target-one external package,
* `TwoHoleKnownArithmetic`: Chim / Gouillon 特殊 corollaryと有限 modular certificate,
* `TwoHoleResidualArithmetic`: 現時点で本当に残る split-regular / target-interior residual,

から derived theorem として再構成する。

これにより A2 のうち何が既知数学・有限計算で、何が未閉鎖 arithmetic かが theorem type 上で分離される。
-/

namespace Collatz3
namespace Mersenne

/-- 分解された入力から従来の A2 package を構成する。 -/
theorem twoHoleFullExternalArithmetic_of_decomposed
    (A1 : TargetOneHoleExternalArithmetic)
    (K : TwoHoleKnownArithmetic)
    (R : TwoHoleResidualArithmetic) :
    TwoHoleFullExternalArithmetic := by
  constructor
  intro k n r L hk7 hFull
  rcases hFull with
    ⟨a, b, ha0, hab, hbn, hr, hL, hEq, _selected, _hCert, _hFull⟩ |
    ⟨a, b, ha0, han, hr, hb0, hbL, hEq, _selected, _hCert, _hFull⟩ |
    ⟨a, b, hn, hr, ha0, hab, hbL, hEq, _selected, _hCert, _hFull⟩
  · exact hEq.largeDepth_impossible_of_knownArithmetic
      K hk7 ha0 hab hbn hr hL
  · exact hEq.largeDepth_impossible_of_known_and_residual
      A1 K R.split_regular hk7 ha0 han hr hb0 hbL
  · exact hEq.largeDepth_impossible_of_residual
      A1 R.target hk7 hn hr ha0 hab hbL

/--
A1 と分解済み A2 入力から `AtMostTwoHoleDepthBound` を得る。

従来の一枚岩 A2 を直接仮定する必要はない。
-/
theorem atMostTwoHoleDepthBound_of_decomposed_external
    (A1 : TargetOneHoleExternalArithmetic)
    (K : TwoHoleKnownArithmetic)
    (R : TwoHoleResidualArithmetic) :
    AtMostTwoHoleDepthBound := by
  exact atMostTwoHoleDepthBound_of_external
    A1 (twoHoleFullExternalArithmetic_of_decomposed A1 K R)

/-- 分解済み外部入力を concrete small-hole lower bound へ直接接続する。 -/
theorem blockSparsePow3LowerBound_smallHole_of_decomposed_external
    (A1 : TargetOneHoleExternalArithmetic)
    (K : TwoHoleKnownArithmetic)
    (R : TwoHoleResidualArithmetic) :
    BlockSparsePow3LowerBound smallHoleLowerBound := by
  exact blockSparsePow3LowerBound_smallHole
    noHoleCompleteClassification
    (atMostOneHoleDepthBound_of_external A1)
    (atMostTwoHoleDepthBound_of_decomposed_external A1 K R)

end Mersenne
end Collatz3
