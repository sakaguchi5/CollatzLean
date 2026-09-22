import CollatzLean.Collatz3.Mersenne.SourceSplitTwoHoleDeepClosure
import CollatzLean.Collatz3.Mersenne.AtMostTwoHoleExternalClosure
import CollatzLean.Collatz3.Mersenne.TwoHoleFiniteInternal

/-!
# Collatz3 Mersenne: 分解された深部算術から A2 を再構成する

一枚岩だった `TwoHoleFullExternalArithmetic` を、

* A1: 既存 target-one external package,
* `TwoHoleKnownArithmetic`: Chim / Gouillon 特殊 corollaryと有限 modular certificate,
* `TwoHoleResidualArithmetic`: split-regular / target-interior residual,

から derived theorem として再構成する。

さらに `TwoHoleFiniteInternal` で finite certificate を内部化した後は、

* 外部既知数学: Chim / Gouillon の特殊 corollary 4本だけ,
* genuinely residual arithmetic:
  split regular と target `n=1` / `n≥4`,

という縮約版から同じ A2 を再構成できる。
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

/-! ## finite certificate 内部化後の縮約版 -/

/--
finite modular certificate を内部 theorem として補い、
Chim / Gouillon 4本と縮約 residual だけから従来 A2 を構成する。
-/
theorem twoHoleFullExternalArithmetic_of_reduced
    (A1 : TargetOneHoleExternalArithmetic)
    (K : TwoHoleDeepKnownArithmetic)
    (R : TwoHoleResidualArithmeticReduced) :
    TwoHoleFullExternalArithmetic := by
  exact twoHoleFullExternalArithmetic_of_decomposed
    A1 K.toKnownArithmetic R.toResidualArithmetic

/--
finite certificate 内部化後の `AtMostTwoHoleDepthBound`。

外部 finite certificate はもう要求しない。
-/
theorem atMostTwoHoleDepthBound_of_reduced_external
    (A1 : TargetOneHoleExternalArithmetic)
    (K : TwoHoleDeepKnownArithmetic)
    (R : TwoHoleResidualArithmeticReduced) :
    AtMostTwoHoleDepthBound := by
  exact atMostTwoHoleDepthBound_of_external
    A1 (twoHoleFullExternalArithmetic_of_reduced A1 K R)

/--
縮約済み入力を small-hole complexity lower bound へ直接接続する。
-/
theorem blockSparsePow3LowerBound_smallHole_of_reduced_external
    (A1 : TargetOneHoleExternalArithmetic)
    (K : TwoHoleDeepKnownArithmetic)
    (R : TwoHoleResidualArithmeticReduced) :
    BlockSparsePow3LowerBound smallHoleLowerBound := by
  exact blockSparsePow3LowerBound_smallHole
    noHoleCompleteClassification
    (atMostOneHoleDepthBound_of_external A1)
    (atMostTwoHoleDepthBound_of_reduced_external A1 K R)

end Mersenne
end Collatz3
