import CollatzLean.Collatz3.Mersenne.TargetOneHoleFinalExternalArithmetic
import CollatzLean.Collatz3.Mersenne.TwoHoleFinalExternalArithmetic
import CollatzLean.Collatz3.Mersenne.A2ExternalCore

/-!
# Collatz3 Mersenne: A2 から A1 external 引数を消す互換 refactor

A1 は `TargetOneHoleFinalExternalArithmetic` で完全内部化され、
旧 `TargetOneHoleExternalArithmetic` も

`targetOneHoleExternalArithmetic_internal`

として repo 内から無条件に構成できるようになった。

一方、A2 の既存 API には歴史的理由で

`(A1 : TargetOneHoleExternalArithmetic)`

という引数が残っている。このファイルでは既存 theorem を壊さず、
その引数へ canonical internal witness を自動挿入する derived theorem をまとめる。

設計方針は次の通り。

* 下位の旧 theorem は互換性のためそのまま残す。
* 新しい A2 の実利用経路では A1 package を要求しない。
* A2 側で本当に外部に残る入力だけを theorem signature に露出させる。
* `A2ExternalCore` では source-even と target analytic bound も branch package から剥がす。

これにより、旧 final package と新 core package の双方から
`AtMostTwoHoleDepthBound` / `smallHoleLowerBound` へ到達できる。
-/

namespace Collatz3
namespace Mersenne

/-! ## source / split / target 深部 closure の internal-A1 版 -/

/--
split-two 深部 closure の A1-free wrapper。

`a=1,n=2` の target-one peel で必要だった A1 package は、
完全内部化済みの canonical witness を自動で使う。
-/
theorem SplitTwoHoleEquation.largeDepth_impossible_internalA1
    (K : TwoHoleKnownArithmetic)
    (R : SplitTwoRegularResidualArithmetic)
    {k n r L a b : ℕ}
    (hk7 : 7 ≤ k)
    (ha0 : 0 < a)
    (han : a < n)
    (hr : 0 < r)
    (hb0 : 0 < b)
    (hbL : b < L)
    (hEq : SplitTwoHoleEquation k n r L a b) :
    False := by
  exact hEq.largeDepth_impossible_of_known_and_residual
    targetOneHoleExternalArithmetic_internal
    K R hk7 ha0 han hr hb0 hbL

/--
target-two 深部 closure の A1-free wrapper。

top target hole を target-one へ peel する branch でも、
旧 A1 引数を呼び出し側へ露出させない。
-/
theorem TargetTwoHoleEquation.largeDepth_impossible_internalA1
    (R : TargetTwoResidualArithmetic)
    {k n r L a b : ℕ}
    (hk7 : 7 ≤ k)
    (hn : 0 < n)
    (hr : 0 < r)
    (ha0 : 0 < a)
    (hab : a < b)
    (hbL : b < L)
    (hEq : TargetTwoHoleEquation k n r L a b) :
    False := by
  exact hEq.largeDepth_impossible_of_residual
    targetOneHoleExternalArithmetic_internal
    R hk7 hn hr ha0 hab hbL

/-! ## 従来 A2 package 再構成の internal-A1 版 -/

/--
分解済み A2 入力から `TwoHoleFullExternalArithmetic` を構成する A1-free 版。

外部入力として残るのは `K` と `R` だけで、A1 は内部 witness を使う。
-/
theorem twoHoleFullExternalArithmetic_of_decomposed_internalA1
    (K : TwoHoleKnownArithmetic)
    (R : TwoHoleResidualArithmetic) :
    TwoHoleFullExternalArithmetic := by
  exact twoHoleFullExternalArithmetic_of_decomposed
    targetOneHoleExternalArithmetic_internal K R

/-- 分解済み A2 入力から `AtMostTwoHoleDepthBound` を得る A1-free 版。 -/
theorem atMostTwoHoleDepthBound_of_decomposed_internalA1
    (K : TwoHoleKnownArithmetic)
    (R : TwoHoleResidualArithmetic) :
    AtMostTwoHoleDepthBound := by
  exact atMostTwoHoleDepthBound_of_decomposed_external
    targetOneHoleExternalArithmetic_internal K R

/-- 分解済み A2 入力から small-hole lower bound へ進む A1-free 版。 -/
theorem blockSparsePow3LowerBound_smallHole_of_decomposed_internalA1
    (K : TwoHoleKnownArithmetic)
    (R : TwoHoleResidualArithmetic) :
    BlockSparsePow3LowerBound smallHoleLowerBound := by
  exact blockSparsePow3LowerBound_smallHole_of_decomposed_external
    targetOneHoleExternalArithmetic_internal K R

/--
finite certificate 内部化後の縮約入力から A2 package を構成する A1-free 版。

現在の研究経路ではこちらが主に使う形になる。
-/
theorem twoHoleFullExternalArithmetic_of_reduced_internalA1
    (K : TwoHoleDeepKnownArithmetic)
    (R : TwoHoleResidualArithmeticReduced) :
    TwoHoleFullExternalArithmetic := by
  exact twoHoleFullExternalArithmetic_of_reduced
    targetOneHoleExternalArithmetic_internal K R

/-- 縮約済み A2 入力から `AtMostTwoHoleDepthBound` を得る A1-free 版。 -/
theorem atMostTwoHoleDepthBound_of_reduced_internalA1
    (K : TwoHoleDeepKnownArithmetic)
    (R : TwoHoleResidualArithmeticReduced) :
    AtMostTwoHoleDepthBound := by
  exact atMostTwoHoleDepthBound_of_reduced_external
    targetOneHoleExternalArithmetic_internal K R

/-- 縮約済み A2 入力から small-hole lower bound へ進む A1-free 版。 -/
theorem blockSparsePow3LowerBound_smallHole_of_reduced_internalA1
    (K : TwoHoleDeepKnownArithmetic)
    (R : TwoHoleResidualArithmeticReduced) :
    BlockSparsePow3LowerBound smallHoleLowerBound := by
  exact blockSparsePow3LowerBound_smallHole_of_reduced_external
    targetOneHoleExternalArithmetic_internal K R

/-! ## generic full-A2 package に対する A1-free closure -/

/--
`TwoHoleFullExternalArithmetic` が与えられれば、A1 package を別途渡さず
`AtMostTwoHoleDepthBound` を得られる。
-/
theorem atMostTwoHoleDepthBound_internalA1
    (A2 : TwoHoleFullExternalArithmetic) :
    AtMostTwoHoleDepthBound := by
  exact atMostTwoHoleDepthBound_of_external
    targetOneHoleExternalArithmetic_internal A2

/-- generic full-A2 package から small-hole lower bound へ進む A1-free 版。 -/
theorem blockSparsePow3LowerBound_smallHole_internalA1
    (A2 : TwoHoleFullExternalArithmetic) :
    BlockSparsePow3LowerBound smallHoleLowerBound := by
  exact blockSparsePow3LowerBound_smallHole_of_external
    targetOneHoleExternalArithmetic_internal A2

/-! ## final A2 package の主経路 -/

/--
最終 A2 算術 package から従来の full-six-term package を再構成する。

旧 theorem `twoHoleFullExternalArithmetic_of_A1_finalA2` から
A1 引数を消した主利用版。
-/
theorem twoHoleFullExternalArithmetic_of_finalA2
    (A2 : TwoHoleFinalExternalArithmetic) :
    TwoHoleFullExternalArithmetic := by
  exact twoHoleFullExternalArithmetic_of_A1_finalA2
    targetOneHoleExternalArithmetic_internal A2

/--
最終 A2 算術 package だけから `AtMostTwoHoleDepthBound` を得る。

A1 は完全内部化済みなので theorem signature に現れない。
-/
theorem atMostTwoHoleDepthBound_of_finalA2
    (A2 : TwoHoleFinalExternalArithmetic) :
    AtMostTwoHoleDepthBound := by
  exact atMostTwoHoleDepthBound_of_A1_finalA2
    targetOneHoleExternalArithmetic_internal A2

/--
最終 A2 算術 package だけから concrete small-hole lower bound へ接続する。

現時点で A2 最終 interface から complexity 側へ進む最短の公開 theorem。
-/
theorem blockSparsePow3LowerBound_smallHole_of_finalA2
    (A2 : TwoHoleFinalExternalArithmetic) :
    BlockSparsePow3LowerBound smallHoleLowerBound := by
  exact blockSparsePow3LowerBound_smallHole_of_A1_finalA2
    targetOneHoleExternalArithmetic_internal A2

end Mersenne
end Collatz3
