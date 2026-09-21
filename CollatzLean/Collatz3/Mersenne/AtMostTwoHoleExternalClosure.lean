import CollatzLean.Collatz3.Mersenne.AtMostOneHoleExternalClosure
import CollatzLean.Collatz3.Mersenne.TwoHoleFullExternalArithmetic

/-!
# Collatz3 Mersenne: external full-six-term closure から AtMostTwoHoleDepthBound へ

hole ≤ 1 は既存 `TargetOneHoleExternalArithmetic` package を再利用する。
hole = 2 は exact normal form で source / split / target の三配置へ分け、
各配置を `TwoHoleFullExternalArithmetic` で `k≤6` へ閉じる。

外部依存は

* one-hole target の既存 package、
* genuinely full six-term two-hole arithmetic、

の二箇所だけに局所化される。
-/

namespace Collatz3
namespace Mersenne

/--
既存 one-hole external package と full-six-term two-hole package から、
`AtMostTwoHoleDepthBound` を得る。
-/
theorem atMostTwoHoleDepthBound_of_external
    (A1 : TargetOneHoleExternalArithmetic)
    (A2 : TwoHoleFullExternalArithmetic) :
    AtMostTwoHoleDepthBound := by
  intro k sourceLength r targetLength sourceTail targetBits hEq hAtMost
  by_cases hAtMostOne :
      Binary.oneCount sourceTail + Binary.oneCount targetBits ≤ 1
  · have hkFive :=
      atMostOneHoleDepthBound_of_external A1
        k sourceLength r targetLength sourceTail targetBits hEq hAtMostOne
    omega
  · have hTwo :
        Binary.oneCount sourceTail + Binary.oneCount targetBits = 2 := by
      omega
    rcases twoHole_normalForm hEq hTwo with hSource | hSplit | hTarget
    · rcases hSource with ⟨a, b, ha0, hab, hbn, hSourceEq⟩
      exact hSourceEq.depth_le_six_of_full_external
        A2 ha0 hab hbn hEq.exitDepth_pos hEq.targetLength_pos
    · rcases hSplit with ⟨a, b, ha0, han, hb0, hbL, hSplitEq⟩
      exact hSplitEq.depth_le_six_of_full_external
        A2 ha0 han hEq.exitDepth_pos hb0 hbL
    · rcases hTarget with ⟨a, b, ha0, hab, hbL, hTargetEq⟩
      exact hTargetEq.depth_le_six_of_full_external
        A2 hEq.sourceLength_pos hEq.exitDepth_pos ha0 hab hbL

/--
外部 closure を small-hole complexity lower bound へ直接接続する。
-/
theorem blockSparsePow3LowerBound_smallHole_of_external
    (A1 : TargetOneHoleExternalArithmetic)
    (A2 : TwoHoleFullExternalArithmetic) :
    BlockSparsePow3LowerBound smallHoleLowerBound := by
  exact blockSparsePow3LowerBound_smallHole
    noHoleCompleteClassification
    (atMostOneHoleDepthBound_of_external A1)
    (atMostTwoHoleDepthBound_of_external A1 A2)

end Mersenne
end Collatz3
