import CollatzLean.Collatz3.Mersenne.TargetOneHoleFourBranchClosure
import CollatzLean.Collatz3.Mersenne.OneHoleSourceResidualProof


/-!
# Collatz3 Mersenne: external target-one closure から AtMostOneHoleDepthBound へ

hole 0 は既存 no-hole 完全分類、source-one は既存 elementary proof、
target-one だけを `TargetOneHoleExternalArithmetic` から閉じる。

従って外部入力の依存範囲は target-one の最後の四枝に限定される。
-/

namespace Collatz3
namespace Mersenne

/--
外部 target-one arithmetic package から `AtMostOneHoleDepthBound` を得る。
-/
theorem atMostOneHoleDepthBound_of_external
    (A : TargetOneHoleExternalArithmetic) :
    AtMostOneHoleDepthBound := by
  intro k sourceLength r targetLength sourceTail targetBits hEq hAtMost
  rcases atMostOneHole_cases hAtMost with hZero | hOne
  · have hNoHole := noHole_normalForm hEq hZero
    have hkTwo :=
      NoHoleCompleteClassification.depth_le_two
        noHoleCompleteClassification
        hEq.depth_pos
        hEq.sourceLength_pos
        hEq.exitDepth_pos
        hEq.targetLength_pos
        hNoHole
    omega
  · rcases oneHole_normalForm hEq hOne with hSource | hTarget
    · rcases hSource with ⟨a, ha0, han, hSourceEq⟩
      exact
        hSourceEq.depth_le_five
          ha0 han hEq.exitDepth_pos hEq.targetLength_pos
    · rcases hTarget with ⟨b, hb0, hbL, hTargetEq⟩
      exact
        hTargetEq.depth_le_five_of_external
          A hEq.sourceLength_pos hEq.exitDepth_pos hb0 hbL

end Mersenne
end Collatz3
