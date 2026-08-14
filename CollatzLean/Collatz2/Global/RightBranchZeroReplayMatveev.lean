import CollatzLean.Collatz2.Global.RightBranchZeroReplay
import CollatzLean.Collatz2.External.MatveevInput

/-!
# Collatz2: Matveev external input を right-branch q=0 reduction に適用する

`RightBranchZeroReplay` は条件付きで axiom-free に保つ。
このファイルだけが `External.matveev_twoThreeSmallGap` を具体的に差し込む。

将来 Matveev を Lean 化したときは `External/MatveevInput.lean` の axiom を theorem に
置き換えればよく、このファイル以下の Collatz proof は変更しない。
-/

namespace Collatz2
namespace Word
namespace FirstCrossing

/-- Matveev external input の下で positive actual FirstCrossing の replay quotient は0。 -/
theorem replayQuotient_eq_zero_of_matveevInput
    {w : Word} {X Y : ℕ}
    (hF : FirstCrossing w)
    (hrun : Runs w X Y)
    (hXY : X < Y) :
    (ReplayCoordinate.ofRuns hrun hF.nonempty).quotient = 0 := by
  exact
    hF.replayQuotient_eq_zero_of_twoThreeSmallGapExclusion
      External.matveev_twoThreeSmallGap hrun hXY

/-- Matveev external input の下で actual positive FirstCrossing は canonical-positive。 -/
theorem canonical_positive_of_matveevInput
    {w : Word} {X Y : ℕ}
    (hF : FirstCrossing w)
    (hrun : Runs w X Y)
    (hXY : X < Y) :
    canonicalStart w < canonicalEnd w := by
  exact
    hF.canonical_positive_of_twoThreeSmallGapExclusion
      External.matveev_twoThreeSmallGap hrun hXY

end FirstCrossing
end Word

/--
Matveev external input を差し込んだ right-branch q=0 reduction。
右枝は canonical positive FirstCrossing まで正式に圧縮される。
-/
theorem hasUnboundedOddOrbit_to_foreverExpanding_or_canonicalPositiveFirstCrossing_of_matveevInput :
    HasUnboundedOddOrbit →
      ∃ O : OddOrbit,
        O.Unbounded ∧
          (
            Word.NestedSurvivalChain.ForeverExpanding
              O.toNestedSurvivalChain
            ∨
            ∃ w : Word,
              Word.Valid w ∧
                Word.FirstCrossing w ∧
                Runs w (Word.canonicalStart w) (Word.canonicalEnd w) ∧
                O.globalMinimumValue = Word.canonicalStart w ∧
                Word.canonicalStart w < Word.canonicalEnd w
          ) := by
  exact
    hasUnboundedOddOrbit_to_foreverExpanding_or_canonicalPositiveFirstCrossing
      External.matveev_twoThreeSmallGap

end Collatz2
