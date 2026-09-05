import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleVisibleDefectDecoder68
import CollatzLean.Collatz2.CSTMicro.DoubleDecomposition.IndependentCriticalDefectInverse


/-!
# 第3例探索 7: decoder と IndependentCriticalDefectProfile の接続

`IndependentCriticalDefectProfile` は exponent word を保持せず

  height k,
  defect k

から valid minimal FirstCrossing word を逆構成する既存 object である。
visible decoder の entry `(index,height)` が independent profile の同じ index の height と
一致すれば、defect depth も自動的に一致する。

このファイルは executable decoder と既存 inverse-construction theorem の境界を固定する。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

open DoubleDecomposition
open FerrersDeficit

/-- 一つの decoder entry が independent profile と一致する条件。 -/
def VisibleDefectCompatible
    {p : ℕ}
    (D : IndependentCriticalDefectProfile p)
    (E : VisibleDefect) : Prop :=
  E.index < p ∧ E.height = D.height E.index

/-- entry の height が一致すれば、decoder depth は profile defect と exact に一致する。 -/
theorem visibleDefect_depth_eq_independentProfile
    {p : ℕ}
    (D : IndependentCriticalDefectProfile p)
    (E : VisibleDefect)
    (h : VisibleDefectCompatible D E) :
    E.depth = D.defect E.index := by
  rcases h with ⟨hIndex, hHeight⟩
  have hEq := D.height_eq_roof_sub_defect E.index hIndex
  have hLe := D.defect_le_roof E.index hIndex
  unfold VisibleDefect.depth
  rw [hHeight, hEq]
  omega

/-- decoder list 全体が independent profile と一致する条件。 -/
def VisibleDecoderCompatible
    {p : ℕ}
    (D : IndependentCriticalDefectProfile p)
    (entries : List VisibleDefect) : Prop :=
  ∀ E : VisibleDefect, E ∈ entries → VisibleDefectCompatible D E

/-- compatible な decoder list の各 depth は independent profile defect と一致する。 -/
theorem visibleDecoderCompatible_depths
    {p : ℕ}
    (D : IndependentCriticalDefectProfile p)
    (entries : List VisibleDefect)
    (hCompat : VisibleDecoderCompatible D entries) :
    ∀ E : VisibleDefect, E ∈ entries → E.depth = D.defect E.index := by
  intro E hE
  exact visibleDefect_depth_eq_independentProfile D E (hCompat E hE)

/--
真の exact target candidate から、既存の independent defect profile を直接構成する。
-/
def thirdExampleIndependentProfileOfExactCandidate
    {w : Word}
    {deficit gap m : ℕ}
    (C : ExactCriticalGapOneFerrersCertificate
      w thirdExampleTargetP thirdExampleTargetH deficit gap m) :
    IndependentCriticalDefectProfile thirdExampleTargetP := by
  have hTerminal :
      Word.twoSteps w =
        Word.criticalHeight (Word.oddSteps w) + 1 := by
    calc
      Word.twoSteps w = thirdExampleTargetH := C.twoSteps_eq
      _ = Word.criticalHeight thirdExampleTargetP + 1 :=
        C.terminalDepth_eq_criticalHeight_succ
      _ = Word.criticalHeight (Word.oddSteps w) + 1 := by
        rw [C.oddSteps_eq]
  let D := independentCriticalDefectProfileOfWord C.minimal hTerminal
  simpa [C.oddSteps_eq] using D

/--
68 decoder の出力が上の independent profile と compatible である、という
後段 soundness が満たすべき最小 predicate。
-/
def ThirdExampleDecoder68MatchesExactCandidate
    {w : Word}
    {deficit gap m : ℕ}
    (C : ExactCriticalGapOneFerrersCertificate
      w thirdExampleTargetP thirdExampleTargetH deficit gap m) : Prop :=
  VisibleDecoderCompatible
    (thirdExampleIndependentProfileOfExactCandidate C)
    (thirdExampleVisibleDefectDecoder68
      (deficit : ZMod thirdExampleLeftModulus))

/-- 上の predicate があれば、decoder entry depth は actual independent profile と一致する。 -/
theorem thirdExampleDecoder68_depths_match_exactCandidate
    {w : Word}
    {deficit gap m : ℕ}
    (C : ExactCriticalGapOneFerrersCertificate
      w thirdExampleTargetP thirdExampleTargetH deficit gap m)
    (hMatch : ThirdExampleDecoder68MatchesExactCandidate C) :
    ∀ E : VisibleDefect,
      E ∈ thirdExampleVisibleDefectDecoder68
          (deficit : ZMod thirdExampleLeftModulus) →
      E.depth = (thirdExampleIndependentProfileOfExactCandidate C).defect E.index := by
  exact visibleDecoderCompatible_depths
    (thirdExampleIndependentProfileOfExactCandidate C)
    (thirdExampleVisibleDefectDecoder68
      (deficit : ZMod thirdExampleLeftModulus))
    hMatch

end ThirdExampleSearch
end CSTMicro
end Collatz2
