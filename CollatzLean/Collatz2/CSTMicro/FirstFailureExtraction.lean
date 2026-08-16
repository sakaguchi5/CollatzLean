import CollatzLean.Collatz2.CSTMicro.FirstPassagePreservation

/-!
# General CST: first failure extraction on a Ferrers chain

pure separation を word 単体へ戻し、Ferrers chain 上で
safe から failure へ初めて移る adjacent edge を抽出する。

no-carry edge は

  B_upper <= B_lower
  R_lower <= R_upper

なので separation を壊せない。
したがって最初の failure edge は必ず carry を持つ。
-/

namespace Collatz2
namespace CSTMicro

/-- word 単体の terminal coefficient gap。 -/
def wordTerminalGap (v : ParityWord) : ℕ :=
  2 ^ v.length - 3 ^ oddCount v

/-- word 単体の pure separation。 -/
def WordPureSeparation (v : ParityWord) : Prop :=
  affineConst v < wordTerminalGap v * leastRepresentative v

namespace MicroObject

/-- MicroObject の separation は underlying word の separation と同じ。 -/
theorem pureSeparation_iff_wordPureSeparation
    (M : MicroObject) :
    M.PureSeparation ↔ WordPureSeparation M.path.word := by
  rfl

/-- CST failure は underlying word の separation failure を与える。 -/
theorem wordPureSeparation_failure_of_cst_failure
    (M : MicroObject)
    (hFail : ¬ M.CSTHolds) :
    ¬ WordPureSeparation M.path.word := by
  intro hWord
  apply hFail
  apply (M.cstHolds_iff_pureSeparation).2
  exact (M.pureSeparation_iff_wordPureSeparation).2 hWord

end MicroObject

namespace FerrersStep

/-- adjacent cover の lower/upper terminal gap は同じ。 -/
theorem wordTerminalGap_eq
    {lower upper : ParityWord}
    (S : FerrersStep lower upper) :
    wordTerminalGap lower = wordTerminalGap upper := by
  unfold wordTerminalGap
  rw [S.length_eq, S.oddCount_eq]

/-- no-carry edge は word-level pure separation を保存する。 -/
theorem wordPureSeparation_preserved_of_noCarry
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hNoCarry : S.edge.NoCarry)
    (hLower : WordPureSeparation lower) :
    WordPureSeparation upper := by
  unfold WordPureSeparation at hLower ⊢
  have hB : affineConst upper ≤ affineConst lower := by
    calc
      affineConst upper = affineConst S.edge.upperWord :=
        congrArg affineConst S.upper_eq
      _ ≤ affineConst S.edge.lowerWord :=
        S.edge.upper_affineConst_le_lower
      _ = affineConst lower :=
        (congrArg affineConst S.lower_eq).symm
  have hR :
      leastRepresentative lower ≤ leastRepresentative upper := by
    calc
      leastRepresentative lower =
          leastRepresentative S.edge.lowerWord :=
        congrArg leastRepresentative S.lower_eq
      _ ≤ leastRepresentative S.edge.upperWord := by
        simpa [
          AdjacentFerrersSwap.lowerR,
          AdjacentFerrersSwap.upperR
        ] using
          S.edge.lowerR_le_upperR_of_noCarry hNoCarry
      _ = leastRepresentative upper :=
        (congrArg leastRepresentative S.upper_eq).symm
  have hG : wordTerminalGap lower = wordTerminalGap upper :=
    S.wordTerminalGap_eq
  have hGR :
      wordTerminalGap lower * leastRepresentative lower ≤
        wordTerminalGap upper * leastRepresentative upper := by
    rw [← hG]
    exact Nat.mul_le_mul_left (wordTerminalGap lower) hR
  exact lt_of_le_of_lt hB (lt_of_lt_of_le hLower hGR)

end FerrersStep

/-- safe -> failure の最初の adjacent edge packet。 -/
structure FirstFailureEdge where
  lower : ParityWord
  upper : ParityWord
  step : FerrersStep lower upper
  lower_firstPassage : IsFirstPassageWord lower
  upper_firstPassage : IsFirstPassageWord upper
  lower_safe : WordPureSeparation lower
  upper_failure : ¬ WordPureSeparation upper

namespace FirstFailureEdge

/-- first failure edge は必ず carry。 -/
theorem hasCarry (F : FirstFailureEdge) :
    F.step.edge.HasCarry := by
  rcases F.step.edge.noCarry_or_hasCarry with hNo | hCarry
  · have hSafeUpper :=
      F.step.wordPureSeparation_preserved_of_noCarry hNo F.lower_safe
    exact False.elim (F.upper_failure hSafeUpper)
  · exact hCarry

end FirstFailureEdge

namespace FerrersChain

/--
safe start から failure finish へ至る有限 chain には
safe -> failure の adjacent edge が存在する。
-/
theorem exists_firstFailureEdge
    {start finish : ParityWord}
    (C : FerrersChain start finish)
    (hStartFP : IsFirstPassageWord start)
    (hStartSafe : WordPureSeparation start)
    (hFinishFail : ¬ WordPureSeparation finish) :
    Nonempty FirstFailureEdge := by
  revert hStartFP hStartSafe hFinishFail
  induction C with
  | refl =>
      intro _hStartFP hStartSafe hFinishFail
      exact False.elim (hFinishFail hStartSafe)
  | @step u v C S ih =>
      intro hStartFP hStartSafe hFinishFail
      have hUFP : IsFirstPassageWord u :=
        C.preserves_firstPassage hStartFP
      have hVFP : IsFirstPassageWord v :=
        S.preserves_firstPassage hUFP
      by_cases hUSafe : WordPureSeparation u
      · exact ⟨{
          lower := u
          upper := v
          step := S
          lower_firstPassage := hUFP
          upper_firstPassage := hVFP
          lower_safe := hUSafe
          upper_failure := hFinishFail
        }⟩
      · exact ih hStartFP hStartSafe hUSafe

end FerrersChain

/--
全 Ferrers boundary が safe なら、任意の bad first-passage word から
first failure edge を抽出できる。
-/
theorem exists_firstFailureEdge_from_bad_word
    {target : ParityWord}
    (hTargetFP : IsFirstPassageWord target)
    (hTargetFail : ¬ WordPureSeparation target)
    (hBoundarySafe :
      ∀ boundary : ParityWord,
        IsFerrersBoundary boundary → WordPureSeparation boundary) :
    Nonempty FirstFailureEdge := by
  rcases exists_ferrersBoundary_chain hTargetFP with
    ⟨boundary, hBoundary, ⟨C⟩⟩
  have hSafe := hBoundarySafe boundary hBoundary
  exact C.exists_firstFailureEdge hBoundary.1 hSafe hTargetFail

/--
MicroObject の CST failure から first failure edge を抽出する global bridge。
boundary safety だけを残りの base theorem として明示する。
-/
theorem exists_firstFailureEdge_of_cst_failure
    (M : MicroObject)
    (hFail : ¬ M.CSTHolds)
    (hBoundarySafe :
      ∀ boundary : ParityWord,
        IsFerrersBoundary boundary → WordPureSeparation boundary) :
    Nonempty FirstFailureEdge := by
  exact exists_firstFailureEdge_from_bad_word
    M.path.isFirstPassageWord
    (M.wordPureSeparation_failure_of_cst_failure hFail)
    hBoundarySafe

end CSTMicro
end Collatz2
