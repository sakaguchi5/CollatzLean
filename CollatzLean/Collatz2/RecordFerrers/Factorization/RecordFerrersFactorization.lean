import CollatzLean.Collatz2.RecordFerrers.Deformation.BlockPermutation
import CollatzLean.Collatz2.Core.BlockAffineFactorization

/-!
# Record–Ferrers Phase A: skeleton / decoration factorization

record skeleton と local minimal decorations を分離し、odd length / two-depth / affine
translation の global data を exact に再構成する。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-- minimal block length list が要求する total local two-depth。 -/
def localMinimalDepthSum (rs : List ℕ) : ℕ :=
  (rs.map minimalDepth).sum

/-- carry-compatible skeleton では local minimal depths が global critical depth に telescope する。 -/
theorem criticalHeight_add_localMinimalDepthSum
    (start : ℕ)
    (rs : List ℕ)
    (hCarry : Skeleton.carryConditionFrom start rs) :
    criticalHeight start + localMinimalDepthSum rs =
      criticalHeight (start + rs.sum) + 1 := by
  induction rs generalizing start with
  | nil =>
      simp [Skeleton.carryConditionFrom] at hCarry
  | cons r rs ih =>
      cases rs with
      | nil =>
          change criticalCarry start r = 0 at hCarry
          have hCrit := criticalHeight_add_eq start r
          rw [hCarry] at hCrit
          simp [localMinimalDepthSum, minimalDepth]
          omega
      | cons s ss =>
          change
            criticalCarry start r = 1 ∧
              Skeleton.carryConditionFrom (start + r) (s :: ss) at hCarry
          have hTail := ih (start + r) hCarry.2
          have hCrit := criticalHeight_add_eq start r
          rw [hCarry.1] at hCrit
          simp only [
            localMinimalDepthSum,
            List.map_cons,
            List.sum_cons
          ] at hTail ⊢
          unfold minimalDepth at hTail ⊢
          simp only [Nat.add_assoc] at hTail hCrit ⊢
          omega

namespace DecoratedSkeleton

/-- decoration を concatenate した word。 -/
def assembledWord
    {S : Skeleton}
    (D : DecoratedSkeleton S) : Word :=
  D.blocks.flatten

/-- assembled word の odd-step 数は skeleton total length。 -/
theorem assembledWord_oddSteps
    {S : Skeleton}
    (D : DecoratedSkeleton S) :
    oddSteps D.assembledWord = S.totalLength := by
  unfold assembledWord
  rw [oddSteps_flatten_blocks]
  unfold blockOddSteps Skeleton.totalLength
  rw [D.lengths_eq]

/-- minimal block list の two-depth sum は length profile の minimalDepth sum。 -/
private theorem twoSteps_sum_eq_minimalDepth_sum
    (bs : List Word)
    (hMinimal : ∀ b ∈ bs, MinimalBlock b) :
    (bs.map twoSteps).sum =
      (bs.map (fun b => minimalDepth (oddSteps b))).sum := by
  revert hMinimal
  induction bs with
  | nil =>
      intro _
      simp
  | cons b bs ih =>
      intro hMinimal
      have hb : MinimalBlock b := hMinimal b (by simp)
      have hTail : ∀ c ∈ bs, MinimalBlock c := by
        intro c hc
        exact hMinimal c (by simp [hc])
      have hTwo : twoSteps b = minimalDepth (oddSteps b) := by
        unfold minimalDepth
        exact hb.minimalDepth
      have hIH := ih hTail
      simp [hTwo, hIH]

/-- minimal decorations の blockwise depth sum は skeleton の local minimal depth sum。 -/
theorem blockDepthSum_eq_localMinimalDepthSum
    {S : Skeleton}
    (D : DecoratedSkeleton S) :
    (D.blocks.map twoSteps).sum = localMinimalDepthSum S.lengths := by
  have hSum := twoSteps_sum_eq_minimalDepth_sum D.blocks D.minimal
  have hMap :
      D.blocks.map (fun b => minimalDepth (oddSteps b)) =
        S.lengths.map minimalDepth := by
    calc
      D.blocks.map (fun b => minimalDepth (oddSteps b))
          = (D.blocks.map oddSteps).map minimalDepth := by
              simp [List.map_map]
      _ = S.lengths.map minimalDepth := by rw [D.lengths_eq]
  rw [hSum, hMap]
  rfl

/-- assembled word の total two-depth は skeleton local minimal depth sum。 -/
theorem assembledWord_twoSteps
    {S : Skeleton}
    (D : DecoratedSkeleton S) :
    twoSteps D.assembledWord = localMinimalDepthSum S.lengths := by
  unfold assembledWord
  rw [twoSteps_flatten_blocks]
  unfold blockTwoSteps
  exact D.blockDepthSum_eq_localMinimalDepthSum

/-- all-valid block list の flatten は valid。 -/
private theorem valid_flatten_of_all
    (bs : List Word)
    (hValid : ∀ b ∈ bs, Valid b) :
    Valid bs.flatten := by
  revert hValid
  induction bs with
  | nil =>
      intro _
      simp [Valid]
  | cons b bs ih =>
      intro hValid
      have hb : Valid b := hValid b (by simp)
      have hTail : ∀ c ∈ bs, Valid c := by
        intro c hc
        exact hValid c (by simp [hc])
      have hTailValid := ih hTail
      simpa only [List.flatten_cons] using hb.append hTailValid

/-- valid decoration の assembled word は valid。 -/
theorem assembledWord_valid
    {S : Skeleton}
    (D : ValidDecoratedSkeleton S) :
    Valid D.toDecoratedSkeleton.assembledWord := by
  exact valid_flatten_of_all D.blocks D.valid

/-- assembled translation は core block composition の weighted translation そのもの。 -/
theorem assembledWord_affineConst
    {S : Skeleton}
    (D : DecoratedSkeleton S) :
    affineConst D.assembledWord = weightedBlockTranslation D.blocks := by
  unfold assembledWord
  exact (weightedBlockTranslation_eq_affineConst_flatten D.blocks).symm

end DecoratedSkeleton

/--
record decomposition の forward factorization packet。
skeleton、local decorations、suffix reconstruction、full carry を一つに束ねる。
-/
structure RecordFactorization
    {p H : ℕ}
    (x : FiberPoint p H)
    (start : ℕ) where
  skeleton : Skeleton
  decoration : DecoratedSkeleton skeleton
  suffix_eq : decoration.assembledWord = x.word.drop start
  carry : Skeleton.carryConditionFrom start skeleton.lengths

namespace RecordDecomposition

/-- genuine decomposition を exact Record–Ferrers factorization packet へ送る。 -/
def toRecordFactorization
    {p H : ℕ}
    {x : FiberPoint p H}
    {start : ℕ}
    (D : RecordDecomposition x start) :
    RecordFactorization x start := by
  let S := Skeleton.ofDecomposition D
  let E : DecoratedSkeleton S := D.toDecoratedSkeleton
  exact {
    skeleton := S
    decoration := E
    suffix_eq := by
      change D.toDecoratedSkeleton.blocks.flatten = x.word.drop start
      exact D.decorated_flatten_eq_drop
    carry := by
      simpa [S] using Skeleton.carryCondition_of_decomposition D
  }

/-- forward factorization は元 decomposition の length skeleton をそのまま保持する。 -/
@[simp] theorem toRecordFactorization_lengths
    {p H : ℕ}
    {x : FiberPoint p H}
    {start : ℕ}
    (D : RecordDecomposition x start) :
    D.toRecordFactorization.skeleton.lengths = D.lengths := by
  simp [toRecordFactorization, Skeleton.ofDecomposition]

end RecordDecomposition

/-- anchor と decorated skeleton を concatenate する。 -/
def assembleWithAnchor
    {S : Skeleton}
    (anchor : Word)
    (D : DecoratedSkeleton S) : Word :=
  anchor ++ D.assembledWord

/-- carry-compatible skeleton は roof anchor を global minimal terminal depth へ送る。 -/
theorem twoSteps_assembleWithAnchor_eq_criticalHeight_add_one
    {S : Skeleton}
    (anchor : Word)
    (D : DecoratedSkeleton S)
    (hAnchorRoof : twoSteps anchor = criticalHeight (oddSteps anchor))
    (hCarry : Skeleton.carryConditionFrom (oddSteps anchor) S.lengths) :
    twoSteps (assembleWithAnchor anchor D) =
      criticalHeight (oddSteps (assembleWithAnchor anchor D)) + 1 := by
  have hLocal := D.assembledWord_twoSteps
  have hOdd := D.assembledWord_oddSteps
  have hTelescope :=
    criticalHeight_add_localMinimalDepthSum
      (oddSteps anchor) S.lengths hCarry
  unfold assembleWithAnchor
  rw [twoSteps_append, oddSteps_append, hAnchorRoof, hLocal, hOdd]
  exact hTelescope


end RecordFerrers
end Collatz2
