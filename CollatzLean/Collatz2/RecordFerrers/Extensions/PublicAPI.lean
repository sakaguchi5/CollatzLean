import CollatzLean.Collatz2.RecordFerrers.Reconstruction.InformationBoundary
import CollatzLean.Collatz2.RecordFerrers.Factorization.PrimitiveReducedInverse

/-!
# Record–Ferrers RF-A+1: public API extraction

Phase A 本体の長い証明や private 補題の中に埋もれていた、後段で再利用価値の高い
一般補題を public API として独立させる。

既存 proof は変更せず、add-only で同値の public theorem を与える。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-- critical roof 以下の positive prefix は expanding。 -/
theorem expanding_take_of_depth_le_criticalHeight_public
    (w : Word)
    {k : ℕ}
    (hkPos : 0 < k)
    (hkLe : k ≤ oddSteps w)
    (hDepth : prefixTwoDepth w k ≤ criticalHeight k) :
    Expanding (w.take k) := by
  have hPowLe :
      2 ^ prefixTwoDepth w k ≤ 2 ^ criticalHeight k :=
    Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hDepth
  have hCrit := criticalHeight_pow_lt_threePow hkPos
  have hPow : 2 ^ prefixTwoDepth w k < 3 ^ k :=
    lt_of_le_of_lt hPowLe hCrit
  have hTakeLen : (w.take k).length = k := by
    apply List.length_take_of_le
    simpa [oddSteps] using hkLe
  apply (expanding_iff_twoPow_lt_threePow).2
  simpa [prefixTwoDepth, oddSteps, hTakeLen] using hPow

/-- FirstCrossing の proper cut では signed critical clearance は nonnegative。 -/
theorem criticalDefectInt_nonneg_of_firstCrossing
    {p H : ℕ}
    {x : FiberPoint p H}
    (hF : FirstCrossing x.word)
    {k : ℕ}
    (hkPos : 0 < k)
    (hkLt : k < p) :
    0 ≤ criticalDefectInt x k := by
  have hkWord : k < oddSteps x.word := by
    rw [x.oddSteps_eq]
    exact hkLt
  have hDepthRaw := hF.prefixTwoDepth_le_criticalHeight hkPos hkWord
  have hDepth : x.height k ≤ criticalHeight k := by
    simpa [FiberPoint.height] using hDepthRaw
  have hDepthZ :
      (x.height k : ℤ) ≤ (criticalHeight k : ℤ) := by
    exact_mod_cast hDepth
  unfold criticalDefectInt
  exact sub_nonneg.mpr hDepthZ

namespace FiberPoint

/-- prefix height と suffix two-depth の exact split。 -/
theorem height_add_drop_twoSteps_eq_terminal
    {p H : ℕ}
    (x : FiberPoint p H)
    (k : ℕ) :
    x.height k + twoSteps (x.word.drop k) = H := by
  have hSplit :
      twoSteps x.word =
        prefixTwoDepth x.word k + twoSteps (x.word.drop k) := by
    have h := twoSteps_append (x.word.take k) (x.word.drop k)
    rw [List.take_append_drop] at h
    simpa [prefixTwoDepth] using h
  rw [x.twoSteps_eq] at hSplit
  simpa [FiberPoint.height] using hSplit.symm

/-- fixed fiber の suffix odd length は `p-k`。 -/
theorem oddSteps_drop_eq_remaining
    {p H : ℕ}
    (x : FiberPoint p H)
    (k : ℕ) :
    oddSteps (x.word.drop k) = p - k := by
  unfold oddSteps
  rw [List.length_drop]
  have hLen : x.word.length = p := by
    simpa [oddSteps] using x.oddSteps_eq
  rw [hLen]

end FiberPoint

/-- minimal block list の two-depth sum は minimalDepth length sum。 -/
theorem minimalBlocks_twoSteps_sum
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

/-- all-valid block list の flatten は valid。 -/
theorem valid_flatten_of_all_public
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

/-- block list に属する block の odd length は flatten 全体以下。 -/
theorem oddSteps_le_flatten_of_mem_public
    {b : Word}
    {bs : List Word}
    (hb : b ∈ bs) :
    oddSteps b ≤ oddSteps bs.flatten := by
  induction bs with
  | nil =>
      simp at hb
  | cons c cs ih =>
      simp only [List.mem_cons] at hb
      simp only [List.flatten_cons, oddSteps_append]
      rcases hb with hEq | hb
      · subst c
        omega
      · have hLe := ih hb
        omega

namespace Skeleton

theorem eq_of_lengths_eq
    {A B : Skeleton}
    (h : A.lengths = B.lengths) :
    A = B := by
  cases A
  cases B
  simp_all

@[simp] theorem carryConditionFrom_nil (start : ℕ) :
    carryConditionFrom start [] = False := rfl

@[simp] theorem carryConditionFrom_singleton
    (start r : ℕ) :
    carryConditionFrom start [r] ↔ criticalCarry start r = 0 := by
  rfl

@[simp] theorem carryConditionFrom_cons_cons
    (start r s : ℕ)
    (rs : List ℕ) :
    carryConditionFrom start (r :: s :: rs) ↔
      criticalCarry start r = 1 ∧
        carryConditionFrom (start + r) (s :: rs) := by
  rfl

@[simp] theorem interiorCarryConditionFrom_nil (start : ℕ) :
    interiorCarryConditionFrom start [] = False := rfl

@[simp] theorem interiorCarryConditionFrom_singleton
    (start r : ℕ) :
    interiorCarryConditionFrom start [r] := by
  simp [interiorCarryConditionFrom]

@[simp] theorem interiorCarryConditionFrom_cons_cons
    (start r s : ℕ)
    (rs : List ℕ) :
    interiorCarryConditionFrom start (r :: s :: rs) ↔
      criticalCarry start r = 1 ∧
        interiorCarryConditionFrom (start + r) (s :: rs) := by
  rfl

end Skeleton

namespace RecordChain

/-- genuine record chain の各 slice は valid。 -/
theorem blocks_valid_public
    {p H : ℕ}
    {x : FiberPoint p H}
    {start : ℕ}
    {lengths : List ℕ}
    (C : RecordChain x start lengths) :
    ∀ b ∈ C.blocks, Valid b := by
  induction C with
  | last B hTerminal =>
      intro b hb
      simp only [blocks, blockWordsFromLengths, List.mem_singleton] at hb
      subst b
      exact RecordBlock.local_valid
  | cons B hInterior T ih =>
      intro b hb
      simp only [blocks, blockWordsFromLengths, List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact RecordBlock.local_valid
      · exact ih b hb

end RecordChain

namespace RecordDecomposition

/-- decomposition の全 local blocks は valid。 -/
theorem blocks_valid_public
    {p H : ℕ}
    {x : FiberPoint p H}
    {start : ℕ}
    (D : RecordDecomposition x start) :
    ∀ b ∈ D.blocks, Valid b :=
  D.chain.blocks_valid_public

/-- decomposition の全 local blocks は valid minimal blocks。 -/
theorem blocks_validMinimal
    {p H : ℕ}
    {x : FiberPoint p H}
    {start : ℕ}
    (D : RecordDecomposition x start) :
    ∀ b ∈ D.blocks, ValidMinimalBlock b := by
  intro b hb
  exact {
    toMinimalBlock := D.blocks_minimal b hb
    valid := D.blocks_valid_public b hb
  }

/-- genuine decomposition を valid decorated skeleton へ忘却する。 -/
def toValidDecoratedSkeleton
    {p H : ℕ}
    {x : FiberPoint p H}
    {start : ℕ}
    (D : RecordDecomposition x start) :
    ValidDecoratedSkeleton (Skeleton.ofDecomposition D) :=
  { toDecoratedSkeleton := D.toDecoratedSkeleton
    valid := D.blocks_valid_public }

end RecordDecomposition

end RecordFerrers
end Collatz2
