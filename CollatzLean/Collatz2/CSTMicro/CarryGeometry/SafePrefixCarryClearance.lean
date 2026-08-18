import CollatzLean.Collatz2.CSTMicro.CarryGeometry.SafePrefixExactCellFirstPassage

/-!
# Safe-prefix carry clearance

`SafeFerrersChain` が lossless に保持する step history を使って、
A boundary から B first failure 直前までの「全 endpoint が safe」という情報を
各 carry cell の strict inequality へ落とす。

normalized defect を `q(v)` と見ると、safe word では `q(v) < 0`。
したがって clearance は `-q(v) > 0` である。

safe prefix 内の carry step `lower -> upper` では

  q(upper) = q(lower) + D

かつ `q(upper) < 0` なので

  D < -q(lower).

一方、distinguished final failure carry では

  q(lower) < 0 <= q(upper),
  q(upper) = q(lower) + D_failure

だから

  -q(lower) <= D_failure.

つまり以前の全 carry はその時点の clearance を strict に下回り、
最後の B carry だけが clearance に到達または超過する。
-/

namespace Collatz2
namespace CSTMicro

/-! ## 1. 一つの safe carry step -/

namespace FerrersStep

/--
safe upper を持つ carry step の residue は、lower の safety clearance より strict に小さい。
-/
theorem carryResidue_lt_neg_lower_of_safe_upper
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower)
    (hUpperSafe : WordPureSeparation upper) :
    S.edge.HasCarry →
      S.edge.toFareyCellPacket.residue <
        - normalizedSeparationDefectInt lower := by
  intro hCarry
  have hUpperFP : IsFirstPassageWord upper :=
    S.preserves_firstPassage hLowerFP
  have hUpperNeg :
      normalizedSeparationDefectInt upper < 0 :=
    normalizedSeparationDefectInt_neg_of_wordPureSeparation
      hUpperFP hUpperSafe
  have hDelta :=
    S.normalizedStepDelta_eq_fareyResidue_of_hasCarry
      hLowerFP hCarry
  unfold normalizedStepDelta at hDelta
  linarith

end FerrersStep

/-! ## 2. safe prefix の全 carry -/

namespace SafeFerrersChain

/--
lossless safe chain に現れる全 carry step で、cell residue はその時点の
lower safety clearance より strict に小さい。

`AllSteps` を使うため、endpoint total だけでなく実際の constructor history 全体に
この条件が付く。
-/
theorem allSteps_carryResidue_lt_clearance :
    {start finish : ParityWord} →
      (C : SafeFerrersChain start finish) →
      IsFirstPassageWord start →
      C.AllSteps
        (fun {lower upper : ParityWord}
            (S : FerrersStep lower upper) =>
          S.edge.HasCarry →
            S.edge.toFareyCellPacket.residue <
              - normalizedSeparationDefectInt lower)
  | _, _, .refl _ _hSafe, _hStartFP => by
      simp [AllSteps]
  | _, _, .step C S hSafe, hStartFP => by
      have hPrev :=
        allSteps_carryResidue_lt_clearance C hStartFP
      have hLowerFP :=
        C.preserves_firstPassage hStartFP
      have hThis :=
        S.carryResidue_lt_neg_lower_of_safe_upper
          hLowerFP hSafe
      exact ⟨hPrev, hThis⟩

end SafeFerrersChain

/-! ## 3. A -> B provenance に直接適用 -/

namespace FirstFailureProvenance

/--
A boundary から B 直前までの safe prefix に現れる全 carry は、
その step の lower clearance より strict に小さい。
-/
theorem all_previous_carries_lt_clearance
    {target : ParityWord}
    (P : FirstFailureProvenance target) :
    P.safePrefixChain.AllSteps
      (fun {lower upper : ParityWord}
          (S : FerrersStep lower upper) =>
        S.edge.HasCarry →
          S.edge.toFareyCellPacket.residue <
            - normalizedSeparationDefectInt lower) := by
  exact
    P.safePrefixChain.allSteps_carryResidue_lt_clearance
      P.boundary_isBoundary.1

/--
最後の distinguished failure carry は lower の残存 clearance に到達または超過する。
-/
theorem final_failureResidue_ge_clearance
    {target : ParityWord}
    (P : FirstFailureProvenance target) :
    - normalizedSeparationDefectInt P.lower ≤
      P.failureStep.edge.toFareyCellPacket.residue := by
  have hUpper :
      0 ≤ normalizedSeparationDefectInt P.upper :=
    P.upper_normalized_nonneg
  have hJump :
      normalizedSeparationDefectInt P.upper =
        normalizedSeparationDefectInt P.lower +
          P.failureStep.edge.toFareyCellPacket.residue :=
    P.upper_eq_lower_add_failureResidue
  linarith

/--
A -> B の carry-clearance dichotomy を一つにまとめる。

* safe prefix 内の全 carry: `D < clearance`
* final failure step: carry かつ `clearance <= D_failure`
-/
theorem previous_carries_small_final_reaches_clearance
    {target : ParityWord}
    (P : FirstFailureProvenance target) :
    P.safePrefixChain.AllSteps
        (fun {lower upper : ParityWord}
            (S : FerrersStep lower upper) =>
          S.edge.HasCarry →
            S.edge.toFareyCellPacket.residue <
              - normalizedSeparationDefectInt lower)
      ∧
    P.failureStep.edge.HasCarry
      ∧
    - normalizedSeparationDefectInt P.lower ≤
      P.failureStep.edge.toFareyCellPacket.residue := by
  exact
    ⟨P.all_previous_carries_lt_clearance,
      P.failure_hasCarry,
      P.final_failureResidue_ge_clearance⟩

end FirstFailureProvenance

/-! ## 4. actual A -> B packet bridge -/

namespace ExternalArithmetic

namespace ActualABObstructionPacket

/-- actual A -> B packet から以前の全 carry の strict clearance condition を直接読む。 -/
theorem all_previous_carries_lt_clearance
    {target : ParityWord}
    (A : ActualABObstructionPacket target) :
    A.cocycle.provenance.safePrefixChain.AllSteps
      (fun {lower upper : ParityWord}
          (S : FerrersStep lower upper) =>
        S.edge.HasCarry →
          S.edge.toFareyCellPacket.residue <
            - normalizedSeparationDefectInt lower) := by
  exact A.cocycle.provenance.all_previous_carries_lt_clearance

/-- actual A -> B packet の final failure residue は残存 clearance に到達する。 -/
theorem final_failureResidue_ge_clearance
    {target : ParityWord}
    (A : ActualABObstructionPacket target) :
    - normalizedSeparationDefectInt A.cocycle.provenance.lower ≤
      A.cocycle.provenance.failureStep.edge.toFareyCellPacket.residue := by
  exact A.cocycle.provenance.final_failureResidue_ge_clearance

/-- actual packet が step 3 / 4 を同時に lossless に保持する。 -/
theorem previous_carries_small_final_reaches_clearance
    {target : ParityWord}
    (A : ActualABObstructionPacket target) :
    A.cocycle.provenance.safePrefixChain.AllSteps
        (fun {lower upper : ParityWord}
            (S : FerrersStep lower upper) =>
          S.edge.HasCarry →
            S.edge.toFareyCellPacket.residue <
              - normalizedSeparationDefectInt lower)
      ∧
    A.cocycle.provenance.failureStep.edge.HasCarry
      ∧
    - normalizedSeparationDefectInt A.cocycle.provenance.lower ≤
      A.cocycle.provenance.failureStep.edge.toFareyCellPacket.residue := by
  exact
    A.cocycle.provenance.previous_carries_small_final_reaches_clearance

end ActualABObstructionPacket

end ExternalArithmetic

end CSTMicro
end Collatz2
