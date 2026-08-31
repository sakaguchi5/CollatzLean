import CollatzLean.Collatz2.CSTMicro.CarryGeometry.EffectiveWindingResidualBound
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBActualProfileCoordinateBridge
import CollatzLean.Collatz2.CSTMicro.CarryGeometry.MinimalBadPredecessorGeometry

/-!
# Actual A -> Pure B: 有効 winding / residual cost bridge

minimal bad word `B` について、actual provenance の critical boundary から
first-failure upper までの Ferrers chain は、minimality により upper が exact に `B` 自身。

一方 `toPureBProfileObstruction` の profile `h` は `B` の
`parityExtraDepth` そのもの。

この二つを合わせ、chain-level の

  q_B = q_A + G * E - R

を PureB profile 座標へ戻す。

さらに

  E = carryCount - A(h)

なので、最終的に

  q_B
    = q_A
      + G * (carryCount - A(h))
      - R(h)

を actual/PureB bridge として公開する。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

namespace MinimalActualABObstructionPacket

/--
actual critical boundary から minimal bad word `B` までの exact Ferrers chain。

既存 provenance chain の start/finish を

* `boundary = criticalBoundaryWord B.length`
* `upper = B`

で transport しただけで、step history 自体は変えない。
-/
def boundaryToBadFerrersChain
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L) :
    FerrersChain (criticalBoundaryWord M.word.length) M.word := by
  have hBoundary :
      M.actual.cocycle.provenance.boundary =
        criticalBoundaryWord M.word.length := by
    simpa [MinimalActualABObstructionPacket.word] using
      M.actual.boundary_eq_critical
  have hUpper :
      M.actual.cocycle.provenance.upper = M.word :=
    M.provenance_upper_eq_word
  rw [← hBoundary, ← hUpper]
  exact M.actual.cocycle.provenance.boundaryToUpperRankTopChain

/-- actual boundary -> B chain の有効 winding。 -/
noncomputable def boundaryToBadEffectiveWinding
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L) : ℤ :=
  M.boundaryToBadFerrersChain.actualEffectiveWindingSum

/--
PureB profile は actual minimal bad word の extra-depth profile と同じ関数。
-/
theorem pureProfile_eq_badExtraDepth
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    (M.toPureBProfileObstruction hL).h =
      parityExtraDepth M.word := by
  funext k
  exact M.toPureBProfileObstruction_h_apply hL k

/--
有効 winding の定義を PureB profile の full-gap quotient sum に戻す。

  E = carryCount - A(h).
-/
theorem boundaryToBadEffectiveWinding_eq_carryCount_sub_pureCostQuotient
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    M.boundaryToBadEffectiveWinding =
      (M.boundaryToBadFerrersChain.normalizedCarryCount : ℤ) -
        (columnProfileCostQuotientSum
          M.word.length
          (oddCount M.word)
          (M.toPureBProfileObstruction hL).h : ℤ) := by
  let C := M.boundaryToBadFerrersChain
  have hLen : 1 < M.word.length := by
    rw [M.word_length_eq]
    omega
  have hE :=
    C.actualEffectiveWindingSum_eq_carryCount_sub_costQuotientSum
  have hA :=
    C.actualCostQuotientSum_eq_finalExtraDepthProfile
      M.word_firstPassage hLen
  have hProfile := M.pureProfile_eq_badExtraDepth hL
  rw [hA, ← hProfile] at hE
  simpa [C, boundaryToBadEffectiveWinding] using hE

/--
actual/PureB の residualized exact bridge。

  q_B = q_A + G * E - R(h).
-/
theorem actualQ_eq_boundary_add_gap_mul_effectiveWinding_sub_pureResidual
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    (M.actual.q : ℤ) =
      normalizedSeparationDefectInt
          (criticalBoundaryWord M.word.length) +
        (wordTerminalGap
            (criticalBoundaryWord M.word.length) : ℤ) *
          M.boundaryToBadEffectiveWinding -
        (columnProfileResidualCostSum
          M.word.length
          (oddCount M.word)
          (M.toPureBProfileObstruction hL).h : ℤ) := by
  let C := M.boundaryToBadFerrersChain
  have hLen : 1 < M.word.length := by
    rw [M.word_length_eq]
    omega
  have hBoundaryFP :
      IsFirstPassageWord (criticalBoundaryWord M.word.length) :=
    criticalBoundaryWord_isFirstPassage M.word_firstPassage
  have hExact :=
    C.normalized_finish_eq_start_add_gap_mul_effectiveWindingSum_sub_residualCostSum
      hBoundaryFP
  have hR :=
    C.actualResidualCostSum_eq_finalExtraDepthProfile
      M.word_firstPassage hLen
  have hProfile := M.pureProfile_eq_badExtraDepth hL
  calc
    (M.actual.q : ℤ)
        = normalizedSeparationDefectInt M.word :=
          M.actual_q_cast_eq_word_normalized
    _ =
      normalizedSeparationDefectInt
          (criticalBoundaryWord M.word.length) +
        (wordTerminalGap
            (criticalBoundaryWord M.word.length) : ℤ) *
          M.boundaryToBadEffectiveWinding -
        (columnProfileResidualCostSum
          M.word.length
          (oddCount M.word)
          (M.toPureBProfileObstruction hL).h : ℤ) := by
            rw [hR, ← hProfile] at hExact
            simpa [C, boundaryToBadEffectiveWinding] using hExact

/--
ユーザー側の記号をそのまま出した actual/PureB exact bridge。

  q_B
    = q_A
      + G * (c - A(h))
      - R(h).
-/
theorem actualQ_eq_boundary_add_gap_mul_carry_sub_pureQuotient_sub_pureResidual
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    (M.actual.q : ℤ) =
      normalizedSeparationDefectInt
          (criticalBoundaryWord M.word.length) +
        (wordTerminalGap
            (criticalBoundaryWord M.word.length) : ℤ) *
          ((M.boundaryToBadFerrersChain.normalizedCarryCount : ℤ) -
            (columnProfileCostQuotientSum
              M.word.length
              (oddCount M.word)
              (M.toPureBProfileObstruction hL).h : ℤ)) -
        (columnProfileResidualCostSum
          M.word.length
          (oddCount M.word)
          (M.toPureBProfileObstruction hL).h : ℤ) := by
  have h :=
    M.actualQ_eq_boundary_add_gap_mul_effectiveWinding_sub_pureResidual hL
  rw [M.boundaryToBadEffectiveWinding_eq_carryCount_sub_pureCostQuotient hL] at h
  exact h

/--
actual chain の `E <= R` を PureB profile だけの右辺へ戻す。
-/
theorem boundaryToBadEffectiveWinding_le_pureResidualCost
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    M.boundaryToBadEffectiveWinding <=
      (columnProfileResidualCostSum
        M.word.length
        (oddCount M.word)
        (M.toPureBProfileObstruction hL).h : ℤ) := by
  let C := M.boundaryToBadFerrersChain
  have hLen : 1 < M.word.length := by
    rw [M.word_length_eq]
    omega
  have hBoundaryFP :
      IsFirstPassageWord (criticalBoundaryWord M.word.length) :=
    criticalBoundaryWord_isFirstPassage M.word_firstPassage
  have hE :=
    C.actualEffectiveWindingSum_le_actualResidualCostSum hBoundaryFP
  have hR :=
    C.actualResidualCostSum_eq_finalExtraDepthProfile
      M.word_firstPassage hLen
  have hProfile := M.pureProfile_eq_badExtraDepth hL
  rw [hR, ← hProfile] at hE
  simpa [C, boundaryToBadEffectiveWinding] using hE

/--
carry history を消去した endpoint difference bound。

  q_B - q_A <= (G - 1) * R(h).
-/
theorem actualQ_sub_boundary_le_gap_sub_one_mul_pureResidualCost
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    (M.actual.q : ℤ) -
        normalizedSeparationDefectInt
          (criticalBoundaryWord M.word.length) <=
      ((wordTerminalGap
          (criticalBoundaryWord M.word.length) : ℤ) - 1) *
        (columnProfileResidualCostSum
          M.word.length
          (oddCount M.word)
          (M.toPureBProfileObstruction hL).h : ℤ) := by
  let C := M.boundaryToBadFerrersChain
  have hLen : 1 < M.word.length := by
    rw [M.word_length_eq]
    omega
  have hBoundaryFP :
      IsFirstPassageWord (criticalBoundaryWord M.word.length) :=
    criticalBoundaryWord_isFirstPassage M.word_firstPassage
  have hDiff :=
    C.normalized_endpoint_difference_le_gap_sub_one_mul_residualCostSum
      hBoundaryFP
  have hR :=
    C.actualResidualCostSum_eq_finalExtraDepthProfile
      M.word_firstPassage hLen
  have hProfile := M.pureProfile_eq_badExtraDepth hL
  rw [hR, ← hProfile] at hDiff
  rw [← M.actual_q_cast_eq_word_normalized] at hDiff
  simpa [C] using hDiff

end MinimalActualABObstructionPacket

end ExternalArithmetic
end CSTMicro
end Collatz2
