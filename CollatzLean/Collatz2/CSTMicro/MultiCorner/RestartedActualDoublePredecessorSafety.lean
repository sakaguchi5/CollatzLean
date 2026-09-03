import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedActualSharedCostPairAssembly
import CollatzLean.Collatz2.CSTMicro.CarryGeometry.ExactNormalizedFerrersLedger

/-!
# restarted branch: actual double predecessor の branch-independent safety

attached branch で使っている double predecessor の議論のうち、
attached placement に依存しない部分を `LastTwoExposedNormalForm` 上へ移す。

ここで未証明の幾何は明示的に packet の field として残す。
特に `double_firstPassage` は仮定であり、このファイルでは捏造しない。

一度この packet が構成できれば、minimality と exact normalized ledger だけで
no-carry 側の double defect は

  q_double = q_B - D₀ - D₁ + G

まで自動的に降りる。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

/--
last-two actual cells を二段に commute した double predecessor の最小 packet。

二段目は `D.step1 : D.lower1 -> M.word` に固定し、
一段目は previous cell を `D.lower1` の下へ commute したものとする。
commute で保存される `deltaR / residue / gap / modulus` は equality field で保持する。
-/
structure RestartedActualDoublePredecessorData
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (N : LastTwoExposedNormalForm (M.toPureBProfileObstruction hL))
    (D : LastTwoSharedCostActualPairAssemblyInput M hL N) where
  doubleWord : ParityWord
  first : FerrersStep doubleWord D.lower1
  double_firstPassage : IsFirstPassageWord doubleWord

  first_deltaR_eq_step0 :
    first.edge.deltaR = D.step0.edge.deltaR

  first_residue_eq_step0 :
    first.edge.toFareyCellPacket.residue =
      D.step0.edge.toFareyCellPacket.residue

  first_gap_eq_step0 :
    first.edge.toFareyCellPacket.G =
      D.step0.edge.toFareyCellPacket.G

  first_modulus_eq_step0 :
    first.edge.modulus = D.step0.edge.modulus

namespace RestartedActualDoublePredecessorData

/-- commute 後の一段目 upper representative は二段目 lower representative。 -/
theorem first_upperR_eq_second_lowerR
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    {hL : 2 < L}
    {N : LastTwoExposedNormalForm (M.toPureBProfileObstruction hL)}
    {D : LastTwoSharedCostActualPairAssemblyInput M hL N}
    (X : RestartedActualDoublePredecessorData M hL N D) :
    X.first.edge.upperR = D.step1.edge.lowerR := by
  unfold AdjacentFerrersSwap.upperR AdjacentFerrersSwap.lowerR
  exact
    congrArg leastRepresentative
      (X.first.upper_eq.symm.trans D.step1.lower_eq)

/-- 二段目の upper representative は minimal bad word の representative。 -/
theorem second_upperR_eq_badRepresentative
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    {hL : 2 < L}
    {N : LastTwoExposedNormalForm (M.toPureBProfileObstruction hL)}
    {D : LastTwoSharedCostActualPairAssemblyInput M hL N}
    (_X : RestartedActualDoublePredecessorData M hL N D) :
    D.step1.edge.upperR = leastRepresentative M.word := by
  unfold AdjacentFerrersSwap.upperR
  exact
    congrArg leastRepresentative D.step1.upper_eq.symm

/-- double predecessor は minimal bad word と同じ length。 -/
theorem doubleWord_length_eq
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    {hL : 2 < L}
    {N : LastTwoExposedNormalForm (M.toPureBProfileObstruction hL)}
    {D : LastTwoSharedCostActualPairAssemblyInput M hL N}
    (X : RestartedActualDoublePredecessorData M hL N D) :
    X.doubleWord.length = L := by
  calc
    X.doubleWord.length = D.lower1.length := X.first.length_eq
    _ = M.word.length := D.step1.length_eq
    _ = L := M.word_length_eq

/-- double predecessor の inversion は bad word より exact に二段低い。 -/
theorem doubleWord_inversion_add_two_eq_bad
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    {hL : 2 < L}
    {N : LastTwoExposedNormalForm (M.toPureBProfileObstruction hL)}
    {D : LastTwoSharedCostActualPairAssemblyInput M hL N}
    (X : RestartedActualDoublePredecessorData M hL N D) :
    ferrersInversion M.word =
      ferrersInversion X.doubleWord + 2 := by
  have h0 := X.first.ferrersInversion_succ
  have h1 := D.step1.ferrersInversion_succ
  omega

/-- double predecessor は minimal bad word より strict に小さい。 -/
theorem doubleWord_inversion_lt
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    {hL : 2 < L}
    {N : LastTwoExposedNormalForm (M.toPureBProfileObstruction hL)}
    {D : LastTwoSharedCostActualPairAssemblyInput M hL N}
    (X : RestartedActualDoublePredecessorData M hL N D) :
    ferrersInversion X.doubleWord < M.minimal.inversion := by
  have h0 := X.first.ferrersInversion_succ
  have h1 := D.step1.ferrersInversion_succ
  unfold MinimalActualABObstructionPacket.word at h1
  unfold MinimalBadFirstPassageAtLength.inversion
  omega

/-- first-passage が構成済みなら minimality から double predecessor は safe。 -/
theorem doubleWord_safe
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    {hL : 2 < L}
    {N : LastTwoExposedNormalForm (M.toPureBProfileObstruction hL)}
    {D : LastTwoSharedCostActualPairAssemblyInput M hL N}
    (X : RestartedActualDoublePredecessorData M hL N D) :
    WordPureSeparation X.doubleWord := by
  exact
    M.lower_region_safe
      X.doubleWord_length_eq
      X.double_firstPassage
      X.doubleWord_inversion_lt

/-- safe double predecessor の normalized defect は strict negative。 -/
theorem doubleWord_normalized_neg
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    {hL : 2 < L}
    {N : LastTwoExposedNormalForm (M.toPureBProfileObstruction hL)}
    {D : LastTwoSharedCostActualPairAssemblyInput M hL N}
    (X : RestartedActualDoublePredecessorData M hL N D) :
    normalizedSeparationDefectInt X.doubleWord < 0 := by
  exact
    normalizedSeparationDefectInt_neg_of_wordPureSeparation
      X.double_firstPassage
      X.doubleWord_safe

/--
actual threshold が no-carry 側なら commute 後の一段目は no-carry。
証明は attached 版と同じ二つの carry equation だけを使い、placement は使わない。
-/
theorem first_noCarry_of_actualThreshold
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    {hL : 2 < L}
    {N : LastTwoExposedNormalForm (M.toPureBProfileObstruction hL)}
    {D : LastTwoSharedCostActualPairAssemblyInput M hL N}
    (X : RestartedActualDoublePredecessorData M hL N D)
    (hThreshold :
      D.step0.edge.deltaR + D.step1.edge.deltaR ≤
        D.step0.edge.modulus + leastRepresentative M.word) :
    X.first.edge.NoCarry := by
  rcases X.first.edge.noCarry_or_hasCarry with hNo | hCarry
  · exact hNo
  · exfalso
    have hSecondCarry : D.step1.edge.HasCarry :=
      M.predecessor_hasCarry D.step1 D.lower1_firstPassage
    have hMod10 :
        D.step1.edge.modulus = D.step0.edge.modulus := by
      exact_mod_cast D.shared_modulus
    have hFirstEq :=
      X.first.edge.lowerR_add_deltaR_eq_modulus_add_upperR_of_hasCarry
        hCarry
    have hSecondEq :=
      D.step1.edge.lowerR_add_deltaR_eq_modulus_add_upperR_of_hasCarry
        hSecondCarry
    have hMid : X.first.edge.upperR = D.step1.edge.lowerR :=
      X.first_upperR_eq_second_lowerR
    have hBadR :
        D.step1.edge.upperR = leastRepresentative M.word :=
      X.second_upperR_eq_badRepresentative
    have hFirstEq' :
        X.first.edge.lowerR + D.step0.edge.deltaR =
          D.step0.edge.modulus + D.step1.edge.lowerR := by
      simpa [
        X.first_deltaR_eq_step0,
        X.first_modulus_eq_step0,
        hMid
      ] using hFirstEq
    have hSecondEq' :
        D.step1.edge.lowerR + D.step1.edge.deltaR =
          D.step0.edge.modulus + leastRepresentative M.word := by
      simpa [hMod10, hBadR] using hSecondEq
    have hDoubleRlt :
        X.first.edge.lowerR < D.step0.edge.modulus := by
      simpa [X.first_modulus_eq_step0] using
        X.first.edge.lowerR_lt_modulus
    omega

/-- Shared-Cost の no-carry threshold から actual Nat threshold を読む。 -/
theorem first_noCarry_of_pairThreshold
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    {hL : 2 < L}
    {N : LastTwoExposedNormalForm (M.toPureBProfileObstruction hL)}
    {D : LastTwoSharedCostActualPairAssemblyInput M hL N}
    (X : RestartedActualDoublePredecessorData M hL N D)
    (hThreshold :
      D.toPair.deltaSum ≤ D.toPair.representativeThreshold) :
    X.first.edge.NoCarry := by
  have hThresholdZ := hThreshold
  change
    (D.step0.edge.deltaR : ℤ) + (D.step1.edge.deltaR : ℤ) ≤
      (D.step0.edge.modulus : ℤ) +
        (leastRepresentative M.word : ℤ) at hThresholdZ
  have hThresholdNat :
      D.step0.edge.deltaR + D.step1.edge.deltaR ≤
        D.step0.edge.modulus + leastRepresentative M.word := by
    exact_mod_cast hThresholdZ
  exact X.first_noCarry_of_actualThreshold hThresholdNat

/--
no-carry 側では exact normalized ledger により
`q_B - D₀ - D₁ + G < 0` を得る。
-/
theorem actual_doubleNormalizedCandidate_neg
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    {hL : 2 < L}
    {N : LastTwoExposedNormalForm (M.toPureBProfileObstruction hL)}
    {D : LastTwoSharedCostActualPairAssemblyInput M hL N}
    (X : RestartedActualDoublePredecessorData M hL N D)
    (hThreshold :
      D.step0.edge.deltaR + D.step1.edge.deltaR ≤
        D.step0.edge.modulus + leastRepresentative M.word) :
    (M.actual.q : ℤ) -
        D.step0.edge.toFareyCellPacket.residue -
        D.step1.edge.toFareyCellPacket.residue +
        D.step0.edge.toFareyCellPacket.G < 0 := by
  have hNo : X.first.edge.NoCarry :=
    X.first_noCarry_of_actualThreshold hThreshold
  have hSecondCarry : D.step1.edge.HasCarry :=
    M.predecessor_hasCarry D.step1 D.lower1_firstPassage
  have hFirst :=
    X.first.normalizedStepDelta_eq_fareyResidue_sub_gap_of_noCarry
      X.double_firstPassage hNo
  have hSecond :=
    D.step1.normalizedStepDelta_eq_fareyResidue_of_hasCarry
      D.lower1_firstPassage hSecondCarry
  have hDoubleNeg := X.doubleWord_normalized_neg
  have hQ := M.actual_q_cast_eq_word_normalized
  unfold FerrersStep.normalizedStepDelta at hFirst hSecond
  rw [X.first_residue_eq_step0, X.first_gap_eq_step0] at hFirst
  linarith

/--
Shared-Cost 座標で no-carry 側の double normalized candidate が負であることを読む。
-/
theorem pair_doubleNormalizedQCandidate_neg
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    {hL : 2 < L}
    {N : LastTwoExposedNormalForm (M.toPureBProfileObstruction hL)}
    {D : LastTwoSharedCostActualPairAssemblyInput M hL N}
    (X : RestartedActualDoublePredecessorData M hL N D)
    (hThreshold :
      D.toPair.deltaSum ≤ D.toPair.representativeThreshold) :
    D.toPair.doubleNormalizedQCandidate
        D.step0.edge.toFareyCellPacket.residue
        D.step1.edge.toFareyCellPacket.residue < 0 := by
  have hThresholdZ := hThreshold
  change
    (D.step0.edge.deltaR : ℤ) + (D.step1.edge.deltaR : ℤ) ≤
      (D.step0.edge.modulus : ℤ) +
        (leastRepresentative M.word : ℤ) at hThresholdZ
  have hThresholdNat :
      D.step0.edge.deltaR + D.step1.edge.deltaR ≤
        D.step0.edge.modulus + leastRepresentative M.word := by
    exact_mod_cast hThresholdZ
  have hNeg := X.actual_doubleNormalizedCandidate_neg hThresholdNat
  change
    (M.actual.q : ℤ) + D.step0.edge.toFareyCellPacket.G -
        D.step0.edge.toFareyCellPacket.residue -
        D.step1.edge.toFareyCellPacket.residue < 0
  linarith


/--
double predecessor packet があれば、Shared-Cost の carry/no-carry 二分岐も
branch-independent に復元できる。

no-carry 側は exact ledger から `costSum < sharedBudget`、
carry 側は master identity から `sharedBudget < costSum` になる。
-/
theorem sharedBudget_dichotomy
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    {hL : 2 < L}
    {N : LastTwoExposedNormalForm (M.toPureBProfileObstruction hL)}
    {D : LastTwoSharedCostActualPairAssemblyInput M hL N}
    (X : RestartedActualDoublePredecessorData M hL N D) :
    (D.toPair.deltaSum ≤ D.toPair.representativeThreshold ∧
        D.toPair.costSum < D.toPair.sharedBudget) ∨
      (D.toPair.representativeThreshold < D.toPair.deltaSum ∧
        D.toPair.sharedBudget < D.toPair.costSum) := by
  apply D.toPair.sharedCost_branch_dichotomy
  intro hThreshold
  have hNeg := X.pair_doubleNormalizedQCandidate_neg hThreshold
  have hCost := D.toPair_costs_eq_gap_sub_residues
  unfold AttachedSharedCostPair.doubleNormalizedQCandidate at hNeg
  rw [hCost.1, hCost.2]
  linarith

end RestartedActualDoublePredecessorData

end MultiCorner
end CSTMicro
end Collatz2
