import CollatzLean.Collatz2.CSTMicro.MultiCorner.ActualAttachedSharedCostPairAssembly
import CollatzLean.Collatz2.CSTMicro.CarryGeometry.ExactNormalizedFerrersLedger

/-!
# MultiCorner attached branch: actual double predecessor safety

`ActualAttachedSharedCostPairAssembly.lean` が通っていることを前提に、
last-two exposed predecessor の二セルを同時に戻した double predecessor を
一つの packet として formalize する。

このファイルの目的は一つだけである。

* double predecessor が first-passage なら、minimal bad word より Ferrers inversion が
  2 小さいので minimality から safe。
* representative threshold が no-carry 側なら、double predecessor の一段目は
  actual に no-carry。
* exact normalized Ferrers ledger を二段に適用すると

    q_double
      = q_B - D₀ - D₁ + G

  となる。
* `q_double < 0` から `AttachedSharedCostPair` が要求していた

    q_B - (G-C₀) - (G-C₁) + G < 0

  を得る。

したがって `doubleSafeNoCarry` は独立の算術仮定ではなく、
double predecessor の first-passage realization と minimality から従う。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

/--
二つの actual exposed predecessor cell を同時に戻した double predecessor。

`D.step1 : lower1 -> M.word` を二段目に固定し、
一段目 `doubleWord -> lower1` は `D.step0` の cell を commute して得るものとして
`deltaR / residue / gap / modulus` の exact identification を保持する。

この packet 自身には safety を入れない。
safety は後で `M.lower_region_safe` から導く。
-/
structure ActualAttachedDoublePredecessorData
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (A : AttachedTwoCornerPacket (M.toPureBProfileObstruction hL))
    (D : AttachedSharedCostActualPairAssemblyInput M hL A) where
  doubleWord : ParityWord

  /-- double predecessor から `D.lower1` への一段目。 -/
  first : FerrersStep doubleWord D.lower1

  /-- double predecessor 自身も first-passage。 -/
  double_firstPassage : IsFirstPassageWord doubleWord

  /-- commute 後の一段目は `step0` と同じ 2-adic increment。 -/
  first_deltaR_eq_step0 :
    first.edge.deltaR = D.step0.edge.deltaR

  /-- commute 後の一段目は `step0` と同じ Farey residue。 -/
  first_residue_eq_step0 :
    first.edge.toFareyCellPacket.residue =
      D.step0.edge.toFareyCellPacket.residue

  /-- common terminal gap も同じ。 -/
  first_gap_eq_step0 :
    first.edge.toFareyCellPacket.G =
      D.step0.edge.toFareyCellPacket.G

  /-- common modulus も同じ。 -/
  first_modulus_eq_step0 :
    first.edge.modulus = D.step0.edge.modulus

namespace ActualAttachedDoublePredecessorData

/--
一段目の upper representative は、二段目の lower representative と同じ。
これは intermediate word が同じ `D.lower1` であることの定義的帰結。
-/
theorem first_upperR_eq_second_lowerR
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    {hL : 2 < L}
    {A : AttachedTwoCornerPacket (M.toPureBProfileObstruction hL)}
    {D : AttachedSharedCostActualPairAssemblyInput M hL A}
    (X : ActualAttachedDoublePredecessorData M hL A D) :
    X.first.edge.upperR = D.step1.edge.lowerR := by
  unfold AdjacentFerrersSwap.upperR AdjacentFerrersSwap.lowerR
  exact
    congrArg leastRepresentative
      (X.first.upper_eq.symm.trans D.step1.lower_eq)

/--
二段目の upper representative は actual minimal bad word の canonical representative。
-/
theorem second_upperR_eq_badRepresentative
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    {hL : 2 < L}
    {A : AttachedTwoCornerPacket (M.toPureBProfileObstruction hL)}
    {D : AttachedSharedCostActualPairAssemblyInput M hL A}
    (_X : ActualAttachedDoublePredecessorData M hL A D) :
    D.step1.edge.upperR = leastRepresentative M.word := by
  unfold AdjacentFerrersSwap.upperR
  exact
    congrArg leastRepresentative D.step1.upper_eq.symm

/--
double predecessor は minimal bad word と同じ length を持つ。
-/
theorem doubleWord_length_eq
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    {hL : 2 < L}
    {A : AttachedTwoCornerPacket (M.toPureBProfileObstruction hL)}
    {D : AttachedSharedCostActualPairAssemblyInput M hL A}
    (X : ActualAttachedDoublePredecessorData M hL A D) :
    X.doubleWord.length = L := by
  calc
    X.doubleWord.length
        = D.lower1.length := X.first.length_eq
    _ = M.word.length := D.step1.length_eq
    _ = L := M.word_length_eq

/--
double predecessor の Ferrers inversion は
actual bad word `M.word` より exact に二段低い。
-/
theorem doubleWord_inversion_add_two_eq_bad
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    {hL : 2 < L}
    {A : AttachedTwoCornerPacket (M.toPureBProfileObstruction hL)}
    {D : AttachedSharedCostActualPairAssemblyInput M hL A}
    (X : ActualAttachedDoublePredecessorData M hL A D) :
    ferrersInversion M.word =
      ferrersInversion X.doubleWord + 2 := by
  have h0 := X.first.ferrersInversion_succ
  have h1 := D.step1.ferrersInversion_succ
  omega

/--
double predecessor の Ferrers inversion は
minimal bad word より strict に小さい。
-/
theorem doubleWord_inversion_lt
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    {hL : 2 < L}
    {A : AttachedTwoCornerPacket (M.toPureBProfileObstruction hL)}
    {D : AttachedSharedCostActualPairAssemblyInput M hL A}
    (X : ActualAttachedDoublePredecessorData M hL A D) :
    ferrersInversion X.doubleWord < M.minimal.inversion := by
  have h0 := X.first.ferrersInversion_succ
  have h1 := D.step1.ferrersInversion_succ
  unfold MinimalActualABObstructionPacket.word at h1
  unfold MinimalBadFirstPassageAtLength.inversion
  omega

/--
double predecessor は minimality により safe。

この theorem が `doubleSafeNoCarry` の本体であり、
安全性を Shared-Cost の独立仮定として置く必要はない。
-/
theorem doubleWord_safe
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    {hL : 2 < L}
    {A : AttachedTwoCornerPacket (M.toPureBProfileObstruction hL)}
    {D : AttachedSharedCostActualPairAssemblyInput M hL A}
    (X : ActualAttachedDoublePredecessorData M hL A D) :
    WordPureSeparation X.doubleWord := by
  exact
    M.lower_region_safe
      X.doubleWord_length_eq
      X.double_firstPassage
      X.doubleWord_inversion_lt

/--
double predecessor の normalized defect は strict negative。
-/
theorem doubleWord_normalized_neg
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    {hL : 2 < L}
    {A : AttachedTwoCornerPacket (M.toPureBProfileObstruction hL)}
    {D : AttachedSharedCostActualPairAssemblyInput M hL A}
    (X : ActualAttachedDoublePredecessorData M hL A D) :
    normalizedSeparationDefectInt X.doubleWord < 0 := by
  exact
    normalizedSeparationDefectInt_neg_of_wordPureSeparation
      X.double_firstPassage
      X.doubleWord_safe

/--
actual representative threshold

  δ₀ + δ₁ ≤ M + R

の側では、double predecessor の一段目は no-carry。

証明は二つの carry equation を重ねるだけ。
二段目 `D.step1 -> M.word` は minimal bad predecessor なので必ず carry。
もし一段目まで carry なら

  R_double + δ₀ + δ₁ = 2M + R

となる。一方 `R_double < M` なので

  M + R < δ₀ + δ₁,

となり threshold と矛盾する。
-/
theorem first_noCarry_of_actualThreshold
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    {hL : 2 < L}
    {A : AttachedTwoCornerPacket (M.toPureBProfileObstruction hL)}
    {D : AttachedSharedCostActualPairAssemblyInput M hL A}
    (X : ActualAttachedDoublePredecessorData M hL A D)
    (hThreshold :
      D.step0.edge.deltaR + D.step1.edge.deltaR ≤
        D.step0.edge.modulus + leastRepresentative M.word) :
    X.first.edge.NoCarry := by
  rcases X.first.edge.noCarry_or_hasCarry with hNo | hCarry
  · exact hNo
  · exfalso
    have hSecondCarry :
        D.step1.edge.HasCarry :=
      M.predecessor_hasCarry
        D.step1
        D.lower1_firstPassage
    have hMod10 :
        D.step1.edge.modulus = D.step0.edge.modulus := by
      exact_mod_cast D.shared_modulus
    have hFirstEq :=
      X.first.edge.lowerR_add_deltaR_eq_modulus_add_upperR_of_hasCarry
        hCarry
    have hSecondEq :=
      D.step1.edge.lowerR_add_deltaR_eq_modulus_add_upperR_of_hasCarry
        hSecondCarry
    have hMid :
        X.first.edge.upperR = D.step1.edge.lowerR :=
      X.first_upperR_eq_second_lowerR
    have hBadR :
        D.step1.edge.upperR =
          leastRepresentative M.word :=
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

/--
Shared-Cost の representative threshold を actual Nat threshold に戻す。
-/
theorem first_noCarry_of_pairThreshold
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    {hL : 2 < L}
    {A : AttachedTwoCornerPacket (M.toPureBProfileObstruction hL)}
    {D : AttachedSharedCostActualPairAssemblyInput M hL A}
    (X : ActualAttachedDoublePredecessorData M hL A D)
    (hThreshold :
      D.toPair.deltaSum ≤ D.toPair.representativeThreshold) :
    X.first.edge.NoCarry := by
  have hThresholdZ := hThreshold
  change
    (D.step0.edge.deltaR : ℤ) +
          (D.step1.edge.deltaR : ℤ) ≤
      (D.step0.edge.modulus : ℤ) +
          (leastRepresentative M.word : ℤ) at hThresholdZ
  have hThresholdNat :
      D.step0.edge.deltaR + D.step1.edge.deltaR ≤
        D.step0.edge.modulus + leastRepresentative M.word := by
    exact_mod_cast hThresholdZ
  exact X.first_noCarry_of_actualThreshold hThresholdNat

/--
no-carry branch の exact double-predecessor defect。

  q_double
    = q_B - D₀ - D₁ + G

と `q_double < 0` を組み合わせ、actual residue 座標で
`doubleSafeNoCarry` を得る。
-/
theorem actual_doubleSafeNoCarry
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    {hL : 2 < L}
    {A : AttachedTwoCornerPacket (M.toPureBProfileObstruction hL)}
    {D : AttachedSharedCostActualPairAssemblyInput M hL A}
    (X : ActualAttachedDoublePredecessorData M hL A D)
    (hThreshold :
      D.step0.edge.deltaR + D.step1.edge.deltaR ≤
        D.step0.edge.modulus + leastRepresentative M.word) :
    (M.actual.q : ℤ) -
        D.step0.edge.toFareyCellPacket.residue -
        D.step1.edge.toFareyCellPacket.residue +
        D.step0.edge.toFareyCellPacket.G < 0 := by
  have hNo :
      X.first.edge.NoCarry :=
    X.first_noCarry_of_actualThreshold hThreshold
  have hSecondCarry :
      D.step1.edge.HasCarry :=
    M.predecessor_hasCarry
      D.step1
      D.lower1_firstPassage
  have hFirst :=
    X.first.normalizedStepDelta_eq_fareyResidue_sub_gap_of_noCarry
      X.double_firstPassage
      hNo
  have hSecond :=
    D.step1.normalizedStepDelta_eq_fareyResidue_of_hasCarry
      D.lower1_firstPassage
      hSecondCarry
  have hDoubleNeg :=
    X.doubleWord_normalized_neg
  have hQ :=
    M.actual_q_cast_eq_word_normalized
  unfold FerrersStep.normalizedStepDelta at hFirst hSecond
  rw [
    X.first_residue_eq_step0,
    X.first_gap_eq_step0
  ] at hFirst
  linarith

/--
`AttachedSharedCostPair` が要求していた `doubleSafeNoCarry` を、
actual double predecessor + minimality から閉じる最終 theorem。

この theorem の結論は `AttachedSharedCostCheckpoint.doubleSafeNoCarry`
にそのまま渡せる型になっている。
-/
theorem pair_doubleSafeNoCarry
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    {hL : 2 < L}
    {A : AttachedTwoCornerPacket (M.toPureBProfileObstruction hL)}
    {D : AttachedSharedCostActualPairAssemblyInput M hL A}
    (X : ActualAttachedDoublePredecessorData M hL A D) :
    D.toPair.deltaSum ≤ D.toPair.representativeThreshold →
      D.toPair.normalizedQ -
          (D.toPair.gap - D.toPair.cost0) -
          (D.toPair.gap - D.toPair.cost1) +
          D.toPair.gap < 0 := by
  intro hThreshold
  have hThresholdNat :
      D.step0.edge.deltaR + D.step1.edge.deltaR ≤
        D.step0.edge.modulus + leastRepresentative M.word := by
    have hThresholdZ := hThreshold
    change
      (D.step0.edge.deltaR : ℤ) +
            (D.step1.edge.deltaR : ℤ) ≤
        (D.step0.edge.modulus : ℤ) +
            (leastRepresentative M.word : ℤ) at hThresholdZ
    exact_mod_cast hThresholdZ
  have hRaw :=
    X.actual_doubleSafeNoCarry hThresholdNat
  change
    (M.actual.q : ℤ) -
        (D.step0.edge.toFareyCellPacket.G -
          D.step0.edge.fareyCellCost) -
        (D.step0.edge.toFareyCellPacket.G -
          D.step1.edge.fareyCellCost) +
        D.step0.edge.toFareyCellPacket.G < 0
  unfold AdjacentFerrersSwap.fareyCellCost
  have hGap := D.shared_gap
  linarith

end ActualAttachedDoublePredecessorData

end MultiCorner
end CSTMicro
end Collatz2
