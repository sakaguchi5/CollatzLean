import CollatzLean.Collatz2.CSTMicro.CarryGeometry.MinimalBadFirstPassage
import CollatzLean.Collatz2.CSTMicro.CarryGeometry.ActualABObstructionPacket

/-!
# Minimal actual A -> B obstruction packet

`MinimalBadFirstPassageAtLength` では、同じ length の bad first-passage word の中から
Ferrers inversion が最小の word `B` を選んだ。

一方 `ActualABObstructionPacket` は、任意の nontrivial bad first-passage target に対して
actual A boundary から first failure までの provenance、bounded Farey strip、
canonical exact trace を保持する。

このファイルでは minimal bad word 自身を target として actual packet を構成し、
両者を一つの dependent packet にまとめる。

さらに重要な点として、actual provenance 内の distinguished first-failure upper が
minimal bad word より手前にあることはできない。

もし

  upper -> ... -> minimal B

という nontrivial suffix が残れば、Ferrers inversion は upper から B へ strict に増える。
しかし upper 自身も同じ length の bad first-passage word なので、B の inversion minimality に
反する。したがって actual first failure upper は exact に minimal B 自身である。
-/

namespace Collatz2
namespace CSTMicro

/-! ## 1. Ferrers chain の inversion 単調性 -/

namespace FerrersChain

/-- Ferrers chain に沿って inversion は weak に増加する。 -/
theorem ferrersInversion_le
    {start finish : ParityWord}
    (C : FerrersChain start finish) :
    ferrersInversion start ≤ ferrersInversion finish := by
  induction C with
  | refl =>
      exact Nat.le_refl _
  | step C S ih =>
      have hSucc := S.ferrersInversion_succ
      omega

/--
Ferrers chain の両 endpoint の inversion が等しければ、chain は実質 refl であり
endpoints は等しい。
-/
theorem eq_of_ferrersInversion_eq
    {start finish : ParityWord}
    (C : FerrersChain start finish)
    (hInv :
      ferrersInversion start =
        ferrersInversion finish) :
    start = finish := by
  cases C with
  | refl =>
      rfl
  | step C S =>
      have hLe := C.ferrersInversion_le
      have hSucc := S.ferrersInversion_succ
      omega

end FerrersChain

/-! ## 2. minimal bad word と actual A -> B packet の統合 -/

namespace ExternalArithmetic

/--
length `L` の inversion-minimal bad first-passage word と、その word 自身を target とする
actual A -> B obstruction packet を一つにまとめた object。
-/
structure MinimalActualABObstructionPacket (L : ℕ) where
  minimal : MinimalBadFirstPassageAtLength L
  actual : ActualABObstructionPacket minimal.word

namespace MinimalActualABObstructionPacket

/-- minimal packet の distinguished word。 -/
def word
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L) : ParityWord :=
  M.minimal.word

/-- minimal packet の word は指定 length `L` を持つ。 -/
theorem word_length_eq
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L) :
    M.word.length = L := by
  exact M.minimal.length_eq

/-- minimal packet の word 自身は first-passage。 -/
theorem word_firstPassage
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L) :
    IsFirstPassageWord M.word :=
  M.minimal.firstPassage

/-- minimal packet の word 自身は separation failure。 -/
theorem word_failure
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L) :
    ¬ WordPureSeparation M.word :=
  M.minimal.failure

/--
minimal bad word より inversion が strict に小さい同 length first-passage word は全て safe。
-/
theorem lower_region_safe
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    {v : ParityWord}
    (hLength : v.length = L)
    (hFP : IsFirstPassageWord v)
    (hInv : ferrersInversion v < M.minimal.inversion) :
    WordPureSeparation v := by
  exact M.minimal.safe_of_strictly_lower_inversion hLength hFP hInv

/--
actual provenance の distinguished first-failure upper は minimal bad word 自身。

minimality により first-failure upper の inversion は B 以上。
一方 failure suffix は upper から B への Ferrers chain なので inversion は B 以下。
したがって inversion は等しく、suffix chain の endpoint も等しい。
-/
theorem provenance_upper_eq_word
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L) :
    M.actual.cocycle.provenance.upper = M.word := by
  let P := M.actual.cocycle.provenance
  have hUpperLength : P.upper.length = L := by
    calc
      P.upper.length = M.minimal.word.length :=
        P.failureSuffixChain.length_eq
      _ = L := M.minimal.length_eq
  have hMinimal :
      M.minimal.inversion ≤ ferrersInversion P.upper :=
    M.minimal.inversion_le_of_failure
      hUpperLength
      P.upper_firstPassage
      P.upper_failure
  have hSuffix :
      ferrersInversion P.upper ≤ ferrersInversion M.minimal.word :=
    P.failureSuffixChain.ferrersInversion_le
  have hInvEq :
      ferrersInversion P.upper = ferrersInversion M.minimal.word := by
    unfold MinimalBadFirstPassageAtLength.inversion at hMinimal
    omega
  have hWordEq : P.upper = M.minimal.word :=
    P.failureSuffixChain.eq_of_ferrersInversion_eq hInvEq
  exact hWordEq

/--
actual provenance の final Ferrers step の upperWord も minimal bad word 自身。
-/
theorem failureStep_upperWord_eq_word
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L) :
    M.actual.cocycle.provenance.failureStep.edge.upperWord = M.word := by
  calc
    M.actual.cocycle.provenance.failureStep.edge.upperWord
        = M.actual.cocycle.provenance.upper :=
      M.actual.cocycle.provenance.failureStep.upper_eq.symm
    _ = M.word := M.provenance_upper_eq_word

/--
minimal actual packet では、B の直前までの actual safe-prefix carry はすべて clearance 未満。
-/
theorem all_previous_carries_lt_clearance
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L) :
    M.actual.cocycle.provenance.safePrefixChain.AllSteps
      (fun {lower upper : ParityWord}
          (S : FerrersStep lower upper) =>
        S.edge.HasCarry →
          S.edge.toFareyCellPacket.residue <
            - normalizedSeparationDefectInt lower) := by
  exact M.actual.all_previous_carries_lt_clearance

/--
minimal actual packet の final failure residue は残存 clearance に到達または超過する。
-/
theorem final_failureResidue_ge_clearance
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L) :
    - normalizedSeparationDefectInt M.actual.cocycle.provenance.lower ≤
      M.actual.cocycle.provenance.failureStep.edge.toFareyCellPacket.residue := by
  exact M.actual.final_failureResidue_ge_clearance

/--
minimality と actual A -> B provenance を同時に読む中心 summary。
-/
theorem minimal_actual_core
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L) :
    M.actual.cocycle.provenance.upper = M.word
      ∧
    (∀ v : ParityWord,
      v.length = L →
      IsFirstPassageWord v →
      ferrersInversion v < M.minimal.inversion →
      WordPureSeparation v)
      ∧
    M.actual.cocycle.provenance.safePrefixChain.AllSteps
      (fun {lower upper : ParityWord}
          (S : FerrersStep lower upper) =>
        S.edge.HasCarry →
          S.edge.toFareyCellPacket.residue <
            - normalizedSeparationDefectInt lower)
      ∧
    M.actual.cocycle.provenance.failureStep.edge.HasCarry
      ∧
    - normalizedSeparationDefectInt M.actual.cocycle.provenance.lower ≤
      M.actual.cocycle.provenance.failureStep.edge.toFareyCellPacket.residue := by
  refine ⟨M.provenance_upper_eq_word, ?_, ?_, ?_, ?_⟩
  · intro v hLength hFP hInv
    exact M.lower_region_safe hLength hFP hInv
  · exact M.all_previous_carries_lt_clearance
  · exact M.actual.cocycle.provenance.failure_hasCarry
  · exact M.final_failureResidue_ge_clearance

end MinimalActualABObstructionPacket

/-! ## 3. bad target から minimal actual packet を抽出 -/

/--
nontrivial bad first-passage target が一つあれば、同じ length に inversion-minimal bad word B があり、
その B 自身を target とする actual A -> B obstruction packet が存在する。
-/
theorem exists_minimalActualABObstructionPacket
    (R : RhinLinearForm14)
    {target : ParityWord}
    (hTargetFP : IsFirstPassageWord target)
    (hTargetFailure : ¬ WordPureSeparation target)
    (hTargetNontrivial : 2 < target.length) :
    Nonempty (MinimalActualABObstructionPacket target.length) := by
  rcases
      exists_minimalBadFirstPassageAtLength
        hTargetFP hTargetFailure with
    ⟨B⟩
  have hBNontrivial : 2 < B.word.length := by
    rw [B.length_eq]
    exact hTargetNontrivial
  rcases
      exists_actualABObstructionPacket
        R B.firstPassage B.failure hBNontrivial with
    ⟨A⟩
  exact
    ⟨{
      minimal := B
      actual := A
    }⟩

/--
step 7 の lossless bridge。

bad target から、minimal bad B と actual A -> B packet を同時に持ち、
actual distinguished first-failure upper が exact に B 自身である packet を得る。
-/
theorem exists_minimalActualABObstructionPacket_with_exact_B
    (R : RhinLinearForm14)
    {target : ParityWord}
    (hTargetFP : IsFirstPassageWord target)
    (hTargetFailure : ¬ WordPureSeparation target)
    (hTargetNontrivial : 2 < target.length) :
    ∃ M : MinimalActualABObstructionPacket target.length,
      M.actual.cocycle.provenance.upper = M.word
        ∧
      ∀ v : ParityWord,
        v.length = target.length →
        IsFirstPassageWord v →
        ferrersInversion v < M.minimal.inversion →
        WordPureSeparation v := by
  rcases
      exists_minimalActualABObstructionPacket
        R hTargetFP hTargetFailure hTargetNontrivial with
    ⟨M⟩
  refine ⟨M, M.provenance_upper_eq_word, ?_⟩
  intro v hLength hFP hInv
  exact M.lower_region_safe hLength hFP hInv

end ExternalArithmetic

end CSTMicro
end Collatz2
