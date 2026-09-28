import CollatzLean.Collatz3.CSTCarry.RecordCompatibilityFailure
import CollatzLean.Collatz3.CSTCarry.InteriorBoundaryState
import CollatzLean.Collatz3.CSTCarry.RecordBlockPieceRun
import CollatzLean.Collatz3.CSTCarry.FirstPassageCanonicalCarry
import CollatzLean.Collatz3.Ferrers.RecordArithmeticFactorization

/-!
# Collatz3 CSTCarry: all-width proof の strong-induction frontier

ここでは未証明数学を theorem に偽装しない。

all-width proof に必要な残りの本体を

`WidthInteriorTransportProperty`

として width ごとに切り出し、既証明の

`canonicalRecordLength_lt_width`

から strong induction が適用できることだけを theorem で閉じる。

non-Record branch は `RecordCompatibilityFailure` により
tie / premature carry-1 roof return / terminal carry-1 へ exact に分解済み。
-/

namespace Collatz3
open Ferrers
namespace CSTCarry

open Critical

/--
width `r` の任意 shifted local critical block が
任意 slack boundary state を保存すること。

これが all-width strong induction の本当の local statement。
-/
def WidthInteriorTransportProperty
    (r : ℕ) : Prop :=
  ∀ {m : ℕ}
    {h : Profile m}
    (_A : Admissible h)
    {a : ℕ}
    (_hStartRoof : IsRoofCut h a)
    (B : IsLocalCriticalBlock h a r),
      InteriorBlockTransportProperty h a r B

/-- width `p` より小さい全 width について transport property を仮定する strong IH。 -/
def StrongInteriorTransportIH
    (p : ℕ) : Prop :=
  ∀ r : ℕ, r < p → WidthInteriorTransportProperty r

/--
RecordFerrers の canonical block width は strong IH の適用範囲へ必ず入る。
-/
theorem strongInteriorIH_on_canonicalRecordLength
    {p r : ℕ}
    (R : RecordFerrers p)
    (IH : StrongInteriorTransportIH p)
    (hr : r ∈ canonicalRecordLengths R.profile.1) :
    WidthInteriorTransportProperty r := by
  exact IH r (R.canonicalRecordLength_lt_width hr)

/--
premature carry-1 roof-return witness は、その block width より strict に小さい
critical width `j` を露出する。

non-Record branch を smaller-width induction へ送るための最小算術 bridge。
-/
theorem prematureFailure_exposes_smaller_width
    {m : ℕ}
    {h : Profile m}
    {a r : ℕ}
    (F : HasPrematureCarryOneRoofReturn h a r) :
    ∃ j : ℕ,
      0 < j ∧
      j < r ∧
      IsRoofCut h (a + j) ∧
      beattyCarry a j = 1 := by
  exact F

/--
block 列中の全 width が `p` 未満なら、recursive premature failure は
実際に `p` 未満の local width `j` を露出する。
-/
theorem prematureCarryFailureFrom_exposes_smaller_width
    {m p : ℕ}
    {h : Profile m} :
    ∀ {a : ℕ} {rs : List ℕ},
      (∀ r ∈ rs, r < p) →
      PrematureCarryFailureFrom h a rs →
        ∃ b j : ℕ,
          0 < j ∧
          j < p ∧
          IsRoofCut h (b + j) ∧
          beattyCarry b j = 1
  | _a, [], _hWidths, hFail => by
      simp [PrematureCarryFailureFrom] at hFail
  | a, r :: rs, hWidths, hFail => by
      simp only [PrematureCarryFailureFrom] at hFail
      rcases hFail with hHead | hTail
      · rcases hHead with ⟨j, hjPos, hjr, hRoof, hCarry⟩
        have hrp : r < p := hWidths r (by simp)
        exact ⟨a, j, hjPos, lt_trans hjr hrp, hRoof, hCarry⟩
      · have hTailWidths :
            ∀ t ∈ rs, t < p := by
          intro t ht
          exact hWidths t (by simp [ht])
        exact prematureCarryFailureFrom_exposes_smaller_width
          hTailWidths hTail

/--
canonical Record block の中で premature failure が起きれば、
露出 width `j` は whole width `p` より strict に小さい。
-/
theorem prematureFailure_on_recordLength_lt_whole
    {p r : ℕ}
    (R : RecordFerrers p)
    (hr : r ∈ canonicalRecordLengths R.profile.1)
    {a : ℕ}
    (F : HasPrematureCarryOneRoofReturn R.profile.1 a r) :
    ∃ j : ℕ,
      0 < j ∧
      j < p ∧
      IsRoofCut R.profile.1 (a + j) ∧
      beattyCarry a j = 1 := by
  rcases F with ⟨j, hjPos, hjr, hRoof, hCarry⟩
  have hrp := R.canonicalRecordLength_lt_width hr
  exact ⟨j, hjPos, lt_trans hjr hrp, hRoof, hCarry⟩

/--
RecordFerrers canonical chain の premature branch は whole width より小さい
local width を必ず露出する。
-/
theorem prematureFailureFrom_canonicalRecordLengths_lt_whole
    {p : ℕ}
    (R : RecordFerrers p)
    (F :
      PrematureCarryFailureFrom
        R.profile.1
        initialRoofAnchor
        (canonicalRecordLengths R.profile.1)) :
    ∃ b j : ℕ,
      0 < j ∧
      j < p ∧
      IsRoofCut R.profile.1 (b + j) ∧
      beattyCarry b j = 1 := by
  apply prematureCarryFailureFrom_exposes_smaller_width
  · intro r hr
    exact R.canonicalRecordLength_lt_width hr
  · exact F

/--
Record branch の all-width proof で、interior block について新しく必要なのは
`WidthInteriorTransportProperty r` だけであることを公開する wrapper。
-/
theorem recordInteriorTransport_of_strongIH
    {p r m a : ℕ}
    (R : RecordFerrers p)
    (IH : StrongInteriorTransportIH p)
    (hr : r ∈ canonicalRecordLengths R.profile.1)
    {h : Profile m}
    (A : Admissible h)
    (hStartRoof : IsRoofCut h a)
    (B : IsLocalCriticalBlock h a r) :
    InteriorBlockTransportProperty h a r B := by
  exact (strongInteriorIH_on_canonicalRecordLength R IH hr)
    A hStartRoof B

/--
non-Record 三分岐それぞれから final carry bound を出す branch-wise interface。

三分岐の存在はすでに theorem なので、この predicate に残るのは
各 branch の数学だけである。
-/
def NonRecordBranchBoundProperty
    (p : ℕ) : Prop :=
  ∀ (P : CSTMicro.FirstPassagePath)
    (_hpEq : P.endpointOddCount = p)
    (hp : 0 < P.endpointOddCount),
    (Ferrers.RecordLevelTieWitness
        (P.endpointIndexedCriticalProfile hp)
        initialRoofAnchor →
      P.canonicalCarryFinal < 2 ^ criticalTwoDepth p) ∧
    (PrematureCarryFailureFrom
        (P.endpointIndexedCriticalProfile hp)
        initialRoofAnchor
        (canonicalRecordLengths
          (P.endpointIndexedCriticalProfile hp)) →
      P.canonicalCarryFinal < 2 ^ criticalTwoDepth p) ∧
    (TerminalCarryOneFrom
        (P.endpointIndexedCriticalProfile hp)
        initialRoofAnchor
        (canonicalRecordLengths
          (P.endpointIndexedCriticalProfile hp)) →
      P.canonicalCarryFinal < 2 ^ criticalTwoDepth p)

/--
non-Record branch に残る final-carry 問題を width ごとに切り出す。

failure の形自体は `RecordCompatibilityFailure` ですでに exact 分解済みであり、
ここではその各 witness から final carry bound を導く未解決部分だけを保持する。
-/
def NonRecordCarryBoundProperty
    (p : ℕ) : Prop :=
  ∀ (P : CSTMicro.FirstPassagePath)
    (_hpEq : P.endpointOddCount = p)
    (hp : 0 < P.endpointOddCount),
    ¬ P.RecordCompatible hp →
      P.canonicalCarryFinal <
        2 ^ criticalTwoDepth p

/--
branch-wise closure があれば non-Record 全体の carry bound が従う。
-/
theorem nonRecordCarryBound_of_branchBound
    {p : ℕ}
    (hp2 : 1 < p)
    (B : NonRecordBranchBoundProperty p) :
    NonRecordCarryBoundProperty p := by
  intro P hpEq hp hNot
  have hm : 1 < P.endpointOddCount := by
    rw [hpEq]
    exact hp2
  have hThree :=
    (P.not_recordCompatible_iff_three_way hp hm).1 hNot
  have hBounds := B P hpEq hp
  rcases hThree with hTie | hRest
  · exact hBounds.1 hTie
  · rcases hRest with hPremature | hTerminal
    · exact hBounds.2.1 hPremature
    · exact hBounds.2.2 hTerminal

/--
現時点の all-width frontier。

`p<=26` は既存 theorem で閉じている。
`26<p` に残る独立な数学は

1. smaller-width transport から width `p` の transport を閉じること、
2. non-Record branch の exact failure witnesses から final carry bound を閉じること

の二つである。
-/
def AllWidthRemainingCore : Prop :=
  (∀ p : ℕ,
      26 < p →
      StrongInteriorTransportIH p →
      WidthInteriorTransportProperty p) ∧
  (∀ p : ℕ,
      26 < p →
      NonRecordBranchBoundProperty p)

end CSTCarry
end Collatz3
