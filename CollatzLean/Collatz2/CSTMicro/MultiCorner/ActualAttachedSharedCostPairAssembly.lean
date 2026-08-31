import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedSharedCostRhoDepthCompatibility
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBExposedPredecessorRealization
import CollatzLean.Collatz2.CSTMicro.CarryGeometry.MinimalBadCellCostObstruction

/-!
# MultiCorner attached branch: actual Shared-Cost pair assembly

このファイルの目的は、abstract `AttachedSharedCostPair` を actual minimal-bad word の
terminal last-two exposed predecessors から組み立てるとき、どこまで既存 theorem だけで
進み、最後に何が残るかを Lean の型として露出させることである。

重要な分離は二段。

1. `exists_lastTwoActualPredecessorSteps`
   `AttachedTwoCornerPacket` の previous / terminal exposed cut から、
   `PureBExposedPredecessorRealization` を使って actual `FerrersStep _ M.word` を二本得る。
   ここは既存 theorem だけで閉じる。

2. `AttachedSharedCostActualPairAssemblyInput.toPair`
   二本の actual step の cell-cost exact identity は既存
   `twoPow_length_mul_fareyCellCost_eq_gap_mul_deltaR_add_deltaB` をそのまま使う。
   したがって constructor 自身で新しく要求されるのは、同じ bad word に由来する
   共通 modulus / gap の同定、bad affine decomposition、positivity だけである。

`doubleSafeNoCarry` はこのファイルには入れない。
それは `AttachedSharedCostPair` の構成条件ではなく、後段
`AttachedSharedCostCheckpoint` の本物の追加 obligation だからである。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

/--
actual attached last-two exposed cuts を、実際の first-passage predecessor step 二本へ戻す。

これは provenance 側で既に閉じている部分。
-/
theorem exists_lastTwoActualPredecessorSteps
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (A : AttachedTwoCornerPacket (M.toPureBProfileObstruction hL)) :
    ∃ lower0 lower1 : ParityWord,
      ∃ S0 : FerrersStep lower0 M.word,
        ∃ S1 : FerrersStep lower1 M.word,
          IsFirstPassageWord lower0 ∧
          IsFirstPassageWord lower1 ∧
          S0.edge.rankCut = A.normalForm.previous ∧
          S1.edge.rankCut = A.normalForm.terminal := by
  have E0 :
      (M.toPureBProfileObstruction hL).IsExposedPredecessorIndex
        A.normalForm.previous :=
    A.previous_isExposed
  have E1 :
      (M.toPureBProfileObstruction hL).IsExposedPredecessorIndex
        A.normalForm.terminal :=
    A.terminal_isExposed
  obtain ⟨lower0, S0, hFP0, hRank0⟩ :=
    M.exists_actualPredecessor_of_exposedIndex hL E0
  obtain ⟨lower1, S1, hFP1, hRank1⟩ :=
    M.exists_actualPredecessor_of_exposedIndex hL E1
  exact ⟨lower0, lower1, S0, S1, hFP0, hFP1, hRank0, hRank1⟩

/--
二本の actual predecessor step を Shared-Cost の一個の pair に束ねるための
最小 assembly input。

`cost`, `delta`, `weight` は自由変数にしない。
actual cell そのものから

* cost   = `fareyCellCost`
* delta  = `deltaR`
* weight = `deltaB`

と固定する。

したがって cell exact identity は field に要求せず、既存 theorem から constructor 内で証明する。
-/
structure AttachedSharedCostActualPairAssemblyInput
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (A : AttachedTwoCornerPacket (M.toPureBProfileObstruction hL)) where
  lower0 : ParityWord
  lower1 : ParityWord

  step0 : FerrersStep lower0 M.word
  step1 : FerrersStep lower1 M.word

  lower0_firstPassage : IsFirstPassageWord lower0
  lower1_firstPassage : IsFirstPassageWord lower1

  rank0_eq : step0.edge.rankCut = A.normalForm.previous
  rank1_eq : step1.edge.rankCut = A.normalForm.terminal

  /-- 二本は同じ actual bad word に入るので modulus は同じ。 -/
  shared_modulus :
    (step1.edge.modulus : ℤ) = (step0.edge.modulus : ℤ)

  /-- 二本は同じ actual bad word に入るので terminal gap も同じ。 -/
  shared_gap :
    step1.edge.toFareyCellPacket.G = step0.edge.toFareyCellPacket.G

  /-- actual bad word の affine numerator decomposition。 -/
  affine_decomposition :
    (affineConst M.word : ℤ) =
      step0.edge.toFareyCellPacket.G *
          (leastRepresentative M.word : ℤ) +
        (step0.edge.modulus : ℤ) * (M.actual.q : ℤ)

  modulus_pos : 0 < (step0.edge.modulus : ℤ)
  gap_pos : 0 < step0.edge.toFareyCellPacket.G

  /-- `AttachedSharedCostPair.extra_pos` の actual 版。 -/
  extra_pos :
    0 <
      (affineConst M.word : ℤ) +
        (step0.edge.deltaB : ℤ) +
        (step1.edge.deltaB : ℤ)

namespace AttachedSharedCostActualPairAssemblyInput

/--
actual two-cell data から abstract `AttachedSharedCostPair` を実際に構成する。

ここで二本の cell exact identity は仮定ではない。
`MinimalBadCellCostObstruction` の generic full-scale identity を使って証明する。
-/
noncomputable def toPair
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    {hL : 2 < L}
    {A : AttachedTwoCornerPacket (M.toPureBProfileObstruction hL)}
    (D : AttachedSharedCostActualPairAssemblyInput M hL A) :
    AttachedSharedCostPair := by
  refine
    { modulus := (D.step0.edge.modulus : ℤ)
      gap := D.step0.edge.toFareyCellPacket.G
      affineB := (affineConst M.word : ℤ)
      normalizedQ := (M.actual.q : ℤ)
      representative := (leastRepresentative M.word : ℤ)
      cost0 := D.step0.edge.fareyCellCost
      cost1 := D.step1.edge.fareyCellCost
      delta0 := (D.step0.edge.deltaR : ℤ)
      delta1 := (D.step1.edge.deltaR : ℤ)
      weight0 := (D.step0.edge.deltaB : ℤ)
      weight1 := (D.step1.edge.deltaB : ℤ)
      modulus_pos := D.modulus_pos
      gap_pos := D.gap_pos
      affine_decomposition := D.affine_decomposition
      cell0_exact := ?_
      cell1_exact := ?_
      extra_pos := D.extra_pos }
  · have h0 :=
      D.step0.edge.twoPow_length_mul_fareyCellCost_eq_gap_mul_deltaR_add_deltaB
    simpa [AdjacentFerrersSwap.modulus] using h0
  · have h1 :=
      D.step1.edge.twoPow_length_mul_fareyCellCost_eq_gap_mul_deltaR_add_deltaB
    have h1' :
        (D.step1.edge.modulus : ℤ) * D.step1.edge.fareyCellCost =
          D.step1.edge.toFareyCellPacket.G * (D.step1.edge.deltaR : ℤ) +
            (D.step1.edge.deltaB : ℤ) := by
      simpa [AdjacentFerrersSwap.modulus] using h1
    rw [D.shared_modulus, D.shared_gap] at h1'
    exact h1'

/-- constructor 後の数値が actual bad word / actual cells に固定されていること。 -/
theorem toPair_actual_coordinates
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    {hL : 2 < L}
    {A : AttachedTwoCornerPacket (M.toPureBProfileObstruction hL)}
    (D : AttachedSharedCostActualPairAssemblyInput M hL A) :
    let P := D.toPair
    P.affineB = (affineConst M.word : ℤ) ∧
    P.normalizedQ = (M.actual.q : ℤ) ∧
    P.representative = (leastRepresentative M.word : ℤ) ∧
    P.cost0 = D.step0.edge.fareyCellCost ∧
    P.cost1 = D.step1.edge.fareyCellCost ∧
    P.delta0 = (D.step0.edge.deltaR : ℤ) ∧
    P.delta1 = (D.step1.edge.deltaR : ℤ) ∧
    P.weight0 = (D.step0.edge.deltaB : ℤ) ∧
    P.weight1 = (D.step1.edge.deltaB : ℤ) := by
  simp [toPair]

end AttachedSharedCostActualPairAssemblyInput

/--
`AttachedTwoCornerPacket` から pair を作る直前に残る exact obligation。

first-passage predecessor 二本の存在自体は
`exists_lastTwoActualPredecessorSteps` で既に証明済み。
したがってこの Nonempty を閉じる仕事は、主として

* same-upper-word から `shared_modulus`, `shared_gap` を回収する bookkeeping、
* actual bad affine decomposition、
* positivity

である。

double-safe / carry 排除はまだここには含めない。
-/
def ActualAttachedSharedCostPairAssemblyObligation
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (A : AttachedTwoCornerPacket (M.toPureBProfileObstruction hL)) : Prop :=
  Nonempty (AttachedSharedCostActualPairAssemblyInput M hL A)

/-- assembly obligation が閉じれば actual Shared-Cost pair は存在する。 -/
theorem exists_actualAttachedSharedCostPair
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (A : AttachedTwoCornerPacket (M.toPureBProfileObstruction hL))
    (H : ActualAttachedSharedCostPairAssemblyObligation M hL A) :
    ∃ _P : AttachedSharedCostPair, True := by
  rcases H with ⟨D⟩
  exact ⟨D.toPair, trivial⟩

end MultiCorner
end CSTMicro
end Collatz2
