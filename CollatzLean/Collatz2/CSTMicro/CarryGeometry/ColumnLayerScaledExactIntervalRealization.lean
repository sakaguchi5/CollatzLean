import CollatzLean.Collatz2.CSTMicro.CarryGeometry.IntervalFerrersDeficitCostBridge
import CollatzLean.Collatz2.CSTMicro.CarryGeometry.ColumnProfileResidualLedger
import CollatzLean.Collatz2.CSTMicro.CarryGeometry.MarkedFinalColumnCellPacket

/-!
# ColumnLayerScaledExactIntervalWitness の actual realization

`IntervalFerrersDeficitCostBridge` では、interval 内の各 occupied cell に対して

  3^m * C(k,j) = G * T(k,j) + scaledPower(k,j)

という局所 exact equation が存在することを
`ColumnLayerScaledExactIntervalWitness` として明示的な仮定にしていた。

このファイルでは、その仮定を actual critical-boundary Ferrers chain から構成する。

核心は次の単純な事実である。
critical boundary から final word までの Ferrers chain において、
final occupancy が `j+1` 以上である column `k` を取ると、chain の途中で必ず

  current occupancy = j

の時点に rank cut `k` を選ぶ Ferrers step が存在する。
その実在 step に既存の

  FerrersStep.columnLayerCellCost_scaled_exact

を適用すれば、final Ferrers diagram の cell `(k,j)` に必要な quotient witness `T`
が得られる。

したがって、ここでは新しい数論仮定を一切追加しない。
`ColumnLayerScaledExactIntervalWitness` は actual Ferrers chain の存在だけから従う。
-/

namespace Collatz2
namespace CSTMicro

open scoped BigOperators
open Collatz2.Word

namespace FerrersChain

/-!
## 1. occupied cell は chain 中の actual step として実現される
-/

/--
critical boundary 起点の Ferrers chain について、final occupancy の下にある任意の cell
`(k,j)` は既存の一 step exact equation を持つ。

  j < occupancy(k)

なら、chain の途中で column `k` の occupancy がちょうど `j` の時に
その column を選ぶ step が存在する。その step の
`columnLayerCellCost_scaled_exact` を final endpoint `(H,m)` へ transport する。
-/
theorem exists_columnLayerScaledExact_of_lt_occupancy
    {v finish : ParityWord}
    (C : FerrersChain (criticalBoundaryWord v.length) finish)
    (hFP : IsFirstPassageWord v)
    (hLen : 1 < v.length)
    {k j : ℕ}
    (hk : k < oddCount finish)
    (hj : j < C.rankColumnOccupancy k) :
    ∃ T : ℤ,
      (3 : ℤ) ^ oddCount finish *
          (columnLayerCellCostNat
            finish.length (oddCount finish) k j : ℤ) =
        (columnLayerGap finish.length (oddCount finish) : ℤ) * T +
          columnLayerScaledPowerTerm (oddCount finish) k j := by
  induction C generalizing k j with
  | refl =>
      simp [rankColumnOccupancy] at hj
  | @step u w C S ih =>
      have hBoundaryFP :
          IsFirstPassageWord (criticalBoundaryWord v.length) :=
        criticalBoundaryWord_isFirstPassage hFP
      have hUFP : IsFirstPassageWord u :=
        C.preserves_firstPassage hBoundaryFP
      change
        j < C.rankColumnOccupancy k +
          (if k = S.edge.rankCut then 1 else 0) at hj
      by_cases hjOld : j < C.rankColumnOccupancy k
      · have hkU : k < oddCount u := by
          rw [S.oddCount_eq]
          exact hk
        obtain ⟨T, hT⟩ := ih hkU hjOld
        refine ⟨T, ?_⟩
        rw [← S.length_eq, ← S.oddCount_eq]
        exact hT
      · by_cases hkSel : k = S.edge.rankCut
        · subst k
          have hjUpper :
              j < C.rankColumnOccupancy S.edge.rankCut + 1 := by
            simpa using hj
          have hjEq :
              j = C.rankColumnOccupancy S.edge.rankCut := by
            omega
          subst j
          have hkBoundary :=
            C.next_rankCut_lt_criticalBoundary_oddSteps S
          have hDepth :=
            C.criticalBoundary_selected_lower_extraDepth_eq_occupancy
              hFP hLen S hkBoundary
          obtain ⟨T, hT⟩ :=
            S.columnLayerCellCost_scaled_exact hUFP hDepth
          have hH : S.edge.length = w.length :=
            S.edge_length_eq_lower_length.trans S.length_eq
          have hm : S.edge.oddTotal = oddCount w :=
            S.edge_oddTotal_eq_lower_oddCount.trans S.oddCount_eq
          rw [hH, hm] at hT
          exact ⟨T, hT⟩
        · have hjOld' : j < C.rankColumnOccupancy k := by
            simpa [hkSel] using hj
          exact (hjOld hjOld').elim

/-!
## 2. 各 occupied cell の quotient を canonical に選ぶ
-/

/--
occupied cell `(k,j)` に対する local scaled quotient witness を選ぶ。

occupied range 外では値は使われないため `0` とする。
-/
noncomputable def columnLayerScaledExactQuotient
    {v finish : ParityWord}
    (C : FerrersChain (criticalBoundaryWord v.length) finish)
    (hFP : IsFirstPassageWord v)
    (hLen : 1 < v.length)
    (k j : ℕ) : ℤ :=
  if h : k < oddCount finish ∧ j < C.rankColumnOccupancy k then
    Classical.choose
      (C.exists_columnLayerScaledExact_of_lt_occupancy
        hFP hLen h.1 h.2)
  else
    0

/--
`columnLayerScaledExactQuotient` は occupied cell 上で期待した exact equation を満たす。
-/
theorem columnLayerScaledExactQuotient_spec
    {v finish : ParityWord}
    (C : FerrersChain (criticalBoundaryWord v.length) finish)
    (hFP : IsFirstPassageWord v)
    (hLen : 1 < v.length)
    {k j : ℕ}
    (hk : k < oddCount finish)
    (hj : j < C.rankColumnOccupancy k) :
    (3 : ℤ) ^ oddCount finish *
        (columnLayerCellCostNat
          finish.length (oddCount finish) k j : ℤ) =
      (columnLayerGap finish.length (oddCount finish) : ℤ) *
          C.columnLayerScaledExactQuotient hFP hLen k j +
        columnLayerScaledPowerTerm (oddCount finish) k j := by
  unfold columnLayerScaledExactQuotient
  rw [dite_eq_left ⟨hk, hj⟩]
  exact
    Classical.choose_spec
      (C.exists_columnLayerScaledExact_of_lt_occupancy
        hFP hLen hk hj)

/-!
## 3. occupancy profile に対する interval witness
-/

/--
critical-boundary chain の occupancy profile から、任意の rank interval `[a,a+n)` に対する
`ColumnLayerScaledExactIntervalWitness` を構成する。
-/
noncomputable def toColumnLayerScaledExactIntervalWitness
    {v finish : ParityWord}
    (C : FerrersChain (criticalBoundaryWord v.length) finish)
    (hFP : IsFirstPassageWord v)
    (hLen : 1 < v.length)
    {a n : ℕ}
    (hRange : a + n ≤ oddCount finish) :
    ColumnLayerScaledExactIntervalWitness
      finish.length
      (oddCount finish)
      C.rankColumnOccupancy
      a n := by
  refine {
    quotient := fun t j =>
      C.columnLayerScaledExactQuotient hFP hLen (a + t) j
    exact_cell := ?_
  }
  intro t j ht hj
  have hk : a + t < oddCount finish := by
    omega
  exact
    C.columnLayerScaledExactQuotient_spec
      hFP hLen hk hj

/-!
## 4. final extra-depth profile に transport
-/

/--
critical boundary 起点では final `parityExtraDepth` と column occupancy は一致する。
したがって occupancy witness は、そのまま final extra-depth profile の
`ColumnLayerScaledExactIntervalWitness` になる。
-/
noncomputable def toFinalExtraDepthScaledExactIntervalWitness
    {v finish : ParityWord}
    (C : FerrersChain (criticalBoundaryWord v.length) finish)
    (hFP : IsFirstPassageWord v)
    (hLen : 1 < v.length)
    {a n : ℕ}
    (hRange : a + n ≤ oddCount finish) :
    ColumnLayerScaledExactIntervalWitness
      finish.length
      (oddCount finish)
      (parityExtraDepth finish)
      a n := by
  let W :=
    C.toColumnLayerScaledExactIntervalWitness
      hFP hLen hRange
  refine {
    quotient := W.quotient
    exact_cell := ?_
  }
  intro t j ht hj
  have hk : a + t < oddCount finish := by
    omega
  have hProfile :
      C.rankColumnOccupancy (a + t) =
        parityExtraDepth finish (a + t) :=
    C.occupancy_eq_finalExtraDepth_on_range
      hFP hLen hk
  have hjOcc :
      j < C.rankColumnOccupancy (a + t) := by
    rw [hProfile]
    exact hj
  exact W.exact_cell t j ht hjOcc

/--
final extra-depth interval witness を存在命題として使うための wrapper。
-/
theorem exists_finalExtraDepth_scaledExactIntervalWitness
    {v finish : ParityWord}
    (C : FerrersChain (criticalBoundaryWord v.length) finish)
    (hFP : IsFirstPassageWord v)
    (hLen : 1 < v.length)
    {a n : ℕ}
    (hRange : a + n ≤ oddCount finish) :
    Nonempty
      (ColumnLayerScaledExactIntervalWitness
        finish.length
        (oddCount finish)
        (parityExtraDepth finish)
        a n) := by
  exact ⟨C.toFinalExtraDepthScaledExactIntervalWitness hFP hLen hRange⟩

end FerrersChain

/-!
## 5. Actual A -> B obstruction への specialization
-/

namespace ExternalArithmetic
namespace ActualABObstructionPacket

/--
actual A -> B provenance の critical-boundary-to-upper chain から、
final bad word `B` の任意 interval に対する scaled exact witness を構成する。

これにより `IntervalFerrersDeficitCostBridge` で仮定として残していた
`ColumnLayerScaledExactIntervalWitness` は、actual B では追加仮定ではなくなる。
-/
noncomputable def toScaledExactIntervalWitness
    {target : ParityWord}
    (A : ActualABObstructionPacket target)
    (hNontrivial : 2 < target.length)
    {a n : ℕ}
    (hRange :
      a + n ≤ oddCount A.cocycle.provenance.upper) :
    ColumnLayerScaledExactIntervalWitness
      A.cocycle.provenance.upper.length
      (oddCount A.cocycle.provenance.upper)
      (parityExtraDepth A.cocycle.provenance.upper)
      a n := by
  let C := A.criticalBoundaryToUpperChain
  have hLen : 1 < target.length := by
    omega
  exact
    C.toFinalExtraDepthScaledExactIntervalWitness
      A.cocycle.provenance.target_firstPassage
      hLen
      hRange

/--
actual B intervalでは witness を仮定せず、scaled cell-cost identity を直接得る。

  3^m C_int = G*T_int + dyadicCellInterval.
-/
theorem exists_intervalCellCost_scaled_exact
    {target : ParityWord}
    (A : ActualABObstructionPacket target)
    (hNontrivial : 2 < target.length)
    {a n : ℕ}
    (hRange :
      a + n ≤ oddCount A.cocycle.provenance.upper) :
    ∃ T : ℤ,
      (3 : ℤ) ^ oddCount A.cocycle.provenance.upper *
          (columnProfileCellCostInterval
            A.cocycle.provenance.upper.length
            (oddCount A.cocycle.provenance.upper)
            (parityExtraDepth A.cocycle.provenance.upper)
            a n : ℤ) =
        (columnLayerGap
          A.cocycle.provenance.upper.length
          (oddCount A.cocycle.provenance.upper) : ℤ) * T +
          (profileDyadicCellInterval
            (oddCount A.cocycle.provenance.upper)
            (parityExtraDepth A.cocycle.provenance.upper)
            a n : ℤ) := by
  let W := A.toScaledExactIntervalWitness hNontrivial hRange
  refine ⟨W.scaledQuotientSum, ?_⟩
  exact W.columnProfileCellCostInterval_scaled_exact

end ActualABObstructionPacket
end ExternalArithmetic

end CSTMicro
end Collatz2
