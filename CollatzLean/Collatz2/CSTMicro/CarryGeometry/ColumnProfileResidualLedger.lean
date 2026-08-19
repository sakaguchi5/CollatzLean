import CollatzLean.Collatz2.CSTMicro.CarryGeometry.CriticalColumnLayerFareyBridge

/-!
# Column-profile residual ledger

critical boundary から始まる Ferrers chain では、各 rank column `k` の current
extra-depth は、その column をそれまで何回通過したかという occupancy そのものになる。
`CriticalColumnLayerFareyBridge` により、その column の layer `j` を通過する cell の

* Farey residue `D`,
* full-gap cost quotient `A`,
* bounded residual cost `R`,
* residual rank-top letter `L`

は endpoint `(H,m)` と `(k,j)` だけから canonical に決まる。

このファイルでは final profile `h : ℕ → ℕ` に対して

  A(h)    = Σ_k Σ_{j<h(k)} costQuotient(H,m,k,j)
  R(h)    = Σ_k Σ_{j<h(k)} residualCost(H,m,k,j)
  L(h)    = Σ_k Σ_{j<h(k)} residualLambda(H,m,k,j)
  Dsum(h) = Σ_k Σ_{j<h(k)} fareyResidue(H,m,k,j)

を定義し、critical-boundary chain の actual step sum と exact に一致することを示す。

さらに rank-top sum の一 step lawを residualize すると

  ΔTop = G * residualLambda - 3 * residualCost

となり carry/effective-winding が消える。従って final profile だけから

  K(h) = Top(boundary) + G*L(h) - 3*R(h)

が決まり、final rank-top sum は exact に `K(h)` に一致する。
-/

namespace Collatz2
namespace CSTMicro

open scoped BigOperators

/-- column-height profile の一つの column を一層だけ増やす。 -/
def bumpColumnProfile
    (h : ℕ → ℕ)
    (k₀ : ℕ) : ℕ → ℕ :=
  fun k => h k + if k = k₀ then 1 else 0

/-- arbitrary additive cell weight の column-profile 二重和。 -/
def columnProfileSum
    {α : Type*}
    [AddCommMonoid α]
    (m : ℕ)
    (h : ℕ → ℕ)
    (weight : ℕ → ℕ → α) : α :=
  Finset.sum (Finset.range m)
    (fun k =>
      Finset.sum (Finset.range (h k))
        (fun j => weight k j))

/-- 一つの column を一層増やすと、profile sum はその top cell 一個分だけ増える。 -/
theorem columnProfileSum_bump
    {α : Type*}
    [AddCommMonoid α]
    (m : ℕ)
    (h : ℕ → ℕ)
    (weight : ℕ → ℕ → α)
    {k₀ : ℕ}
    (hk₀ : k₀ < m) :
    columnProfileSum m (bumpColumnProfile h k₀) weight =
      columnProfileSum m h weight + weight k₀ (h k₀) := by
  classical
  unfold columnProfileSum bumpColumnProfile
  have hPointwise :
      ∀ k ∈ Finset.range m,
        Finset.sum
            (Finset.range (h k + if k = k₀ then 1 else 0))
            (fun j => weight k j) =
          Finset.sum (Finset.range (h k)) (fun j => weight k j) +
            (if k = k₀ then weight k (h k) else 0) := by
    intro k hk
    by_cases hkk : k = k₀
    · subst k
      simp [Finset.sum_range_succ]
    · simp [hkk]
  calc
    Finset.sum (Finset.range m)
        (fun k =>
          Finset.sum
            (Finset.range (h k + if k = k₀ then 1 else 0))
            (fun j => weight k j))
        =
      Finset.sum (Finset.range m)
        (fun k =>
          Finset.sum (Finset.range (h k)) (fun j => weight k j) +
            (if k = k₀ then weight k (h k) else 0)) := by
          apply Finset.sum_congr rfl
          intro k hk
          exact hPointwise k hk
    _ =
      Finset.sum (Finset.range m)
          (fun k =>
            Finset.sum (Finset.range (h k)) (fun j => weight k j)) +
        Finset.sum (Finset.range m)
          (fun k => if k = k₀ then weight k (h k) else 0) := by
            rw [Finset.sum_add_distrib]
    _ =
      Finset.sum (Finset.range m)
          (fun k =>
            Finset.sum (Finset.range (h k)) (fun j => weight k j)) +
        weight k₀ (h k₀) := by
          have hSingle :
              Finset.sum (Finset.range m)
                  (fun k => if k = k₀ then weight k (h k) else 0) =
                weight k₀ (h k₀) := by
            rw [Finset.sum_eq_single k₀]
            · simp
            · intro b hb hbk
              simp [hbk]
            · intro hkNot
              exact False.elim (hkNot (Finset.mem_range.mpr hk₀))
          rw [hSingle]

/-- profile が relevant columns 上で一致すれば profile sum も一致する。 -/
theorem columnProfileSum_congr_of_eq_on_range
    {α : Type*}
    [AddCommMonoid α]
    (m : ℕ)
    (h₁ h₂ : ℕ → ℕ)
    (weight : ℕ → ℕ → α)
    (hh : ∀ k : ℕ, k < m → h₁ k = h₂ k) :
    columnProfileSum m h₁ weight =
      columnProfileSum m h₂ weight := by
  unfold columnProfileSum
  apply Finset.sum_congr rfl
  intro k hk
  rw [hh k (Finset.mem_range.mp hk)]

/-- `A(h)`: full-gap cost quotient の profile sum。 -/
def columnProfileCostQuotientSum
    (H m : ℕ)
    (h : ℕ → ℕ) : ℕ :=
  columnProfileSum m h
    (fun k j => columnLayerCostQuotient H m k j)

/-- `R(h)`: bounded residual cost の profile sum。 -/
def columnProfileResidualCostSum
    (H m : ℕ)
    (h : ℕ → ℕ) : ℕ :=
  columnProfileSum m h
    (fun k j => columnLayerResidualCost H m k j)

/-- `L(h)`: residual four-letter lambda の profile sum。 -/
def columnProfileResidualLambdaSum
    (H m : ℕ)
    (h : ℕ → ℕ) : ℕ :=
  columnProfileSum m h
    (fun k j => columnLayerResidualLambda H m k j)

/-- `Dsum(h)`: canonical Farey residue の integer profile sum。 -/
def columnProfileFareyResidueSum
    (H m : ℕ)
    (h : ℕ → ℕ) : ℤ :=
  columnProfileSum m h
    (fun k j => columnLayerFareyResidue H m k j)

/-- one-column bump law for `A(h)`。 -/
theorem columnProfileCostQuotientSum_bump
    {H m k₀ : ℕ}
    (h : ℕ → ℕ)
    (hk₀ : k₀ < m) :
    columnProfileCostQuotientSum H m (bumpColumnProfile h k₀) =
      columnProfileCostQuotientSum H m h +
        columnLayerCostQuotient H m k₀ (h k₀) := by
  exact columnProfileSum_bump m h
    (fun k j => columnLayerCostQuotient H m k j) hk₀

/-- one-column bump law for `R(h)`。 -/
theorem columnProfileResidualCostSum_bump
    {H m k₀ : ℕ}
    (h : ℕ → ℕ)
    (hk₀ : k₀ < m) :
    columnProfileResidualCostSum H m (bumpColumnProfile h k₀) =
      columnProfileResidualCostSum H m h +
        columnLayerResidualCost H m k₀ (h k₀) := by
  exact columnProfileSum_bump m h
    (fun k j => columnLayerResidualCost H m k j) hk₀

/-- one-column bump law for `L(h)`。 -/
theorem columnProfileResidualLambdaSum_bump
    {H m k₀ : ℕ}
    (h : ℕ → ℕ)
    (hk₀ : k₀ < m) :
    columnProfileResidualLambdaSum H m (bumpColumnProfile h k₀) =
      columnProfileResidualLambdaSum H m h +
        columnLayerResidualLambda H m k₀ (h k₀) := by
  exact columnProfileSum_bump m h
    (fun k j => columnLayerResidualLambda H m k j) hk₀

/-- one-column bump law for `Dsum(h)`。 -/
theorem columnProfileFareyResidueSum_bump
    {H m k₀ : ℕ}
    (h : ℕ → ℕ)
    (hk₀ : k₀ < m) :
    columnProfileFareyResidueSum H m (bumpColumnProfile h k₀) =
      columnProfileFareyResidueSum H m h +
        columnLayerFareyResidue H m k₀ (h k₀) := by
  exact columnProfileSum_bump m h
    (fun k j => columnLayerFareyResidue H m k j) hk₀

/-- profile rank-top increment `G*L(h)-3*R(h)`。 -/
def columnProfileRankTopIncrement
    (H m : ℕ)
    (h : ℕ → ℕ) : ℤ :=
  (columnLayerGap H m : ℤ) *
      (columnProfileResidualLambdaSum H m h : ℤ) -
    3 * (columnProfileResidualCostSum H m h : ℤ)

/-- boundary top sum を基準にした profile value `K(h)`。 -/
def columnProfileK
    (H m : ℕ)
    (baseTop : ℤ)
    (h : ℕ → ℕ) : ℤ :=
  baseTop + columnProfileRankTopIncrement H m h

namespace FerrersStep

/-- edge length は endpoint lower length と同じ。 -/
theorem edge_length_eq_lower_length
    {lower upper : ParityWord}
    (S : FerrersStep lower upper) :
    S.edge.length = lower.length := by
  calc
    S.edge.length = S.edge.lowerWord.length := S.edge.lowerWord_length.symm
    _ = lower.length := congrArg List.length S.lower_eq.symm

/-- edge odd total は endpoint lower odd count と同じ。 -/
theorem edge_oddTotal_eq_lower_oddCount
    {lower upper : ParityWord}
    (S : FerrersStep lower upper) :
    S.edge.oddTotal = oddCount lower := by
  calc
    S.edge.oddTotal = oddCount S.edge.lowerWord := S.edge.lowerWord_oddCount.symm
    _ = oddCount lower := congrArg oddCount S.lower_eq.symm

/--
full cost quotient を消去した one-step rank-top sum law。

  ΔTop = G * residualLambda - 3 * residualCost.
-/
theorem parityRankTopSum_step_residualized
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower)
    (hLowerLen : 1 < lower.length) :
    let hUpperFP : IsFirstPassageWord upper :=
      Eq.mp (congrArg IsFirstPassageWord S.upper_eq.symm)
        (S.edge_upper_firstPassage_of_lower hLowerFP)
    let hUpperLen : 1 < upper.length := by
      rw [← S.length_eq]
      exact hLowerLen
    (parityRankTopSum upper hUpperFP hUpperLen : ℤ) =
      (parityRankTopSum lower hLowerFP hLowerLen : ℤ) +
        (wordTerminalGap lower : ℤ) *
          (S.actualResidualRankTopLambda : ℤ) -
        3 * (S.actualRankTopResidualCost : ℤ) := by
  let hUpperFP : IsFirstPassageWord upper :=
    Eq.mp (congrArg IsFirstPassageWord S.upper_eq.symm)
      (S.edge_upper_firstPassage_of_lower hLowerFP)
  let hUpperLen : 1 < upper.length := by
    rw [← S.length_eq]
    exact hLowerLen
  change
    (parityRankTopSum upper hUpperFP hUpperLen : ℤ) =
      (parityRankTopSum lower hLowerFP hLowerLen : ℤ) +
        (wordTerminalGap lower : ℤ) *
          (S.actualResidualRankTopLambda : ℤ) -
        3 * (S.actualRankTopResidualCost : ℤ)
  have hOld := S.parityRankTopSum_step hLowerFP hLowerLen
  have hLam :=
    S.actualRankTopLambda_eq_three_mul_costQuotient_add_residualLambda
      hLowerFP
  have hGap : S.actualRankTopGap = wordTerminalGap lower := by
    unfold actualRankTopGap
    exact congrArg wordTerminalGap S.lower_eq.symm
  have hDecompNat :
      S.edge.fareyCellCost.toNat =
        S.actualRankTopGap * S.actualRankTopCostQuotient +
          S.actualRankTopResidualCost := by
    simpa [actualRankTopCostQuotient, actualRankTopResidualCost] using
      rankTopCost_eq_gap_mul_quotient_add_residual
        S.actualRankTopGap S.edge.fareyCellCost.toNat
  have hDecomp := congrArg (fun n : ℕ => (n : ℤ)) hDecompNat
  push_cast at hDecomp
  rw [hGap] at hDecomp
  dsimp [hUpperFP, hUpperLen] at hOld ⊢
  rw [hLam] at hOld
  push_cast at hOld
  rw [hDecomp] at hOld
  ring_nf at hOld ⊢
  exact hOld

end FerrersStep

namespace FerrersChain

open FerrersStep

/-- chain actual full-gap quotient sum。 -/
noncomputable def actualCostQuotientSum
    {start finish : ParityWord} :
    FerrersChain start finish → ℕ
  | .refl _ => 0
  | .step C S => C.actualCostQuotientSum + S.actualRankTopCostQuotient

/-- chain actual residual cost sum。 -/
noncomputable def actualResidualCostSum
    {start finish : ParityWord} :
    FerrersChain start finish → ℕ
  | .refl _ => 0
  | .step C S => C.actualResidualCostSum + S.actualRankTopResidualCost

/-- chain actual residual lambda sum。 -/
noncomputable def actualResidualLambdaSum
    {start finish : ParityWord} :
    FerrersChain start finish → ℕ
  | .refl _ => 0
  | .step C S => C.actualResidualLambdaSum + S.actualResidualRankTopLambda

/--
residualized rank-top sum の chain telescope。
-/
theorem parityRankTopSum_telescope_residualized
    {start finish : ParityWord}
    (C : FerrersChain start finish)
    (hStartFP : IsFirstPassageWord start)
    (hStartLen : 1 < start.length)
    (hFinishFP : IsFirstPassageWord finish)
    (hFinishLen : 1 < finish.length) :
    (parityRankTopSum finish hFinishFP hFinishLen : ℤ) =
      (parityRankTopSum start hStartFP hStartLen : ℤ) +
        (wordTerminalGap start : ℤ) *
          (C.actualResidualLambdaSum : ℤ) -
        3 * (C.actualResidualCostSum : ℤ) := by
  revert hFinishFP hFinishLen
  induction C with
  | refl =>
      intro hFinishFP hFinishLen
      have hProof :=
        parityRankTopSum_proof_irrel
          start hFinishFP hStartFP hFinishLen hStartLen
      rw [hProof]
      simp [actualResidualLambdaSum, actualResidualCostSum]
  | @step u v C S ih =>
      intro hFinishFP hFinishLen
      have hUFP : IsFirstPassageWord u :=
        C.preserves_firstPassage hStartFP
      have hULen : 1 < u.length := by
        rw [← C.length_eq]
        exact hStartLen
      have hIH := ih hUFP hULen
      have hStepRaw :=
        S.parityRankTopSum_step_residualized hUFP hULen
      let hVFP0 : IsFirstPassageWord v :=
        Eq.mp (congrArg IsFirstPassageWord S.upper_eq.symm)
          (S.edge_upper_firstPassage_of_lower hUFP)
      let hVLen0 : 1 < v.length := by
        rw [← S.length_eq]
        exact hULen
      have hStep0 :
          (parityRankTopSum v hVFP0 hVLen0 : ℤ) =
            (parityRankTopSum u hUFP hULen : ℤ) +
              (wordTerminalGap u : ℤ) *
                (S.actualResidualRankTopLambda : ℤ) -
              3 * (S.actualRankTopResidualCost : ℤ) := by
        simpa [hVFP0, hVLen0] using hStepRaw
      have hFinishProof :=
        parityRankTopSum_proof_irrel
          v hFinishFP hVFP0 hFinishLen hVLen0
      have hStep :
          (parityRankTopSum v hFinishFP hFinishLen : ℤ) =
            (parityRankTopSum u hUFP hULen : ℤ) +
              (wordTerminalGap u : ℤ) *
                (S.actualResidualRankTopLambda : ℤ) -
              3 * (S.actualRankTopResidualCost : ℤ) := by
        rw [hFinishProof]
        exact hStep0
      have hGap : wordTerminalGap u = wordTerminalGap start :=
        C.wordTerminalGap_eq.symm
      change
        (parityRankTopSum v hFinishFP hFinishLen : ℤ) =
          (parityRankTopSum start hStartFP hStartLen : ℤ) +
            (wordTerminalGap start : ℤ) *
              (((C.actualResidualLambdaSum +
                  S.actualResidualRankTopLambda : ℕ) : ℤ)) -
            3 *
              (((C.actualResidualCostSum +
                  S.actualRankTopResidualCost : ℕ) : ℤ))
      rw [hStep, hIH, hGap]
      push_cast
      ring

/-- next selected rank cut is within the boundary odd-column range. -/
theorem next_rankCut_lt_criticalBoundary_oddSteps
    {v lower upper : ParityWord}
    (C : FerrersChain (criticalBoundaryWord v.length) lower)
    (S : FerrersStep lower upper) :
    S.edge.rankCut <
      Collatz2.Word.oddSteps
        (exponentWordOfParity (criticalBoundaryWord v.length)) := by
  rw [oddSteps_exponentWordOfParity]
  have hCut : S.edge.rankCut < S.edge.oddTotal := by
    have h := S.edge.rankCut_lt_oddSteps
    rw [S.edge.rankUpperExponentWord_oddSteps] at h
    exact h
  have hOdd := C.oddCount_eq
  have hEdgeOdd := S.edge_oddTotal_eq_lower_oddCount
  rw [hOdd, ← hEdgeOdd]
  exact hCut

/-- critical-boundary chain の quotient sum は occupancy profile の `A(h)`。 -/
theorem actualCostQuotientSum_eq_occupancyProfile
    {v finish : ParityWord}
    (C : FerrersChain (criticalBoundaryWord v.length) finish)
    (hFP : IsFirstPassageWord v)
    (hLen : 1 < v.length) :
    C.actualCostQuotientSum =
      columnProfileCostQuotientSum
        finish.length (oddCount finish) C.rankColumnOccupancy := by
  induction C with
  | refl =>
      simp [actualCostQuotientSum, columnProfileCostQuotientSum,
        columnProfileSum, rankColumnOccupancy]
  | @step u w C S ih =>
      have hBoundaryFP :
          IsFirstPassageWord (criticalBoundaryWord v.length) :=
        criticalBoundaryWord_isFirstPassage hFP
      have hUFP : IsFirstPassageWord u :=
        C.preserves_firstPassage hBoundaryFP
      have hk : S.edge.rankCut < oddCount u := by
        have h := S.edge.rankCut_lt_oddSteps
        rw [S.edge.rankUpperExponentWord_oddSteps] at h
        rw [S.edge_oddTotal_eq_lower_oddCount] at h
        exact h
      have hkBoundary := C.next_rankCut_lt_criticalBoundary_oddSteps S
      have hLocal :=
        C.criticalBoundary_next_costQuotient_eq_columnLayer
          hFP hLen S hkBoundary
      rw [S.edge_length_eq_lower_length,
          S.edge_oddTotal_eq_lower_oddCount] at hLocal
      have hBump :=
        columnProfileCostQuotientSum_bump
          (H := u.length) (m := oddCount u)
          C.rankColumnOccupancy hk
      change
        C.actualCostQuotientSum + S.actualRankTopCostQuotient =
          columnProfileCostQuotientSum
            w.length (oddCount w)
            (bumpColumnProfile C.rankColumnOccupancy S.edge.rankCut)
      rw [← S.length_eq, ← S.oddCount_eq]
      rw [hBump, ← ih, ← hLocal]

/-- critical-boundary chain の residual cost sum は occupancy profile の `R(h)`。 -/
theorem actualResidualCostSum_eq_occupancyProfile
    {v finish : ParityWord}
    (C : FerrersChain (criticalBoundaryWord v.length) finish)
    (hFP : IsFirstPassageWord v)
    (hLen : 1 < v.length) :
    C.actualResidualCostSum =
      columnProfileResidualCostSum
        finish.length (oddCount finish) C.rankColumnOccupancy := by
  induction C with
  | refl =>
      simp [actualResidualCostSum, columnProfileResidualCostSum,
        columnProfileSum, rankColumnOccupancy]
  | @step u w C S ih =>
      have hBoundaryFP :
          IsFirstPassageWord (criticalBoundaryWord v.length) :=
        criticalBoundaryWord_isFirstPassage hFP
      have hUFP : IsFirstPassageWord u :=
        C.preserves_firstPassage hBoundaryFP
      have hk : S.edge.rankCut < oddCount u := by
        have h := S.edge.rankCut_lt_oddSteps
        rw [S.edge.rankUpperExponentWord_oddSteps] at h
        rw [S.edge_oddTotal_eq_lower_oddCount] at h
        exact h
      have hkBoundary := C.next_rankCut_lt_criticalBoundary_oddSteps S
      have hLocal :=
        C.criticalBoundary_next_residualCost_eq_columnLayer
          hFP hLen S hkBoundary
      rw [S.edge_length_eq_lower_length,
          S.edge_oddTotal_eq_lower_oddCount] at hLocal
      have hBump :=
        columnProfileResidualCostSum_bump
          (H := u.length) (m := oddCount u)
          C.rankColumnOccupancy hk
      change
        C.actualResidualCostSum + S.actualRankTopResidualCost =
          columnProfileResidualCostSum
            w.length (oddCount w)
            (bumpColumnProfile C.rankColumnOccupancy S.edge.rankCut)
      rw [← S.length_eq, ← S.oddCount_eq]
      rw [hBump, ← ih, ← hLocal]

/-- critical-boundary chain の residual lambda sum は occupancy profile の `L(h)`。 -/
theorem actualResidualLambdaSum_eq_occupancyProfile
    {v finish : ParityWord}
    (C : FerrersChain (criticalBoundaryWord v.length) finish)
    (hFP : IsFirstPassageWord v)
    (hLen : 1 < v.length) :
    C.actualResidualLambdaSum =
      columnProfileResidualLambdaSum
        finish.length (oddCount finish) C.rankColumnOccupancy := by
  induction C with
  | refl =>
      simp [actualResidualLambdaSum, columnProfileResidualLambdaSum,
        columnProfileSum, rankColumnOccupancy]
  | @step u w C S ih =>
      have hBoundaryFP :
          IsFirstPassageWord (criticalBoundaryWord v.length) :=
        criticalBoundaryWord_isFirstPassage hFP
      have hUFP : IsFirstPassageWord u :=
        C.preserves_firstPassage hBoundaryFP
      have hk : S.edge.rankCut < oddCount u := by
        have h := S.edge.rankCut_lt_oddSteps
        rw [S.edge.rankUpperExponentWord_oddSteps] at h
        rw [S.edge_oddTotal_eq_lower_oddCount] at h
        exact h
      have hkBoundary := C.next_rankCut_lt_criticalBoundary_oddSteps S
      have hLocal :=
        C.criticalBoundary_next_residualLambda_eq_columnLayer
          hFP hLen S hkBoundary
      rw [S.edge_length_eq_lower_length,
          S.edge_oddTotal_eq_lower_oddCount] at hLocal
      have hBump :=
        columnProfileResidualLambdaSum_bump
          (H := u.length) (m := oddCount u)
          C.rankColumnOccupancy hk
      change
        C.actualResidualLambdaSum + S.actualResidualRankTopLambda =
          columnProfileResidualLambdaSum
            w.length (oddCount w)
            (bumpColumnProfile C.rankColumnOccupancy S.edge.rankCut)
      rw [← S.length_eq, ← S.oddCount_eq]
      rw [hBump, ← ih, ← hLocal]

/-- critical-boundary chain の Farey residue sum は occupancy profile の `Dsum(h)`。 -/
theorem normalizedCellResidueSum_eq_occupancyProfile
    {v finish : ParityWord}
    (C : FerrersChain (criticalBoundaryWord v.length) finish)
    (hFP : IsFirstPassageWord v)
    (hLen : 1 < v.length) :
    C.normalizedCellResidueSum =
      columnProfileFareyResidueSum
        finish.length (oddCount finish) C.rankColumnOccupancy := by
  induction C with
  | refl =>
      simp [normalizedCellResidueSum, columnProfileFareyResidueSum,
        columnProfileSum, rankColumnOccupancy]
  | @step u w C S ih =>
      have hk : S.edge.rankCut < oddCount u := by
        have h := S.edge.rankCut_lt_oddSteps
        rw [S.edge.rankUpperExponentWord_oddSteps] at h
        rw [S.edge_oddTotal_eq_lower_oddCount] at h
        exact h
      have hkBoundary := C.next_rankCut_lt_criticalBoundary_oddSteps S
      have hLocal :=
        C.criticalBoundary_next_fareyResidue_eq_columnLayer
          hFP hLen S hkBoundary
      rw [S.edge_length_eq_lower_length,
          S.edge_oddTotal_eq_lower_oddCount] at hLocal
      have hBump :=
        columnProfileFareyResidueSum_bump
          (H := u.length) (m := oddCount u)
          C.rankColumnOccupancy hk
      change
        C.normalizedCellResidueSum + S.edge.toFareyCellPacket.residue =
          columnProfileFareyResidueSum
            w.length (oddCount w)
            (bumpColumnProfile C.rankColumnOccupancy S.edge.rankCut)
      rw [← S.length_eq, ← S.oddCount_eq]
      rw [hBump, ← ih, ← hLocal]

/-- relevant rank columns 上で occupancy と final extra-depth は一致する。 -/
theorem occupancy_eq_finalExtraDepth_on_range
    {v finish : ParityWord}
    (C : FerrersChain (criticalBoundaryWord v.length) finish)
    (hFP : IsFirstPassageWord v)
    (hLen : 1 < v.length)
    {k : ℕ}
    (hk : k < oddCount finish) :
    C.rankColumnOccupancy k = parityExtraDepth finish k := by
  have hkBoundary :
      k < Collatz2.Word.oddSteps
        (exponentWordOfParity (criticalBoundaryWord v.length)) := by
    rw [oddSteps_exponentWordOfParity]
    rw [C.oddCount_eq]
    exact hk
  exact
    (criticalBoundary_to_finish_extraDepth_eq_columnOccupancy
      hFP hLen C hkBoundary).symm

/-- `A(h)` も final extra-depth profile だけで決まる。 -/
theorem actualCostQuotientSum_eq_finalExtraDepthProfile
    {v finish : ParityWord}
    (C : FerrersChain (criticalBoundaryWord v.length) finish)
    (hFP : IsFirstPassageWord v)
    (hLen : 1 < v.length) :
    C.actualCostQuotientSum =
      columnProfileCostQuotientSum
        finish.length (oddCount finish) (parityExtraDepth finish) := by
  rw [C.actualCostQuotientSum_eq_occupancyProfile hFP hLen]
  unfold columnProfileCostQuotientSum
  apply columnProfileSum_congr_of_eq_on_range
  intro k hk
  exact C.occupancy_eq_finalExtraDepth_on_range hFP hLen hk

/-- `R(h)` も final extra-depth profile だけで決まる。 -/
theorem actualResidualCostSum_eq_finalExtraDepthProfile
    {v finish : ParityWord}
    (C : FerrersChain (criticalBoundaryWord v.length) finish)
    (hFP : IsFirstPassageWord v)
    (hLen : 1 < v.length) :
    C.actualResidualCostSum =
      columnProfileResidualCostSum
        finish.length (oddCount finish) (parityExtraDepth finish) := by
  rw [C.actualResidualCostSum_eq_occupancyProfile hFP hLen]
  unfold columnProfileResidualCostSum
  apply columnProfileSum_congr_of_eq_on_range
  intro k hk
  exact C.occupancy_eq_finalExtraDepth_on_range hFP hLen hk

/-- `L(h)` も final extra-depth profile だけで決まる。 -/
theorem actualResidualLambdaSum_eq_finalExtraDepthProfile
    {v finish : ParityWord}
    (C : FerrersChain (criticalBoundaryWord v.length) finish)
    (hFP : IsFirstPassageWord v)
    (hLen : 1 < v.length) :
    C.actualResidualLambdaSum =
      columnProfileResidualLambdaSum
        finish.length (oddCount finish) (parityExtraDepth finish) := by
  rw [C.actualResidualLambdaSum_eq_occupancyProfile hFP hLen]
  unfold columnProfileResidualLambdaSum
  apply columnProfileSum_congr_of_eq_on_range
  intro k hk
  exact C.occupancy_eq_finalExtraDepth_on_range hFP hLen hk

/-- `Dsum(h)` も final extra-depth profile だけで決まる。 -/
theorem normalizedCellResidueSum_eq_finalExtraDepthProfile
    {v finish : ParityWord}
    (C : FerrersChain (criticalBoundaryWord v.length) finish)
    (hFP : IsFirstPassageWord v)
    (hLen : 1 < v.length) :
    C.normalizedCellResidueSum =
      columnProfileFareyResidueSum
        finish.length (oddCount finish) (parityExtraDepth finish) := by
  rw [C.normalizedCellResidueSum_eq_occupancyProfile hFP hLen]
  unfold columnProfileFareyResidueSum
  apply columnProfileSum_congr_of_eq_on_range
  intro k hk
  exact C.occupancy_eq_finalExtraDepth_on_range hFP hLen hk

/-- endpoint `(H,m)` の gap と boundary terminal gap の一致。 -/
theorem columnLayerGap_finish_eq_boundaryGap
    {v finish : ParityWord}
    (C : FerrersChain (criticalBoundaryWord v.length) finish) :
    columnLayerGap finish.length (oddCount finish) =
      wordTerminalGap (criticalBoundaryWord v.length) := by
  unfold columnLayerGap wordTerminalGap
  rw [← C.length_eq, ← C.oddCount_eq]

/--
critical boundary から final word までの rank-top sum は final profile value `K(h)`。
-/
theorem parityRankTopSum_eq_columnProfileK
    {v finish : ParityWord}
    (C : FerrersChain (criticalBoundaryWord v.length) finish)
    (hFP : IsFirstPassageWord v)
    (hLen : 1 < v.length) :
    let hBoundaryFP : IsFirstPassageWord (criticalBoundaryWord v.length) :=
      criticalBoundaryWord_isFirstPassage hFP
    let hBoundaryLen : 1 < (criticalBoundaryWord v.length).length := by
      simpa using hLen
    let hFinishFP : IsFirstPassageWord finish :=
      C.preserves_firstPassage hBoundaryFP
    let hFinishLen : 1 < finish.length := by
      rw [← C.length_eq]
      exact hBoundaryLen
    (parityRankTopSum finish hFinishFP hFinishLen : ℤ) =
      columnProfileK
        finish.length
        (oddCount finish)
        (parityRankTopSum
          (criticalBoundaryWord v.length)
          hBoundaryFP hBoundaryLen : ℤ)
        (parityExtraDepth finish) := by
  let hBoundaryFP : IsFirstPassageWord (criticalBoundaryWord v.length) :=
    criticalBoundaryWord_isFirstPassage hFP
  let hBoundaryLen : 1 < (criticalBoundaryWord v.length).length := by
    simpa using hLen
  let hFinishFP : IsFirstPassageWord finish :=
    C.preserves_firstPassage hBoundaryFP
  let hFinishLen : 1 < finish.length := by
    rw [← C.length_eq]
    exact hBoundaryLen
  change
    (parityRankTopSum finish hFinishFP hFinishLen : ℤ) =
      columnProfileK
        finish.length (oddCount finish)
        (parityRankTopSum
          (criticalBoundaryWord v.length)
          hBoundaryFP hBoundaryLen : ℤ)
        (parityExtraDepth finish)
  have hTel :=
    C.parityRankTopSum_telescope_residualized
      hBoundaryFP hBoundaryLen hFinishFP hFinishLen
  have hL := C.actualResidualLambdaSum_eq_finalExtraDepthProfile hFP hLen
  have hR := C.actualResidualCostSum_eq_finalExtraDepthProfile hFP hLen
  have hG := C.columnLayerGap_finish_eq_boundaryGap
  unfold columnProfileK columnProfileRankTopIncrement
  rw [← hG, hL, hR] at hTel
  simpa only [sub_eq_add_neg, add_assoc] using hTel

end FerrersChain

end CSTMicro
end Collatz2
