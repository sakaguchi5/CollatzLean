import CollatzLean.Collatz2.CSTMicro.CarryGeometry.FerrersStepRankTopLedger
import CollatzLean.Collatz2.CSTMicro.CarryGeometry.RankTopWinding

set_option linter.style.longLine false

/-!
# Rank-top chain winding ledger

one-step law

  ΔJnum = G * (lambda - 3*carry)

を Ferrers chain 全体へ telescope する。

各 step の `lambda` と carry indicator は List trace として保持し、

  Jnum(finish)
    = Jnum(start)
      + G * (sum lambdaTrace - 3 * sum carryTrace)

を得る。

FirstFailureProvenance の boundary -> first-failure upper に適用すると、
`RankTopWinding.exists_rankTopWinding` の final winding `nB` に対して

  nB = jA + sum lambdaTrace - 3 * sum carryTrace

となる boundary winding `jA : ℤ` が存在する。

この telescope 自体は cell residue の符号を仮定しない。
一方 `lambda ∈ {0,1,2,3}` は既存 `LocalRankTopLedger` の通り
`0 < residue`（equivalently `0 < C < G`）の cell で成立するので、
chain 全 cell に finite alphabet を要求する条件は別 predicate として明示する。
-/

namespace Collatz2
namespace CSTMicro

namespace IsFirstPassageWord

/-- standard first-passage word と odd-only encoding は terminal gap も一致する。 -/
theorem exponentWordOfParity_terminalGap_eq_wordTerminalGap
    {v : ParityWord}
    (hFP : IsFirstPassageWord v)
    (hLen : 1 < v.length) :
    Collatz2.Word.terminalGap (exponentWordOfParity v) =
      wordTerminalGap v := by
  unfold Collatz2.Word.terminalGap wordTerminalGap
  rw [hFP.twoSteps_exponentWordOfParity_eq_length hLen]
  rw [oddSteps_exponentWordOfParity]

end IsFirstPassageWord

namespace FerrersStep

/-- carry indicator 自身は常に binary alphabet。 -/
theorem normalizedCarryIndicator_cases
    {lower upper : ParityWord}
    (S : FerrersStep lower upper) :
    S.normalizedCarryIndicator = 0 ∨
      S.normalizedCarryIndicator = 1 := by
  classical
  unfold normalizedCarryIndicator
  by_cases h : S.edge.HasCarry
  · rw [if_pos h]
    exact Or.inr rfl
  · rw [if_neg h]
    exact Or.inl rfl

end FerrersStep

namespace FerrersChain
open FerrersStep
/-- chain の lambda 総和。 -/
noncomputable def rankTopLambdaSum
    {start finish : ParityWord} :
    FerrersChain start finish → ℕ
  | .refl _ => 0
  | .step C S => C.rankTopLambdaSum + S.actualRankTopLambda

/-- cell-by-cell lambda trace。 -/
noncomputable def rankTopLambdaTrace
    {start finish : ParityWord} :
    FerrersChain start finish → List ℕ
  | .refl _ => []
  | .step C S => C.rankTopLambdaTrace ++ [S.actualRankTopLambda]

/-- cell-by-cell carry indicator trace。 -/
noncomputable def rankTopCarryTrace
    {start finish : ParityWord} :
    FerrersChain start finish → List ℕ
  | .refl _ => []
  | .step C S => C.rankTopCarryTrace ++ [S.normalizedCarryIndicator]

/-- lambda trace の総和は chain の rank-top lambda 総和に一致する。 -/
theorem rankTopLambdaTrace_sum_eq_rankTopLambdaSum
    {start finish : ParityWord}
    (C : FerrersChain start finish) :
    C.rankTopLambdaTrace.sum = C.rankTopLambdaSum := by
  induction C with
  | refl =>
      simp [rankTopLambdaTrace, rankTopLambdaSum]
  | step C S ih =>
      simp [rankTopLambdaTrace, rankTopLambdaSum, ih]


/-- carry indicator trace の総和は chain の carry step 数に一致する。 -/
theorem rankTopCarryTrace_sum_eq_normalizedCarryCount
    {start finish : ParityWord}
    (C : FerrersChain start finish) :
    C.rankTopCarryTrace.sum = C.normalizedCarryCount := by
  induction C with
  | refl =>
      simp [rankTopCarryTrace, normalizedCarryCount]
  | step C S ih =>
      simp [rankTopCarryTrace, normalizedCarryCount, ih]

/-- 全 step の Farey residue が正であるという明示条件。 -/
def AllPositiveCellResidues
    {start finish : ParityWord} :
    FerrersChain start finish → Prop
  | .refl _ => True
  | .step C S =>
      C.AllPositiveCellResidues ∧
        0 < S.edge.toFareyCellPacket.residue

@[simp] theorem rankTopLambdaTrace_sum
    {start finish : ParityWord}
    (C : FerrersChain start finish) :
    C.rankTopLambdaTrace.sum = C.rankTopLambdaSum := by
  induction C with
  | refl =>
      simp [rankTopLambdaTrace, rankTopLambdaSum]
  | @step u v C S ih =>
      simp [rankTopLambdaTrace, rankTopLambdaSum, ih]

@[simp] theorem rankTopCarryTrace_sum
    {start finish : ParityWord}
    (C : FerrersChain start finish) :
    C.rankTopCarryTrace.sum = C.normalizedCarryCount := by
  induction C with
  | refl =>
      simp [rankTopCarryTrace, normalizedCarryCount]
  | @step u v C S ih =>
      simp [rankTopCarryTrace, normalizedCarryCount, ih]

/-- carry trace の各 entry は `0/1`。 -/
theorem rankTopCarryTrace_entry_cases
    {start finish : ParityWord}
    (C : FerrersChain start finish)
    {x : ℕ}
    (hx : x ∈ C.rankTopCarryTrace) :
    x = 0 ∨ x = 1 := by
  induction C with
  | refl =>
      simp [rankTopCarryTrace] at hx
  | @step u v C S ih =>
      simp only [rankTopCarryTrace, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | hx
      · exact ih hx
      · subst x
        exact S.normalizedCarryIndicator_cases

/--
全 cell residue が正なら lambda trace の各 entry は `{0,1,2,3}`。

finite alphabet が必要な箇所だけこの条件を使う。
-/
theorem rankTopLambdaTrace_entry_cases_of_allPositiveResidues
    {start finish : ParityWord}
    (C : FerrersChain start finish)
    (hStartFP : IsFirstPassageWord start)
    (hPos : C.AllPositiveCellResidues)
    {x : ℕ}
    (hx : x ∈ C.rankTopLambdaTrace) :
    x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by
  induction C with
  | refl =>
      simp [rankTopLambdaTrace] at hx
  | @step u v C S ih =>
      rcases hPos with ⟨hPosC, hPosS⟩
      have hUFP : IsFirstPassageWord u :=
        C.preserves_firstPassage hStartFP
      simp only [rankTopLambdaTrace, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | hx
      · exact ih hPosC hx
      · subst x
        exact S.actualRankTopLambda_cases_of_residue_pos hUFP hPosS

/--
rank-top numerator の chain telescope。

proof 引数は Prop proof irrelevance により endpoint value に影響しないため、
start / finish の任意の first-passage proof を許す。
-/
theorem parityRankTopNumerator_telescope
    {start finish : ParityWord}
    (C : FerrersChain start finish)
    (hStartFP : IsFirstPassageWord start)
    (hStartLen : 1 < start.length)
    (hFinishFP : IsFirstPassageWord finish)
    (hFinishLen : 1 < finish.length) :
    parityRankTopNumerator finish hFinishFP hFinishLen =
      parityRankTopNumerator start hStartFP hStartLen +
        (wordTerminalGap start : ℤ) *
          ((C.rankTopLambdaSum : ℤ) -
            3 * (C.normalizedCarryCount : ℤ)) := by
  revert hFinishFP hFinishLen
  induction C with
  | refl =>
      intro hFinishFP hFinishLen
      have hProof :=
        parityRankTopNumerator_proof_irrel
          start hFinishFP hStartFP hFinishLen hStartLen
      rw [hProof]
      simp [rankTopLambdaSum, normalizedCarryCount]
  | @step u v C S ih =>
      intro hFinishFP hFinishLen
      have hUFP : IsFirstPassageWord u :=
        C.preserves_firstPassage hStartFP
      have hULen : 1 < u.length := by
        rw [← C.length_eq]
        exact hStartLen
      have hIH := ih hUFP hULen
      have hStepRaw := S.parityRankTopNumerator_step hUFP hULen
      let hVFP0 : IsFirstPassageWord v :=
        Eq.mp (congrArg IsFirstPassageWord S.upper_eq.symm)
          (S.edge_upper_firstPassage_of_lower hUFP)
      let hVLen0 : 1 < v.length := by
        rw [← S.length_eq]
        exact hULen
      have hStep0 :
          parityRankTopNumerator v hVFP0 hVLen0 =
            parityRankTopNumerator u hUFP hULen +
              (wordTerminalGap u : ℤ) *
                ((S.actualRankTopLambda : ℤ) -
                  3 * (S.normalizedCarryIndicator : ℤ)) := by
        simpa [hVFP0, hVLen0] using hStepRaw
      have hFinishProof :=
        parityRankTopNumerator_proof_irrel
          v hFinishFP hVFP0 hFinishLen hVLen0
      have hStep :
          parityRankTopNumerator v hFinishFP hFinishLen =
            parityRankTopNumerator u hUFP hULen +
              (wordTerminalGap u : ℤ) *
                ((S.actualRankTopLambda : ℤ) -
                  3 * (S.normalizedCarryIndicator : ℤ)) := by
        rw [hFinishProof]
        exact hStep0
      have hGap : wordTerminalGap u = wordTerminalGap start :=
        C.wordTerminalGap_eq.symm
      change
        parityRankTopNumerator v hFinishFP hFinishLen =
          parityRankTopNumerator start hStartFP hStartLen +
            (wordTerminalGap start : ℤ) *
              (((C.rankTopLambdaSum + S.actualRankTopLambda : ℕ) : ℤ) -
                3 *
                  (((C.normalizedCarryCount + S.normalizedCarryIndicator : ℕ) : ℤ)))
      rw [hStep, hIH, hGap]
      push_cast
      ring

/-- trace を明示した同じ telescope。 -/
theorem parityRankTopNumerator_telescope_trace
    {start finish : ParityWord}
    (C : FerrersChain start finish)
    (hStartFP : IsFirstPassageWord start)
    (hStartLen : 1 < start.length)
    (hFinishFP : IsFirstPassageWord finish)
    (hFinishLen : 1 < finish.length) :
    parityRankTopNumerator finish hFinishFP hFinishLen =
      parityRankTopNumerator start hStartFP hStartLen +
        (wordTerminalGap start : ℤ) *
          ((C.rankTopLambdaTrace.sum : ℤ) -
            3 * (C.rankTopCarryTrace.sum : ℤ)) := by
  rw [C.rankTopLambdaTrace_sum, C.rankTopCarryTrace_sum]
  exact
    C.parityRankTopNumerator_telescope
      hStartFP hStartLen hFinishFP hFinishLen

end FerrersChain
open FerrersStep
namespace FirstFailureProvenance

/-- boundary から distinguished first-failure upper までの exact Ferrers chain。 -/
def boundaryToUpperRankTopChain
    {target : ParityWord}
    (P : FirstFailureProvenance target) :
    FerrersChain P.boundary P.upper :=
  FerrersChain.step
    P.safePrefixChain.toFerrersChain
    P.failureStep

/-- boundary -> failure upper の lambda trace。 -/
noncomputable def boundaryToUpperLambdaTrace
    {target : ParityWord}
    (P : FirstFailureProvenance target) : List ℕ :=
  P.boundaryToUpperRankTopChain.rankTopLambdaTrace

/-- boundary -> failure upper の carry trace。 -/
noncomputable def boundaryToUpperCarryTrace
    {target : ParityWord}
    (P : FirstFailureProvenance target) : List ℕ :=
  P.boundaryToUpperRankTopChain.rankTopCarryTrace

/-- boundary -> upper chain の terminal gap は endpoint 間で不変。 -/
theorem boundaryToUpper_wordTerminalGap_eq
    {target : ParityWord}
    (P : FirstFailureProvenance target) :
    wordTerminalGap P.boundary = wordTerminalGap P.upper :=
  P.boundaryToUpperRankTopChain.wordTerminalGap_eq

/-- 語が等しければ、対応する FirstCrossing proof で計算した rankTopSum も等しい。 -/
theorem Word.rankTopSum_congr
    {w₁ w₂ : Collatz2.Word}
    (hw : w₁ = w₂)
    (hF₁ : Collatz2.Word.FirstCrossing w₁)
    (hF₂ : Collatz2.Word.FirstCrossing w₂) :
    Collatz2.Word.rankTopSum hF₁ =
      Collatz2.Word.rankTopSum hF₂ := by
  subst w₂
  have hProof : hF₁ = hF₂ := Subsingleton.elim _ _
  rw [hProof]

/--
first-failure final winding `nB` を upper rank-top numerator の
terminal-gap normal form へ変換する。

  N_upper = G_boundary * nB.
-/
theorem exists_rankTopWinding_upper_normal_form
    {target : ParityWord}
    (P : FirstFailureProvenance target)
    (hLen : 2 < P.upper.length)
    (hUpperLen : 1 < P.upper.length) :
    ∃ nB : ℕ,
      1 ≤ nB ∧
      nB < Collatz2.Word.oddSteps P.toFirstFailureEdge.upperExponentWord ∧
      parityRankTopNumerator
          P.upper
          P.upper_firstPassage
          hUpperLen =
        (wordTerminalGap P.boundary : ℤ) * (nB : ℤ) := by
  let F := P.toFirstFailureEdge
  have hFLen : 2 < F.step.edge.upperWord.length := by
    have hEq := congrArg List.length P.failureStep.upper_eq
    change P.upper.length = F.step.edge.upperWord.length at hEq
    rw [← hEq]
    exact hLen
  obtain ⟨nB, hnPos, hnLt, hWind⟩ :=
    F.exists_rankTopWinding hFLen
  have hEdgeUpper : F.step.edge.upperWord = P.upper := by
    change P.failureStep.edge.upperWord = P.upper
    exact P.failureStep.upper_eq.symm
  have hExp :
      F.upperExponentWord = exponentWordOfParity P.upper :=
    congrArg exponentWordOfParity hEdgeUpper
  have hTopEq :
      Collatz2.Word.rankTopSum F.upperExponentWord_firstCrossing =
        parityRankTopSum P.upper P.upper_firstPassage hUpperLen := by
    unfold parityRankTopSum
    exact Word.rankTopSum_congr
      hExp
      F.upperExponentWord_firstCrossing
      (P.upper_firstPassage.exponentWordOfParity_firstCrossing hUpperLen)
  have hGapExp :
      Collatz2.Word.terminalGap F.upperExponentWord =
        wordTerminalGap P.boundary := by
    calc
      Collatz2.Word.terminalGap F.upperExponentWord
          = Collatz2.Word.terminalGap (exponentWordOfParity P.upper) :=
            congrArg Collatz2.Word.terminalGap hExp
      _ = wordTerminalGap P.upper :=
            P.upper_firstPassage.exponentWordOfParity_terminalGap_eq_wordTerminalGap
              hUpperLen
      _ = wordTerminalGap P.boundary :=
            P.boundaryToUpper_wordTerminalGap_eq.symm
  have hQ :
      (F.upperNormalizedDefectNat : ℤ) =
        normalizedSeparationDefectInt P.upper := by
    calc
      (F.upperNormalizedDefectNat : ℤ)
          = normalizedSeparationDefectInt F.step.edge.upperWord :=
            F.upperNormalizedDefectNat_cast
      _ = normalizedSeparationDefectInt P.upper :=
            congrArg normalizedSeparationDefectInt hEdgeUpper
  have hWindZ := congrArg (fun n : ℕ => (n : ℤ)) hWind
  push_cast at hWindZ
  rw [hTopEq, hGapExp, hQ] at hWindZ
  have hFinalNumerator :
      parityRankTopNumerator
          P.upper P.upper_firstPassage hUpperLen =
        (wordTerminalGap P.boundary : ℤ) * (nB : ℤ) := by
    unfold parityRankTopNumerator
    rw [hWindZ]
    ring
  refine ⟨nB, hnPos, ?_, hFinalNumerator⟩
  simpa [F] using hnLt


/--
upper rank-top numerator の winding normal form を、
boundary-to-upper cell trace に沿って boundary numerator へ引き戻す。

  N_upper = G * nB

から

  N_boundary = G * jA,
  nB = jA + sum(lambdaTrace) - 3*sum(carryTrace)

を得る。
-/
theorem exists_boundaryWinding_of_upper_normal_form
    {target : ParityWord}
    (P : FirstFailureProvenance target)
    (hBoundaryLen : 1 < P.boundary.length)
    (hUpperLen : 1 < P.upper.length)
    {nB : ℕ}
    (hFinalNumerator :
      parityRankTopNumerator
          P.upper P.upper_firstPassage hUpperLen =
        (wordTerminalGap P.boundary : ℤ) * (nB : ℤ)) :
    ∃ jA : ℤ,
      parityRankTopNumerator
          P.boundary
          P.boundary_isBoundary.1
          hBoundaryLen =
        (wordTerminalGap P.boundary : ℤ) * jA
      ∧
      (nB : ℤ) =
        jA + (P.boundaryToUpperLambdaTrace.sum : ℤ) -
          3 * (P.boundaryToUpperCarryTrace.sum : ℤ) := by
  let C := P.boundaryToUpperRankTopChain
  have hChain :=
    C.parityRankTopNumerator_telescope_trace
      P.boundary_isBoundary.1
      hBoundaryLen
      P.upper_firstPassage
      hUpperLen
  let delta : ℤ :=
    (C.rankTopLambdaSum : ℤ) -
      3 * (C.normalizedCarryCount : ℤ)
  let jA : ℤ := (nB : ℤ) - delta
  have hStart :
      parityRankTopNumerator
          P.boundary
          P.boundary_isBoundary.1
          hBoundaryLen =
        (wordTerminalGap P.boundary : ℤ) * jA := by
    rw [hFinalNumerator] at hChain
    have hChain' :
        (wordTerminalGap P.boundary : ℤ) * (nB : ℤ) =
          parityRankTopNumerator
              P.boundary
              P.boundary_isBoundary.1
              hBoundaryLen +
            (wordTerminalGap P.boundary : ℤ) * delta := by
      simpa [C, delta] using hChain
    have hRearrange :
        parityRankTopNumerator
            P.boundary
            P.boundary_isBoundary.1
            hBoundaryLen =
          (wordTerminalGap P.boundary : ℤ) * (nB : ℤ) -
            (wordTerminalGap P.boundary : ℤ) * delta := by
      linarith [hChain']
    rw [hRearrange]
    dsimp [jA]
    ring
  have hnEq :
      (nB : ℤ) =
        jA + (P.boundaryToUpperLambdaTrace.sum : ℤ) -
          3 * (P.boundaryToUpperCarryTrace.sum : ℤ) := by
    dsimp [jA, delta]
    rw [
      boundaryToUpperLambdaTrace,
      boundaryToUpperCarryTrace,
      FerrersChain.rankTopLambdaTrace_sum_eq_rankTopLambdaSum,
      FerrersChain.rankTopCarryTrace_sum_eq_normalizedCarryCount
    ]
    ring
  exact ⟨jA, hStart, hnEq⟩


/--
first-failure final winding `nB` を boundary winding と cell trace へ lift した normal form。

  nB = jA + sum(lambdaTrace) - 3*sum(carryTrace).

同時に boundary numerator 自身が `G*jA` であることも保持する。
-/
theorem exists_rankTopWinding_with_boundary_trace
    {target : ParityWord}
    (P : FirstFailureProvenance target)
    (hLen : 2 < P.upper.length) :
    ∃ nB : ℕ,
      1 ≤ nB ∧
      nB < Collatz2.Word.oddSteps P.toFirstFailureEdge.upperExponentWord ∧
      ∃ jA : ℤ,
        parityRankTopNumerator
            P.boundary
            P.boundary_isBoundary.1
            (by
              have hC := P.boundaryToUpperRankTopChain.length_eq
              rw [hC]
              omega) =
          (wordTerminalGap P.boundary : ℤ) * jA
        ∧
        (nB : ℤ) =
          jA + (P.boundaryToUpperLambdaTrace.sum : ℤ) -
            3 * (P.boundaryToUpperCarryTrace.sum : ℤ) := by
  let C := P.boundaryToUpperRankTopChain
  have hBoundaryLen : 1 < P.boundary.length := by
    have hEq := C.length_eq
    rw [hEq]
    omega
  have hUpperLen : 1 < P.upper.length := by
    omega
  obtain ⟨nB, hnPos, hnLt, hFinalNumerator⟩ :=
    exists_rankTopWinding_upper_normal_form
      P hLen hUpperLen
  obtain ⟨jA, hStart, hnEq⟩ :=
    exists_boundaryWinding_of_upper_normal_form
      P hBoundaryLen hUpperLen hFinalNumerator
  refine ⟨nB, hnPos, hnLt, jA, ?_, hnEq⟩
  have hProof :=
    parityRankTopNumerator_proof_irrel
      P.boundary
      P.boundary_isBoundary.1
      P.boundary_isBoundary.1
      (by
        have hC := P.boundaryToUpperRankTopChain.length_eq
        rw [hC]
        omega)
      hBoundaryLen
  rw [hProof]
  exact hStart

/--
全 A->B cell residue が正である場合、上の boundary trace の lambda は全て finite alphabet。
この条件は telescope 本体には不要であり、現在の repo から無条件には仮定しない。
-/
theorem boundaryToUpper_lambdaTrace_entry_cases_of_allPositiveResidues
    {target : ParityWord}
    (P : FirstFailureProvenance target)
    (hPos : P.boundaryToUpperRankTopChain.AllPositiveCellResidues)
    {x : ℕ}
    (hx : x ∈ P.boundaryToUpperLambdaTrace) :
    x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by
  unfold boundaryToUpperLambdaTrace at hx
  exact
    P.boundaryToUpperRankTopChain.rankTopLambdaTrace_entry_cases_of_allPositiveResidues
      P.boundary_isBoundary.1 hPos hx

/-- boundary -> upper carry trace は無条件に binary alphabet。 -/
theorem boundaryToUpper_carryTrace_entry_cases
    {target : ParityWord}
    (P : FirstFailureProvenance target)
    {x : ℕ}
    (hx : x ∈ P.boundaryToUpperCarryTrace) :
    x = 0 ∨ x = 1 := by
  unfold boundaryToUpperCarryTrace at hx
  exact P.boundaryToUpperRankTopChain.rankTopCarryTrace_entry_cases hx

end FirstFailureProvenance

end CSTMicro
end Collatz2
