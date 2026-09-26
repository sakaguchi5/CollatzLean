import CollatzLean.Collatz4.Finite.ForwardSemantics
import CollatzLean.Collatz4.Finite.Witness
import CollatzLean.Collatz4.Targets.M7.ResidualBridge
import CollatzLean.Collatz4.Targets.M7.ForwardReduction

/-!
# Collatz4.Targets.M7.Witness

m=7 の「元の数論的 witness」と有限前向き問題の間に置く意味論層。

この witness は `ResidualData` をそのまま内包しない。
保持するのは、元の残余語から直接得るべき次の事実だけである。

* `q>0`
* 残余語長 `r` の偶数性
* `r ≤ residualTwoExponent q`
* 正確な `G_min/G_max` bound
* `3^(targetTime-r)-1` から目標状態までの1段ずつの forward recurrence

そこから `ResidualData`、有限候補添字、`M7ForwardCandidate` を順に導く。
-/

namespace Collatz4.Targets.M7

open Collatz4.Finite

/--
m=7 の意味論的 witness。

今後、より原始的な指数語・Mersenne block 語彙からこの構造を構成すれば、
有限 certificate までの残りの論理は本ファイル以下で閉じる。
-/
structure M7Witness where
  q : ℕ
  r : ℕ
  q_pos : 0 < q
  r_even : r % 2 = 0
  r_le_residual : r ≤ residualTwoExponent q
  g_lower :
    Collatz4.Finite.residualGMin (residualTwoExponent q) r ≤ gStar
  g_upper :
    gStar ≤ Collatz4.Finite.residualGMax (residualTwoExponent q) r
  recurrence :
    Collatz4.Finite.ResidualRecurrence r
      (ForwardState.ofNat (3 ^ (targetTime - r) - 1))
      targetState

namespace M7Witness

/-- witness から、数値有限化に必要な `ResidualData` を構成する。 -/
def toResidualData (h : M7Witness) : ResidualData where
  q := h.q
  r := h.r
  q_pos := h.q_pos
  r_le_residual := h.r_le_residual
  r_even := h.r_even
  g_bounds := ⟨h.g_lower, h.g_upper⟩

@[simp] theorem toResidualData_q (h : M7Witness) :
    h.toResidualData.q = h.q := rfl

@[simp] theorem toResidualData_r (h : M7Witness) :
    h.toResidualData.r = h.r := rfl

/--
ユーザーが求めた第一 bridge。

`M7Witness` から `ResidualData` が存在し、q と r も保存される。
-/
theorem residualData_of_m7_witness (h : M7Witness) :
    ∃ d : ResidualData, d.q = h.q ∧ d.r = h.r := by
  exact ⟨h.toResidualData, rfl, rfl⟩

/-- 意味論的 recurrence は計算関数 `run` と一致する。 -/
theorem run_to_target (h : M7Witness) :
    run h.r (ForwardState.ofNat (3 ^ (targetTime - h.r) - 1)) = targetState := by
  exact Collatz4.Finite.run_eq_of_residual_recurrence h.recurrence

/--
意味論的 witness は、有限候補列のどれか一つを実際に目標状態へ送る。

数値 bound だけで候補添字を作るのではなく、`recurrence` により
その候補の `finalState` が `targetState` と一致するところまで接続する。
-/
theorem forward_candidate_of_m7_witness (h : M7Witness) :
    M7ForwardCandidate := by
  rcases h.toResidualData.exists_candidateN with ⟨i, hiN⟩
  have hiN' : candidateN i = targetTime - h.r := by
    simpa [M7Witness.toResidualData] using hiN
  have hrle : h.r ≤ targetTime := by
    have hru := h.toResidualData.r_upper
    simp [targetTime] at hru ⊢
    omega
  have hremaining : targetTime - (targetTime - h.r) = h.r := by
    omega
  apply (m7ForwardCandidate_iff).2
  refine ⟨i, ?_⟩
  unfold finalState remainingSteps initialState initialA
  rw [hiN']
  rw [hremaining]
  exact h.run_to_target

end M7Witness

/-- 要求された公開名: `M7Witness` から `ResidualData` を得る。 -/
theorem residualData_of_m7_witness (h : M7Witness) :
    ∃ d : ResidualData, d.q = h.q ∧ d.r = h.r :=
  h.residualData_of_m7_witness

/-- 要求された公開名: `M7Witness` から reduced forward candidate を得る。 -/
theorem forward_candidate_of_m7_witness (h : M7Witness) :
    M7ForwardCandidate :=
  h.forward_candidate_of_m7_witness

/-- m=7 の意味論的 witness が少なくとも一つ存在する、という命題。 -/
def HasM7Witness : Prop :=
  Nonempty M7Witness

/-- `HasM7Witness` から reduced finite candidate への reduction。 -/
theorem hasM7Witness_reducesTo :
    Collatz4.Finite.ReducesTo HasM7Witness forwardProblem := by
  intro h
  rcases h with ⟨w⟩
  exact w.forward_candidate_of_m7_witness

end Collatz4.Targets.M7
