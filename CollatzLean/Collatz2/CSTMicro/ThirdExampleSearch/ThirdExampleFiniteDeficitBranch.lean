import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleLongWidthBranchPruning
set_option linter.style.nativeDecide false
/-!
# 第3例探索: 最後41列の完全有限枝

`ThirdExampleLast41TailCoordinates` から既に得られている

* `r + d ≤ 41`
* `w + 1 ≤ d`

だけを使い、位相 checkpoint に依存しない完全な `(r,d,w)` 有限領域を作る。
長幅22/23だけに絞らないため、actual-phase certification をこの層では要求しない。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

/-- 最後41列で許される `(r,d,w)` の純粋な有限枝条件。 -/
def ThirdExampleFiniteDeficitBranch
    (B : ThirdExampleRDW) : Prop :=
  B.r + B.d ≤ 41 ∧
    B.w + 1 ≤ B.d

instance instDecidableThirdExampleFiniteDeficitBranch :
    DecidablePred ThirdExampleFiniteDeficitBranch := by
  intro B
  unfold ThirdExampleFiniteDeficitBranch
  infer_instance

/--
`r,d,w` を安全な小直方体に一度載せる。
後段の filter が exact な last-41 条件だけを残す。
-/
def thirdExampleFiniteDeficitUniverse : List ThirdExampleRDW :=
  (List.range 42).flatMap (fun r =>
    (List.range 42).flatMap (fun d =>
      (List.range 41).map (fun w =>
        { r := r, d := d, w := w })))

/-- `native_decide` が走る完全な last-41 branch list。 -/
def thirdExampleFiniteDeficitBranches : List ThirdExampleRDW :=
  thirdExampleFiniteDeficitUniverse.filter
    (fun B => decide (ThirdExampleFiniteDeficitBranch B))

/-- last-41 条件を満たす枝は小直方体の中に必ず入る。 -/
theorem thirdExampleFiniteDeficitUniverse_mem_of_branch
    (B : ThirdExampleRDW)
    (hB : ThirdExampleFiniteDeficitBranch B) :
    B ∈ thirdExampleFiniteDeficitUniverse := by
  rcases B with ⟨r, d, w⟩
  rcases hB with ⟨hrd, hwd⟩
  change r + d ≤ 41 at hrd
  change w + 1 ≤ d at hwd
  simp [thirdExampleFiniteDeficitUniverse]
  omega

/-- finite list の membership は数学的 branch 条件と exact に一致する。 -/
theorem thirdExampleFiniteDeficitBranches_mem_iff
    (B : ThirdExampleRDW) :
    B ∈ thirdExampleFiniteDeficitBranches ↔
      ThirdExampleFiniteDeficitBranch B := by
  constructor
  · intro h
    have h' :
        B ∈ thirdExampleFiniteDeficitUniverse ∧
          decide (ThirdExampleFiniteDeficitBranch B) = true := by
      simpa [thirdExampleFiniteDeficitBranches] using h
    exact of_decide_eq_true h'.2
  · intro hB
    have hU := thirdExampleFiniteDeficitUniverse_mem_of_branch B hB
    have hD : decide (ThirdExampleFiniteDeficitBranch B) = true :=
      decide_eq_true hB
    simp only [thirdExampleFiniteDeficitBranches, List.mem_filter, hU, hD, and_self]

/-- actual last-41 座標を executable `(r,d,w)` へ忘却する。 -/
def thirdExampleRDWOfLast41
    (B : ThirdExampleLast41TailCoordinates) : ThirdExampleRDW :=
  { r := B.r, d := B.d, w := B.w }

/-- actual last-41 座標は完全有限枝条件を満たす。 -/
theorem thirdExampleRDWOfLast41_isBranch
    (B : ThirdExampleLast41TailCoordinates) :
    ThirdExampleFiniteDeficitBranch (thirdExampleRDWOfLast41 B) := by
  constructor
  · exact thirdExampleLast41_r_add_d_le_41 B
  · exact B.attached_width

/-- actual last-41 座標は必ず finite verifier の list に現れる。 -/
theorem thirdExampleRDWOfLast41_mem
    (B : ThirdExampleLast41TailCoordinates) :
    thirdExampleRDWOfLast41 B ∈ thirdExampleFiniteDeficitBranches := by
  rw [thirdExampleFiniteDeficitBranches_mem_iff]
  exact thirdExampleRDWOfLast41_isBranch B

/--
完全 finite domain の枝数は exact に 12,341。
これは proof term を巨大化させず native evaluator に計算させる。
-/
theorem thirdExampleFiniteDeficitBranches_length :
    thirdExampleFiniteDeficitBranches.length = 12_341 := by
  native_decide

end ThirdExampleSearch
end CSTMicro
end Collatz2
