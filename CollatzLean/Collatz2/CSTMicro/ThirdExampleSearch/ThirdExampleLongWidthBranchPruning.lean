import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleLast41TailPruning
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleLongWidthPhaseCheckpoint
import Mathlib.Tactic.NormNum

/-!
# 第3例探索: 幅22/23の `(r,d,w)` 枝表

最後41列の一般不等式

`r + d ≤ 41`, `w + 1 ≤ d`

と long-width phase checkpoint を合成し、次段の Ferrers deficit residue 計算へ
渡す有限 `(r,d,w)` 枝を確定する。

ここでは endpoint compatibility 自体はまだ計算しない。
目的は、その計算が走る有限 domain を proof 付きで固定することである。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

/-- 次段の finite deficit evaluator が受け取る軽量 `(r,d,w)` 座標。 -/
structure ThirdExampleRDW where
  r : ℕ
  d : ℕ
  w : ℕ
  deriving DecidableEq, Repr

/-- 幅23の枝条件。`d ≥ 24` は attached 条件 `w+1 ≤ d` の特殊化。 -/
def ThirdExampleWidth23RD (r d : ℕ) : Prop :=
  ThirdExampleWidth23RCheckpoint r ∧
    24 ≤ d ∧
    r + d ≤ 41

/-- 幅22の枝条件。`d ≥ 23` は attached 条件 `w+1 ≤ d` の特殊化。 -/
def ThirdExampleWidth22RD (r d : ℕ) : Prop :=
  ThirdExampleWidth22RCheckpoint r ∧
    23 ≤ d ∧
    r + d ≤ 41

/-- 一般の最後41列枝を、幅23の有限枝条件へ落とす。 -/
theorem thirdExampleLast41_to_width23RD
    (B : ThirdExampleLast41TailCoordinates)
    (hw : B.w = 23)
    (hr : ThirdExampleWidth23RCheckpoint B.r) :
    ThirdExampleWidth23RD B.r B.d := by
  have hrd := thirdExampleLast41_r_add_d_le_41 B
  have hwidth := B.attached_width
  have hd : 24 ≤ B.d := by
    omega
  exact ⟨hr, hd, hrd⟩

/-- 一般の最後41列枝を、幅22の有限枝条件へ落とす。 -/
theorem thirdExampleLast41_to_width22RD
    (B : ThirdExampleLast41TailCoordinates)
    (hw : B.w = 22)
    (hr : ThirdExampleWidth22RCheckpoint B.r) :
    ThirdExampleWidth22RD B.r B.d := by
  have hrd := thirdExampleLast41_r_add_d_le_41 B
  have hwidth := B.attached_width
  have hd : 23 ≤ B.d := by
    omega
  exact ⟨hr, hd, hrd⟩

/--
幅23では `(r,d)` は二つの閉区間に限られる。

* `r=3`  : `24 ≤ d ≤ 38`
* `r=15` : `24 ≤ d ≤ 26`
-/
theorem thirdExampleWidth23RD_cases
    {r d : ℕ}
    (h : ThirdExampleWidth23RD r d) :
    (r = 3 ∧ 24 ≤ d ∧ d ≤ 38) ∨
    (r = 15 ∧ 24 ≤ d ∧ d ≤ 26) := by
  rcases h with ⟨hr, hd, hsum⟩
  rcases hr with hr | hr
  · left
    constructor
    · exact hr
    constructor
    · exact hd
    · omega
  · right
    constructor
    · exact hr
    constructor
    · exact hd
    · omega

/-- 幅23の二つの閉区間は元の枝条件を満たす。 -/
theorem thirdExampleWidth23RD_of_cases
    {r d : ℕ}
    (h :
      (r = 3 ∧ 24 ≤ d ∧ d ≤ 38) ∨
      (r = 15 ∧ 24 ≤ d ∧ d ≤ 26)) :
    ThirdExampleWidth23RD r d := by
  rcases h with h | h
  · rcases h with ⟨hr, hd0, hd1⟩
    subst r
    refine ⟨?_, hd0, ?_⟩
    · exact Or.inl rfl
    · omega
  · rcases h with ⟨hr, hd0, hd1⟩
    subst r
    refine ⟨?_, hd0, ?_⟩
    · exact Or.inr rfl
    · omega

/-- 幅23枝の exact な区間表示。 -/
theorem thirdExampleWidth23RD_iff
    {r d : ℕ} :
    ThirdExampleWidth23RD r d ↔
      ((r = 3 ∧ 24 ≤ d ∧ d ≤ 38) ∨
       (r = 15 ∧ 24 ≤ d ∧ d ≤ 26)) := by
  constructor
  · exact thirdExampleWidth23RD_cases
  · exact thirdExampleWidth23RD_of_cases

/--
幅22では `(r,d)` は四つの閉区間に限られる。

* `r=3`  : `23 ≤ d ≤ 38`
* `r=7`  : `23 ≤ d ≤ 34`
* `r=9`  : `23 ≤ d ≤ 32`
* `r=15` : `23 ≤ d ≤ 26`
-/
theorem thirdExampleWidth22RD_cases
    {r d : ℕ}
    (h : ThirdExampleWidth22RD r d) :
    (r = 3 ∧ 23 ≤ d ∧ d ≤ 38) ∨
    (r = 7 ∧ 23 ≤ d ∧ d ≤ 34) ∨
    (r = 9 ∧ 23 ≤ d ∧ d ≤ 32) ∨
    (r = 15 ∧ 23 ≤ d ∧ d ≤ 26) := by
  rcases h with ⟨hr, hd, hsum⟩
  rcases hr with hr | hr
  · exact Or.inl ⟨hr, hd, by omega⟩
  rcases hr with hr | hr
  · exact Or.inr (Or.inl ⟨hr, hd, by omega⟩)
  rcases hr with hr | hr
  · exact Or.inr (Or.inr (Or.inl ⟨hr, hd, by omega⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hr, hd, by omega⟩))

/-- 幅22の四つの閉区間は元の枝条件を満たす。 -/
theorem thirdExampleWidth22RD_of_cases
    {r d : ℕ}
    (h :
      (r = 3 ∧ 23 ≤ d ∧ d ≤ 38) ∨
      (r = 7 ∧ 23 ≤ d ∧ d ≤ 34) ∨
      (r = 9 ∧ 23 ≤ d ∧ d ≤ 32) ∨
      (r = 15 ∧ 23 ≤ d ∧ d ≤ 26)) :
    ThirdExampleWidth22RD r d := by
  rcases h with h | h
  · rcases h with ⟨hr, hd0, hd1⟩
    subst r
    refine ⟨?_, hd0, ?_⟩
    · exact Or.inl rfl
    · omega
  rcases h with h | h
  · rcases h with ⟨hr, hd0, hd1⟩
    subst r
    refine ⟨?_, hd0, ?_⟩
    · exact Or.inr (Or.inl rfl)
    · omega
  rcases h with h | h
  · rcases h with ⟨hr, hd0, hd1⟩
    subst r
    refine ⟨?_, hd0, ?_⟩
    · exact Or.inr (Or.inr (Or.inl rfl))
    · omega
  · rcases h with ⟨hr, hd0, hd1⟩
    subst r
    refine ⟨?_, hd0, ?_⟩
    · exact Or.inr (Or.inr (Or.inr rfl))
    · omega

/-- 幅22枝の exact な区間表示。 -/
theorem thirdExampleWidth22RD_iff
    {r d : ℕ} :
    ThirdExampleWidth22RD r d ↔
      ((r = 3 ∧ 23 ≤ d ∧ d ≤ 38) ∨
       (r = 7 ∧ 23 ≤ d ∧ d ≤ 34) ∨
       (r = 9 ∧ 23 ≤ d ∧ d ≤ 32) ∨
       (r = 15 ∧ 23 ≤ d ∧ d ≤ 26)) := by
  constructor
  · exact thirdExampleWidth22RD_cases
  · exact thirdExampleWidth22RD_of_cases

/-- 閉区間 `[lo,hi]` を固定 `(r,w)` の `(r,d,w)` list にする。 -/
def thirdExampleRDWInterval
    (r w lo hi : ℕ) : List ThirdExampleRDW :=
  (List.range (hi + 1 - lo)).map
    (fun i => { r := r, d := lo + i, w := w })

/-- 幅23で次段へ渡す18本の executable branch list。 -/
def thirdExampleWidth23Branches : List ThirdExampleRDW :=
  thirdExampleRDWInterval 3 23 24 38 ++
  thirdExampleRDWInterval 15 23 24 26

/-- 幅22で次段へ渡す42本の executable branch list。 -/
def thirdExampleWidth22Branches : List ThirdExampleRDW :=
  thirdExampleRDWInterval 3 22 23 38 ++
  thirdExampleRDWInterval 7 22 23 34 ++
  thirdExampleRDWInterval 9 22 23 32 ++
  thirdExampleRDWInterval 15 22 23 26

/-- 長幅22/23をまとめた60本の branch list。 -/
def thirdExampleLongWidthBranches : List ThirdExampleRDW :=
  thirdExampleWidth23Branches ++ thirdExampleWidth22Branches

/-- 幅23の枝数は `15+3=18`。 -/
theorem thirdExampleWidth23Branches_length :
    thirdExampleWidth23Branches.length = 18 := by
  norm_num [thirdExampleWidth23Branches, thirdExampleRDWInterval]

/-- 幅22の枝数は `16+12+10+4=42`。 -/
theorem thirdExampleWidth22Branches_length :
    thirdExampleWidth22Branches.length = 42 := by
  norm_num [thirdExampleWidth22Branches, thirdExampleRDWInterval]

/-- 幅22/23を合わせた長幅枝は exact に60本。 -/
theorem thirdExampleLongWidthBranches_length :
    thirdExampleLongWidthBranches.length = 60 := by
  simp [
    thirdExampleLongWidthBranches,
    thirdExampleWidth23Branches_length,
    thirdExampleWidth22Branches_length
  ]

/-- 直前に誤記した `43` ではなく、幅22の区間 cardinality は42。 -/
theorem thirdExampleWidth22_interval_count_checkpoint :
    (38 - 23 + 1) + (34 - 23 + 1) +
      (32 - 23 + 1) + (26 - 23 + 1) = 42 := by
  norm_num

/-- 幅23の区間 cardinality は18。 -/
theorem thirdExampleWidth23_interval_count_checkpoint :
    (38 - 24 + 1) + (26 - 24 + 1) = 18 := by
  norm_num

/-- よって長幅22/23の合計は `42+18=60`。 -/
theorem thirdExampleLongWidth_interval_count_checkpoint :
    42 + 18 = 60 := by
  norm_num

end ThirdExampleSearch
end CSTMicro
end Collatz2
