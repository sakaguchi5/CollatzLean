import CollatzLean.Collatz3.Experimental2.OstrowskiCanonicalArithmetic

/-!
# Collatz3 Experimental2: semi-normalized infinite Sturmian graph

Epifanio--Frougny--Gabriele--Mignosi--Shallit (2012) の Definition 6 に現れる
semi-normalized infinite Sturmian graph `G'(α)` の、continued-fraction / Ostrowski
weight 側だけを抽象化した薄い実装。

現行 repo の `UnitOstrowskiWeightSystem` は

* `a n` : 第 `n` block の幅（partial quotient / digit upper bound）、
* `Q n` : 第 `n` Sturmian arc weight、

をすでに持つ。したがって新しい continued-fraction data は保存しない。

論文の

`b_s = a_0 + ... + a_s`

に対応する `sturmianBoundary W s` を作り、状態 `i` が第 `h` block

`[b_{h-1}, b_h)`

に属するとき、二本の outgoing arc

* `i -> i+1`      weight `Q h`,
* `i -> b_h + 1`  weight `Q (h+1)`

だけを許す。

このファイルでは graph 自体と weighted path の最小 API だけを置く。
2012 年 Theorem 42/47 の counting / lazy-representation 一意性は、
この graph を土台にした後段 bridge で扱う。
-/

namespace Collatz3
namespace Experimental2
namespace GenericRecordFerrers

/--
論文の `b_h = Σ_{j=0}^h a_j` に対応する Sturmian block の右端。
-/
def sturmianBoundary
    (W : UnitOstrowskiWeightSystem) : ℕ → ℕ
  | 0 => W.a 0
  | n + 1 => sturmianBoundary W n + W.a (n + 1)

/--
第 `h` Sturmian block の左端。`h=0` では初期状態 `0`、
`h+1` では直前 boundary `b_h`。
-/
def sturmianBlockStart
    (W : UnitOstrowskiWeightSystem) : ℕ → ℕ
  | 0 => 0
  | n + 1 => sturmianBoundary W n

@[simp] theorem sturmianBoundary_zero
    (W : UnitOstrowskiWeightSystem) :
    sturmianBoundary W 0 = W.a 0 := rfl

@[simp] theorem sturmianBoundary_succ
    (W : UnitOstrowskiWeightSystem)
    (n : ℕ) :
    sturmianBoundary W (n + 1) =
      sturmianBoundary W n + W.a (n + 1) := rfl

@[simp] theorem sturmianBlockStart_zero
    (W : UnitOstrowskiWeightSystem) :
    sturmianBlockStart W 0 = 0 := rfl

@[simp] theorem sturmianBlockStart_succ
    (W : UnitOstrowskiWeightSystem)
    (n : ℕ) :
    sturmianBlockStart W (n + 1) = sturmianBoundary W n := rfl

/-- 第 `h` block の長さは exact に `a h`。 -/
theorem sturmianBoundary_eq_blockStart_add
    (W : UnitOstrowskiWeightSystem)
    (h : ℕ) :
    sturmianBoundary W h = sturmianBlockStart W h + W.a h := by
  cases h with
  | zero => simp
  | succ n => simp [sturmianBoundary, sturmianBlockStart]

/-- partial quotient が正なので、各 block は空でない。 -/
theorem sturmianBlockStart_lt_boundary
    (W : UnitOstrowskiWeightSystem)
    (h : ℕ) :
    sturmianBlockStart W h < sturmianBoundary W h := by
  rw [sturmianBoundary_eq_blockStart_add]
  have ha := W.a_pos h
  omega

/-- Sturmian boundary は一段ごとに真に右へ進む。 -/
theorem sturmianBoundary_lt_succ
    (W : UnitOstrowskiWeightSystem)
    (h : ℕ) :
    sturmianBoundary W h < sturmianBoundary W (h + 1) := by
  rw [sturmianBoundary_succ]
  have ha := W.a_pos (h + 1)
  omega

/-- Sturmian boundary 列は strict monotone。 -/
theorem sturmianBoundary_strictMono
    (W : UnitOstrowskiWeightSystem) :
    StrictMono (sturmianBoundary W) := by
  exact strictMono_nat_of_lt_succ (sturmianBoundary_lt_succ W)

/-- `b_h` は少なくとも `h+1`。したがって boundary は無限遠へ進む。 -/
theorem index_succ_le_sturmianBoundary
    (W : UnitOstrowskiWeightSystem) :
    ∀ h : ℕ, h + 1 ≤ sturmianBoundary W h := by
  intro h
  induction h with
  | zero =>
      have ha := W.a_pos 0
      simp [sturmianBoundary]
      omega
  | succ h ih =>
      rw [sturmianBoundary_succ]
      have ha := W.a_pos (h + 1)
      omega

/-- 任意の状態番号 `i` より右に Sturmian boundary が存在する。 -/
theorem exists_sturmianBoundary_gt
    (W : UnitOstrowskiWeightSystem)
    (i : ℕ) :
    ∃ h : ℕ, i < sturmianBoundary W h := by
  refine ⟨i, ?_⟩
  have h := index_succ_le_sturmianBoundary W i
  omega

/--
semi-normalized infinite Sturmian graph の weighted arc。

`h` block 内の状態 `i` から、論文 Definition 6 の二本の arc をそのまま生成する。
後段で arc の種類と level をデータとして読むため、arc certificate は `Type` に置く。
-/
inductive IsSturmianArc
    (W : UnitOstrowskiWeightSystem) : ℕ → ℕ → ℕ → Type
  | short {h i : ℕ}
      (hLo : sturmianBlockStart W h ≤ i)
      (hHi : i < sturmianBoundary W h) :
      IsSturmianArc W i (i + 1) (W.Q h)
  | jump {h i : ℕ}
      (hLo : sturmianBlockStart W h ≤ i)
      (hHi : i < sturmianBoundary W h) :
      IsSturmianArc W i (sturmianBoundary W h + 1) (W.Q (h + 1))

namespace IsSturmianArc

/-- すべての Sturmian arc は状態番号を真に増加させる。 -/
theorem source_lt_target
    {W : UnitOstrowskiWeightSystem}
    {i j w : ℕ}
    (A : IsSturmianArc W i j w) :
    i < j := by
  cases A with
  | short hLo hHi => omega
  | jump hLo hHi => omega

/-- すべての Sturmian arc weight は正。 -/
theorem weight_pos
    {W : UnitOstrowskiWeightSystem}
    {i j w : ℕ}
    (A : IsSturmianArc W i j w) :
    0 < w := by
  cases A with
  | short hLo hHi => exact W.q_pos _
  | jump hLo hHi => exact W.q_pos _

/-- arc weight は必ず Ostrowski weight 列 `Q` の一要素。 -/
theorem weight_eq_some_Q
    {W : UnitOstrowskiWeightSystem}
    {i j w : ℕ}
    (A : IsSturmianArc W i j w) :
    ∃ h : ℕ, w = W.Q h := by
  cases A with
  | short hLo hHi => exact ⟨_, rfl⟩
  | jump hLo hHi => exact ⟨_, rfl⟩

end IsSturmianArc

/--
Sturmian graph 上の有限 directed path。

始点・終点に加えて総 weight も型 index に持たせる。
これにより path weight の整合性を別 theorem / field として保存しない。
-/
inductive SturmianPath
    (W : UnitOstrowskiWeightSystem) : ℕ → ℕ → ℕ → Type
  | nil (v : ℕ) : SturmianPath W v v 0
  | cons {u v z w total : ℕ}
      (edge : IsSturmianArc W u v w)
      (tail : SturmianPath W v z total) :
      SturmianPath W u z (w + total)

/--
初期状態 `0` から始まり、総 weight が `N` である Sturmian path の certificate。

2012 年 Theorem 42 の counting property を形式化するときの公開 target type として使う。
-/
structure InitialSturmianPathOfWeight
    (W : UnitOstrowskiWeightSystem)
    (N : ℕ) where
  terminal : ℕ
  path : SturmianPath W 0 terminal N

/-- weight `0` には空 path がある。 -/
def zeroInitialSturmianPath
    (W : UnitOstrowskiWeightSystem) :
    InitialSturmianPathOfWeight W 0 where
  terminal := 0
  path := SturmianPath.nil 0

end GenericRecordFerrers
end Experimental2
end Collatz3
