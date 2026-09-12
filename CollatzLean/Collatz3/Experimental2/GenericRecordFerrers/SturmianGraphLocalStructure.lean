import CollatzLean.Collatz3.Experimental2.GenericRecordFerrers.SturmianGraph

import Mathlib.Tactic.Ring

/-!
# Collatz3 Experimental2: Sturmian graph の局所構造と Proposition 12 / 13

Epifanio--Frougny--Gabriele--Mignosi--Shallit (2012) の
semi-normalized Sturmian graph `G'(α)` について、後段の lazy Ostrowski bridge に
必要な局所構造を、現行 `UnitOstrowskiWeightSystem` 上で証明する。

このファイルの中心は次の二点。

* Proposition 12 型：ある block を一度に飛び越える arc は、その block の
  左端から右端の一つ先へ進む jump arc に限る。
* Proposition 13 型：任意 path に現れる第 `h` weight の arc 本数は `a h` 以下。
  初期状態 `0` から第 `h` boundary まで到達する path では、その本数は exact に `a h`。

証明では graph state `i` が第 `h` block をどこまで進んだかを
`sturmianProgress W h i` として測る。
第 `h` weight の arc はこの progress を exactly `1` 増やす一方、
第 `h+1` jump だけが第 `h` block の残りを一度に飛び越えられる。
この観察が Proposition 13 と、後段の lazy 条件を同じ算術にまとめる。
-/

namespace Collatz3
namespace Experimental2
namespace GenericRecordFerrers

/-- boundary の weak monotonicity。 -/
theorem sturmianBoundary_mono
    (W : UnitOstrowskiWeightSystem) :
    Monotone (sturmianBoundary W) :=
  (sturmianBoundary_strictMono W).monotone

/-- より左の block の boundary は、より右の block の start 以下。 -/
theorem sturmianBoundary_le_blockStart_of_lt
    (W : UnitOstrowskiWeightSystem)
    {k h : ℕ}
    (hkh : k < h) :
    sturmianBoundary W k ≤ sturmianBlockStart W h := by
  cases h with
  | zero => omega
  | succ h =>
      rw [sturmianBlockStart_succ]
      exact sturmianBoundary_mono W (by omega)

/-- block start はその boundary 以下。 -/
theorem sturmianBlockStart_le_boundary
    (W : UnitOstrowskiWeightSystem)
    (h : ℕ) :
    sturmianBlockStart W h ≤ sturmianBoundary W h :=
  Nat.le_of_lt (sturmianBlockStart_lt_boundary W h)

namespace IsSturmianArc

/--
arc が担う Ostrowski / Sturmian weight index。
short arc は現在 block `h`、jump arc は次 weight `h+1` を担う。
-/
def level
    {W : UnitOstrowskiWeightSystem}
    {i j w : ℕ} :
    IsSturmianArc W i j w → ℕ
  | .short (h := h) _ _ => h
  | .jump (h := h) _ _ => h + 1

/-- arc weight は `level` の Ostrowski weight そのもの。 -/
theorem weight_eq_Q_level
    {W : UnitOstrowskiWeightSystem}
    {i j w : ℕ}
    (A : IsSturmianArc W i j w) :
    w = W.Q A.level := by
  cases A <;> rfl

/--
level `h` の arc の target は、第 `h` target block
`(blockStart h, boundary h]` の中に入る。

これは論文 Proposition 10 のうち、後段で必要な target 側の exact 形。
-/
theorem target_mem_levelBlock
    {W : UnitOstrowskiWeightSystem}
    {i j w : ℕ}
    (A : IsSturmianArc W i j w) :
    sturmianBlockStart W A.level < j ∧
      j ≤ sturmianBoundary W A.level := by
  cases A with
  | @short h i hLo hHi =>
      constructor
      · change sturmianBlockStart W h < i + 1
        omega
      · change i + 1 ≤ sturmianBoundary W h
        omega
  | @jump h i hLo hHi =>
      constructor
      · change
          sturmianBlockStart W (h + 1) <
            sturmianBoundary W h + 1
        rw [sturmianBlockStart_succ]
        omega
      · change
          sturmianBoundary W h + 1 ≤
            sturmianBoundary W (h + 1)
        rw [sturmianBoundary_succ]
        have ha := W.a_pos (h + 1)
        omega

/--
異なる level の target blocks は交わらない。
従って arc target が第 `h` target block に入れば、その arc level は `h` に一意。
-/
theorem level_eq_of_target_mem
    {W : UnitOstrowskiWeightSystem}
    {i j w h : ℕ}
    (A : IsSturmianArc W i j w)
    (hLo : sturmianBlockStart W h < j)
    (hHi : j ≤ sturmianBoundary W h) :
    A.level = h := by
  rcases A.target_mem_levelBlock with ⟨aLo, aHi⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hb := sturmianBoundary_le_blockStart_of_lt W hlt
    omega
  · have hb := sturmianBoundary_le_blockStart_of_lt W hgt
    omega

/--
2012 Proposition 12 の index-shift を吸収した exact 形。

第 `h` block の `blockStart h + 1` より左から出て、`boundary h` より右へ
一度に抜ける arc は、`blockStart h` から `boundary h + 1` への jump だけ。
-/
theorem proposition12_crossing_arc
    {W : UnitOstrowskiWeightSystem}
    {i j w h : ℕ}
    (A : IsSturmianArc W i j w)
    (hSource : i < sturmianBlockStart W h + 1)
    (hTarget : sturmianBoundary W h < j) :
    i = sturmianBlockStart W h ∧
      j = sturmianBoundary W h + 1 := by
  have hSourceLe : i ≤ sturmianBlockStart W h := by omega
  cases A with
  | @short k i hLo hHi =>
      have hStartLt := sturmianBlockStart_lt_boundary W h
      omega
  | @jump k i hLo hHi =>
      by_cases hkh : k < h
      · have hb : sturmianBoundary W k < sturmianBoundary W h :=
          sturmianBoundary_strictMono W hkh
        omega
      · by_cases hhk : h < k
        · have hb := sturmianBoundary_le_blockStart_of_lt W hhk
          have hStartLt := sturmianBlockStart_lt_boundary W h
          omega
        · have hk : k = h := by omega
          subst k
          have hi : i = sturmianBlockStart W h := by omega
          exact ⟨hi, rfl⟩

end IsSturmianArc

/--
state `i` が第 `h` block をどこまで進んだかを `0..a h` に切り詰めた座標。
-/
def sturmianProgress
    (W : UnitOstrowskiWeightSystem)
    (h i : ℕ) : ℕ :=
  if i ≤ sturmianBlockStart W h then
    0
  else if i ≤ sturmianBoundary W h then
    i - sturmianBlockStart W h
  else
    W.a h

@[simp] theorem sturmianProgress_zero_state
    (W : UnitOstrowskiWeightSystem)
    (h : ℕ) :
    sturmianProgress W h 0 = 0 := by
  simp [sturmianProgress]

/-- progress は常に `a h` 以下。 -/
theorem sturmianProgress_le
    (W : UnitOstrowskiWeightSystem)
    (h i : ℕ) :
    sturmianProgress W h i ≤ W.a h := by
  by_cases h0 : i ≤ sturmianBlockStart W h
  · simp [sturmianProgress, h0]
  · by_cases h1 : i ≤ sturmianBoundary W h
    · rw [sturmianProgress, ite_eq_right h0, ite_eq_left h1]
      rw [sturmianBoundary_eq_blockStart_add] at h1
      omega
    · simp [sturmianProgress, h0, h1]

/-- block start 以前では progress は `0`。 -/
theorem sturmianProgress_eq_zero_of_le_start
    (W : UnitOstrowskiWeightSystem)
    {h i : ℕ}
    (hi : i ≤ sturmianBlockStart W h) :
    sturmianProgress W h i = 0 := by
  simp [sturmianProgress, hi]

/-- boundary 以後では progress は最大値 `a h`。boundary 自身も含む。 -/
theorem sturmianProgress_eq_a_of_boundary_le
    (W : UnitOstrowskiWeightSystem)
    {h i : ℕ}
    (hi : sturmianBoundary W h ≤ i) :
    sturmianProgress W h i = W.a h := by
  have hStartLt := sturmianBlockStart_lt_boundary W h
  have hNotStart : ¬ i ≤ sturmianBlockStart W h := by
    omega
  by_cases hLe : i ≤ sturmianBoundary W h
  · have hEq : i = sturmianBoundary W h := by
      omega
    subst i
    rw [sturmianProgress, ite_eq_right hNotStart, ite_eq_left le_rfl]
    rw [sturmianBoundary_eq_blockStart_add]
    omega
  · rw [sturmianProgress, ite_eq_right hNotStart, ite_eq_right hLe]

/-- progress は state とともに減らない。 -/
theorem sturmianProgress_mono
    (W : UnitOstrowskiWeightSystem)
    (h : ℕ) :
    Monotone (sturmianProgress W h) := by
  intro i j hij
  by_cases hi0 : i ≤ sturmianBlockStart W h
  · simp [sturmianProgress, hi0]
  · have hj0 : ¬ j ≤ sturmianBlockStart W h := by omega
    by_cases hj1 : j ≤ sturmianBoundary W h
    · have hi1 : i ≤ sturmianBoundary W h := le_trans hij hj1
      simp [sturmianProgress, hi0, hj0, hi1, hj1]
      omega
    · by_cases hi1 : i ≤ sturmianBoundary W h
      · rw [sturmianProgress, ite_eq_right hi0, ite_eq_left hi1,
          sturmianProgress, ite_eq_right hj0, ite_eq_right hj1]
        rw [sturmianBoundary_eq_blockStart_add] at hi1
        omega
      · simp [sturmianProgress, hi0, hj0, hi1, hj1]

namespace IsSturmianArc

/--
任意 arc について、第 `h` progress の増加量は
「その arc が level `h` なら 1、そうでなければ 0」以上。

jump `h -> h+1` は残り block を一度に飛び越えるので、そこだけ増加量が 1 より大きくなり得る。
-/
theorem indicator_le_progress_change
    {W : UnitOstrowskiWeightSystem}
    {i j w h : ℕ}
    (A : IsSturmianArc W i j w) :
    (if A.level = h then 1 else 0) ≤
      sturmianProgress W h j - sturmianProgress W h i := by
  cases A with
  | @short k i hLo hHi =>
      by_cases hk : k = h
      · subst k
        have hs : ¬ i + 1 ≤ sturmianBlockStart W h := by
          omega
        have ht : i + 1 ≤ sturmianBoundary W h := by
          omega
        by_cases hi : i ≤ sturmianBlockStart W h
        · have hieq : i = sturmianBlockStart W h := by
            omega
          subst i
          simp [IsSturmianArc.level, sturmianProgress, ht]
        · have hi1 : i ≤ sturmianBoundary W h := by
            exact Nat.le_of_lt hHi
          simp [IsSturmianArc.level, sturmianProgress, hi, hs, ht, hi1]
          omega
      · have hmono := sturmianProgress_mono W h (Nat.le_succ i)
        simp [IsSturmianArc.level, hk]
  | @jump k i hLo hHi =>
      by_cases hk : k + 1 = h
      · have hk0 : 0 < h := by omega
        have hStart : sturmianBoundary W k = sturmianBlockStart W h := by
          cases h with
          | zero => omega
          | succ h =>
              have : k = h := by omega
              subst k
              rfl
        have hi0 : i ≤ sturmianBlockStart W h := by
          rw [← hStart]
          omega
        have ht0 : ¬ sturmianBoundary W k + 1 ≤ sturmianBlockStart W h := by
          rw [← hStart]
          omega
        have ht1 : sturmianBoundary W k + 1 ≤ sturmianBoundary W h := by
          rw [hStart, sturmianBoundary_eq_blockStart_add]
          have ha := W.a_pos h
          omega
        simp [IsSturmianArc.level, hk, sturmianProgress, hi0, ht0, ht1]
        omega
      · have hmono :=
          sturmianProgress_mono W h (by omega : i ≤ sturmianBoundary W k + 1)
        simp [IsSturmianArc.level, hk]

/--
level `h+1` の arc を使わない場合、progress 増加量は indicator と exact に一致する。
これは lazy 条件の核心となる局所式。
-/
theorem progress_change_eq_indicator_of_not_next
    {W : UnitOstrowskiWeightSystem}
    {i j w h : ℕ}
    (A : IsSturmianArc W i j w)
    (hNext : A.level ≠ h + 1) :
    sturmianProgress W h j - sturmianProgress W h i =
      (if A.level = h then 1 else 0) := by
  cases A with
  | @short k i hLo hHi =>
      by_cases hk : k = h
      · subst k
        have hs : ¬ i + 1 ≤ sturmianBlockStart W h := by
          omega
        have ht : i + 1 ≤ sturmianBoundary W h := by
          omega
        by_cases hi : i ≤ sturmianBlockStart W h
        · have hieq : i = sturmianBlockStart W h := by
            omega
          subst i
          simp [IsSturmianArc.level, sturmianProgress, ht]
        · have hi1 : i ≤ sturmianBoundary W h := by
            exact Nat.le_of_lt hHi
          simp [IsSturmianArc.level, sturmianProgress, hi, hs, ht, hi1]
          omega
      · by_cases hkh : k < h
        · have hb := sturmianBoundary_le_blockStart_of_lt W hkh
          have hu : i + 1 ≤ sturmianBlockStart W h := by omega
          have hi : i ≤ sturmianBlockStart W h := by omega
          rw [sturmianProgress_eq_zero_of_le_start W hi,
            sturmianProgress_eq_zero_of_le_start W hu]
          simp [IsSturmianArc.level, hk]
        · have hhk : h < k := by omega
          have hb := sturmianBoundary_le_blockStart_of_lt W hhk
          have hi : sturmianBoundary W h ≤ i := by omega
          have hj : sturmianBoundary W h ≤ i + 1 := by omega
          rw [sturmianProgress_eq_a_of_boundary_le W hi,
            sturmianProgress_eq_a_of_boundary_le W hj]
          simp [IsSturmianArc.level, hk]
  | @jump k i hLo hHi =>
      have hkNext : k + 1 ≠ h + 1 := by
        simpa [IsSturmianArc.level] using hNext
      by_cases hk : k + 1 = h
      · have hStart : sturmianBoundary W k = sturmianBlockStart W h := by
          cases h with
          | zero => omega
          | succ h =>
              have : k = h := by omega
              subst k
              rfl
        have hi0 : i ≤ sturmianBlockStart W h := by
          rw [← hStart]
          omega
        have ht0 : ¬ sturmianBoundary W k + 1 ≤ sturmianBlockStart W h := by
          rw [← hStart]
          omega
        have ht1 : sturmianBoundary W k + 1 ≤ sturmianBoundary W h := by
          rw [hStart, sturmianBoundary_eq_blockStart_add]
          have ha := W.a_pos h
          omega
        simp [IsSturmianArc.level, hk, sturmianProgress, hi0, ht0, ht1]
        omega
      · by_cases hkh : k + 1 < h
        · have hb := sturmianBoundary_le_blockStart_of_lt W hkh
          have hi : i ≤ sturmianBlockStart W h := by
            have hib : i < sturmianBoundary W k := hHi
            have hbk : sturmianBoundary W k ≤ sturmianBoundary W (k + 1) :=
              sturmianBoundary_mono W (by omega)
            omega
          have hStep :
              sturmianBoundary W k + 1 ≤ sturmianBoundary W (k + 1) := by
            rw [sturmianBoundary_succ]
            have ha := W.a_pos (k + 1)
            omega
          have hj :
              sturmianBoundary W k + 1 ≤ sturmianBlockStart W h := by
            exact le_trans hStep hb
          simp [IsSturmianArc.level, hk, sturmianProgress, hi, hj]
        · have hgt : h < k := by omega
          have hb := sturmianBoundary_le_blockStart_of_lt W hgt
          have hi : sturmianBoundary W h ≤ i := by omega
          have hj : sturmianBoundary W h ≤ sturmianBoundary W k + 1 := by
            have hm := sturmianBoundary_mono W (show h ≤ k by omega)
            omega
          rw [sturmianProgress_eq_a_of_boundary_le W hi,
            sturmianProgress_eq_a_of_boundary_le W hj]
          simp [IsSturmianArc.level, hk]

end IsSturmianArc

namespace SturmianPath

/-- path 中で level `h` の arc が現れる本数。 -/
def edgeCount
    {W : UnitOstrowskiWeightSystem}
    {u z N : ℕ} :
    SturmianPath W u z N → ℕ → ℕ
  | .nil _, _ => 0
  | .cons edge tail, h =>
      (if edge.level = h then 1 else 0) + tail.edgeCount h

/-- path の全 arc level より真に大きい有限 bound。 -/
def levelBound
    {W : UnitOstrowskiWeightSystem}
    {u z N : ℕ} :
    SturmianPath W u z N → ℕ
  | .nil _ => 0
  | .cons edge tail => max (edge.level + 1) tail.levelBound

/-- path の始点は終点以下。 -/
theorem source_le_terminal
    {W : UnitOstrowskiWeightSystem}
    {u z N : ℕ}
    (P : SturmianPath W u z N) :
    u ≤ z := by
  induction P with
  | nil => exact le_rfl
  | cons edge tail ih =>
      exact le_trans (Nat.le_of_lt edge.source_lt_target) ih

/-- bound 以上の level は path に現れない。 -/
theorem edgeCount_eq_zero_of_levelBound_le
    {W : UnitOstrowskiWeightSystem}
    {u z N h : ℕ}
    (P : SturmianPath W u z N)
    (hh : P.levelBound ≤ h) :
    P.edgeCount h = 0 := by
  induction P with
  | nil => rfl
  | cons edge tail ih =>
      have he : edge.level ≠ h := by
        simp [levelBound] at hh
        omega
      have ht : tail.levelBound ≤ h := by
        simp [levelBound] at hh
        omega
      simp [edgeCount, he, ih ht]

/--
edgeCount が正なら、その level の target block より終点は右にある。
-/
theorem terminal_gt_boundary_of_edgeCount_pos
    {W : UnitOstrowskiWeightSystem}
    {u z N r h : ℕ}
    (P : SturmianPath W u z N)
    (hc : 0 < P.edgeCount r)
    (hhr : h < r) :
    sturmianBoundary W h < z := by
  induction P with
  | nil =>
      simp [edgeCount] at hc
  | @cons u v z w total edge tail ih =>
      by_cases he : edge.level = r
      · have ht := edge.target_mem_levelBlock
        have ht' :
            sturmianBlockStart W r < v ∧
              v ≤ sturmianBoundary W r := by
          simpa [he] using ht
        have hb :
            sturmianBoundary W h ≤ sturmianBlockStart W r :=
          sturmianBoundary_le_blockStart_of_lt W hhr
        have hz : v ≤ z := tail.source_le_terminal
        exact lt_of_lt_of_le
          (lt_of_le_of_lt hb ht'.1)
          hz
      · have hcTail : 0 < tail.edgeCount r := by
          simpa [edgeCount, he] using hc
        exact ih hcTail

/--
任意 path で level `h` arc 本数は第 `h` progress の総増加量以下。
-/
theorem edgeCount_le_progress_change
    {W : UnitOstrowskiWeightSystem}
    {u z N h : ℕ}
    (P : SturmianPath W u z N) :
    P.edgeCount h ≤
      sturmianProgress W h z - sturmianProgress W h u := by
  induction P with
  | nil => simp [edgeCount]
  | cons edge tail ih =>
      have hLocal := edge.indicator_le_progress_change (h := h)
      have hmono1 := sturmianProgress_mono W h (Nat.le_of_lt edge.source_lt_target)
      have hmono2 := sturmianProgress_mono W h tail.source_le_terminal
      simp only [edgeCount]
      omega

/--
path に level `h+1` arc が一本もなければ、level `h` 本数は progress 増加量と exact に一致。
-/
theorem edgeCount_eq_progress_change_of_next_zero
    {W : UnitOstrowskiWeightSystem}
    {u z N h : ℕ}
    (P : SturmianPath W u z N)
    (hZero : P.edgeCount (h + 1) = 0) :
    P.edgeCount h =
      sturmianProgress W h z - sturmianProgress W h u := by
  induction P with
  | nil => simp [edgeCount]
  | cons edge tail ih =>
      have heNext : edge.level ≠ h + 1 := by
        intro he
        simp [edgeCount, he] at hZero
      have hTailZero : tail.edgeCount (h + 1) = 0 := by
        by_cases he : edge.level = h + 1
        · exact False.elim (heNext he)
        · simpa [edgeCount, he] using hZero
      have hLocal := edge.progress_change_eq_indicator_of_not_next
        (h := h) heNext
      have hTail := ih hTailZero
      have hmono1 := sturmianProgress_mono W h (Nat.le_of_lt edge.source_lt_target)
      have hmono2 := sturmianProgress_mono W h tail.source_le_terminal
      simp only [edgeCount]
      omega

/--
2012 Proposition 13 前半。
任意 path に現れる level `h` arc は高々 `a h` 本。
-/
theorem proposition13_edgeCount_le
    {W : UnitOstrowskiWeightSystem}
    {u z N h : ℕ}
    (P : SturmianPath W u z N) :
    P.edgeCount h ≤ W.a h := by
  exact le_trans P.edgeCount_le_progress_change
    (by
      have hz := sturmianProgress_le W h z
      omega)

/--
2012 Proposition 13 後半。
初期状態から第 `h` boundary に到達する path は level `h` arc を exact に `a h` 本含む。
-/
theorem proposition13_edgeCount_eq_of_terminal_boundary
    {W : UnitOstrowskiWeightSystem}
    {N h : ℕ}
    (P : SturmianPath W 0 (sturmianBoundary W h) N) :
    P.edgeCount h = W.a h := by
  have hNextZero : P.edgeCount (h + 1) = 0 := by
    by_contra hne
    have hp : 0 < P.edgeCount (h + 1) := Nat.pos_of_ne_zero hne
    have hgt := P.terminal_gt_boundary_of_edgeCount_pos hp (by omega : h < h + 1)
    omega
  have hEq := P.edgeCount_eq_progress_change_of_next_zero hNextZero
  have hProgEnd :
      sturmianProgress W h (sturmianBoundary W h) = W.a h :=
    sturmianProgress_eq_a_of_boundary_le W le_rfl
  rw [hProgEnd, sturmianProgress_zero_state] at hEq
  simpa using hEq

/-- levelBound が正なら、その最上位 level は path に実際に現れる。 -/
theorem edgeCount_top_pos
    {W : UnitOstrowskiWeightSystem}
    {u z N : ℕ}
    (P : SturmianPath W u z N)
    (hPos : 0 < P.levelBound) :
    0 < P.edgeCount (P.levelBound - 1) := by
  induction P with
  | nil => simp [levelBound] at hPos
  | cons edge tail ih =>
      by_cases hle : tail.levelBound ≤ edge.level + 1
      · have hMax :
            max (edge.level + 1) tail.levelBound =
              edge.level + 1 :=
          Nat.max_eq_left hle
        have hTop :
            (SturmianPath.cons edge tail).levelBound - 1 =
              edge.level := by
          change
            max (edge.level + 1) tail.levelBound - 1 =
              edge.level
          rw [hMax]
          omega
        rw [hTop]
        change
          0 <
            (if edge.level = edge.level then 1 else 0) +
              tail.edgeCount edge.level
        simp
      · have hlt : edge.level + 1 < tail.levelBound := by omega
        have hMax : max (edge.level + 1) tail.levelBound = tail.levelBound :=
          Nat.max_eq_right (Nat.le_of_lt hlt)
        have hTailPos : 0 < tail.levelBound := by omega
        have hp := ih hTailPos
        have heNe : edge.level ≠ tail.levelBound - 1 := by omega
        simpa [levelBound, hMax, edgeCount, heNe] using hp


end SturmianPath

/-- prefix weighted sum は digit-wise addition を保つ。 -/
theorem ostrowskiPrefixSum_add_digits
    (w d e : ℕ → ℕ) :
    ∀ t : ℕ,
      ostrowskiPrefixSum w (fun n => d n + e n) t =
        ostrowskiPrefixSum w d t + ostrowskiPrefixSum w e t := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [ostrowskiPrefixSum_succ, ostrowskiPrefixSum_succ,
        ostrowskiPrefixSum_succ, ih]
      ring

/-- 一つの level だけを 1 にした digit の weighted sum。 -/
theorem ostrowskiPrefixSum_singleLevel
    (W : UnitOstrowskiWeightSystem)
    (r t : ℕ) :
    ostrowskiPrefixSum W.Q (fun h => if r = h then 1 else 0) t =
      if r < t then W.Q r else 0 := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [ostrowskiPrefixSum_succ, ih]
      by_cases hrt : r = t
      · subst r
        simp
      · by_cases hrlt : r < t
        · have hrs : r < t + 1 := by omega
          simp [hrt, hrlt, hrs]
        · have hgt : t < r := by omega
          have hrs : ¬ r < t + 1 := by omega
          simp [hrt, hrlt, hrs]

namespace SturmianPath

/-- edgeCount は先頭 arc の singleton digit と tail digit の和。 -/
theorem edgeCount_cons_eq
    {W : UnitOstrowskiWeightSystem}
    {u v z w total h : ℕ}
    (edge : IsSturmianArc W u v w)
    (tail : SturmianPath W v z total) :
    (SturmianPath.cons edge tail).edgeCount h =
      (if edge.level = h then 1 else 0) + tail.edgeCount h := rfl

/--
levelBound 以下の prefix を取れば、path edge-count digits の weighted sumは
path 自身の総 weight と exact に一致する。
-/
theorem edgeCount_value_of_bound_le
    {W : UnitOstrowskiWeightSystem}
    {u z N t : ℕ}
    (P : SturmianPath W u z N)
    (hBound : P.levelBound ≤ t) :
    ostrowskiPrefixSum W.Q P.edgeCount t = N := by
  induction P with
  | nil =>
      induction t with
      | zero =>
          rfl
      | succ t ih =>
          rw [ostrowskiPrefixSum_succ]
          simp only [edgeCount, zero_mul, add_zero]
          exact ih (by simp [levelBound])
  | @cons u v z w total edge tail ih =>
      have he : edge.level < t := by
        simp [levelBound] at hBound
        omega
      have ht : tail.levelBound ≤ t := by
        simp [levelBound] at hBound
        omega
      have hTail := ih ht
      have hAdd := ostrowskiPrefixSum_add_digits W.Q
        (fun h => if edge.level = h then 1 else 0)
        tail.edgeCount t
      have hSingle := ostrowskiPrefixSum_singleLevel W edge.level t
      change
        ostrowskiPrefixSum W.Q
            (fun h => (if edge.level = h then 1 else 0) + tail.edgeCount h) t =
          w + total
      rw [hAdd, hSingle, ite_eq_left he, hTail]
      exact congrArg (fun x : ℕ => x + total) edge.weight_eq_Q_level.symm

/-- path 自身の canonical bound での reconstruction。 -/
theorem edgeCount_value
    {W : UnitOstrowskiWeightSystem}
    {u z N : ℕ}
    (P : SturmianPath W u z N) :
    ostrowskiPrefixSum W.Q P.edgeCount P.levelBound = N :=
  P.edgeCount_value_of_bound_le le_rfl

/--
初期 path の top より下で level `h+1` が欠けるなら、level `h` は最大本数 `a h`。
2012 Proposition 12/13 から Theorem 47 へ進む核心の lazy implication。
-/
theorem lazy_previous_full_of_next_zero
    {W : UnitOstrowskiWeightSystem}
    {z N h : ℕ}
    (P : SturmianPath W 0 z N)
    (hInside : h + 1 < P.levelBound)
    (hZero : P.edgeCount (h + 1) = 0) :
    P.edgeCount h = W.a h := by
  have hBoundPos : 0 < P.levelBound := by omega
  have hTop := P.edgeCount_top_pos hBoundPos
  let r := P.levelBound - 1
  have hrPos : 0 < P.edgeCount r := by simpa [r] using hTop
  have hrGe : h + 1 ≤ r := by
    dsimp [r]
    omega
  have hrNe : r ≠ h + 1 := by
    intro hrEq
    have hPosNext : 0 < P.edgeCount (h + 1) := by
      simpa [hrEq] using hrPos
    rw [hZero] at hPosNext
    omega
  have hrGt : h + 1 < r := by omega
  have hTerminal :=
    P.terminal_gt_boundary_of_edgeCount_pos hrPos (show h < r by omega)
  have hEq := P.edgeCount_eq_progress_change_of_next_zero hZero
  have hProgEnd : sturmianProgress W h z = W.a h := by
    have hS : ¬ z ≤ sturmianBlockStart W h := by
      intro hz
      exact (not_lt_of_ge
        (le_trans hz (sturmianBlockStart_le_boundary W h))) hTerminal
    have hB : ¬ z ≤ sturmianBoundary W h := by omega
    simp [sturmianProgress, hS, hB]
  rw [hProgEnd, sturmianProgress_zero_state] at hEq
  simpa using hEq

end SturmianPath

end GenericRecordFerrers
end Experimental2
end Collatz3
