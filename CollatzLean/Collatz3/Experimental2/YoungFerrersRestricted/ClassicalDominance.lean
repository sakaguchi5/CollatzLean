import CollatzLean.Collatz3.Experimental2.YoungFerrersRestricted.GenuineDurfee
import CollatzLean.Collatz3.Experimental2.YoungFerrersRestricted.Dominance
import Mathlib.Data.List.GetD

/-!
# Collatz3 Experimental2: ColumnDominates と classical partition dominance

古典的な partition dominance は、非増加な part 列 `λ, μ` に対し

  μ₀+...+μ_{k-1} ≤ λ₀+...+λ_{k-1}

を全 `k` で要求する。

この repo の Ferrers shape は「列高」を part 列として保存するため、
既存 `ColumnDominates` はまさにその column partition に対する classical dominance である。

一方、通常の row-length convention は Young 共役を取った column partition なので、
row dominance は conjugate code 上の同じ classical dominance として exact に表せる。

さらに本ファイルでは、同じ cell 数を持つ二つの Young 図形について古典的な

  A dominates B
    ↔
  conjugate B dominates conjugate A

という共役による dominance 反転も証明する。
-/

namespace Collatz3
namespace Experimental2
namespace YoungFerrersRestricted

/-- 任意の自然数 part 列に対する classical dominance。 -/
def ClassicalDominatesList
    (lambda mu : List ℕ) : Prop :=
  ∀ k : ℕ,
    (mu.take k).sum ≤ (lambda.take k).sum

/-- classical dominance は反射的。 -/
theorem classicalDominatesList_refl
    (lambda : List ℕ) :
    ClassicalDominatesList lambda lambda := by
  intro k
  exact Nat.le_refl _

/-- classical dominance は推移的。 -/
theorem classicalDominatesList_trans
    {lambda mu nu : List ℕ}
    (hLM : ClassicalDominatesList lambda mu)
    (hMN : ClassicalDominatesList mu nu) :
    ClassicalDominatesList lambda nu := by
  intro k
  exact le_trans (hMN k) (hLM k)

/-- width-drop code が表す column partition。 -/
def columnPartitionOfCode
    (c : WidthDropCode) : List ℕ :=
  columnListFromWidthDropCode c

/-- genuine Young 共役が表す row partition。 -/
def rowPartitionOfCode
    (c : WidthDropCode) : List ℕ :=
  columnListFromWidthDropCode (conjugateWidthDropCode c)

/--
C の第一の exact relation：`ColumnDominates` は column-height partition 上の
classical dominance そのもの。
-/
theorem columnDominates_iff_classicalDominates_columnPartition
    (A B : WidthDropCode) :
    ColumnDominates A B ↔
      ClassicalDominatesList
        (columnPartitionOfCode A)
        (columnPartitionOfCode B) := by
  rfl

/-- row convention の classical dominance。 -/
def RowClassicalDominates
    (A B : WidthDropCode) : Prop :=
  ClassicalDominatesList
    (rowPartitionOfCode A)
    (rowPartitionOfCode B)

/--
C の第二の exact relation：row dominance は genuine conjugate code 上の
`ColumnDominates` と exact に一致する。
-/
theorem rowClassicalDominates_iff_conjugateColumnDominates
    (A B : WidthDropCode) :
    RowClassicalDominates A B ↔
      ColumnDominates
        (conjugateWidthDropCode A)
        (conjugateWidthDropCode B) := by
  rfl

/--
column convention と row convention は Young 共役を一回挟むだけで相互変換できる。
-/
theorem columnDominates_conjugate_iff_rowClassicalDominates
    (A B : WidthDropCode) :
    ColumnDominates
        (conjugateWidthDropCode A)
        (conjugateWidthDropCode B) ↔
      RowClassicalDominates A B := by
  exact (rowClassicalDominates_iff_conjugateColumnDominates A B).symm

/-- 共役を二回取れば row convention から元の column convention に戻る。 -/
theorem rowClassicalDominates_conjugate_iff_columnDominates
    (A B : WidthDropCode) :
    RowClassicalDominates
        (conjugateWidthDropCode A)
        (conjugateWidthDropCode B) ↔
      ColumnDominates A B := by
  rw [rowClassicalDominates_iff_conjugateColumnDominates]
  simp

/-!
## 共役による dominance 反転

以下では classical dominance の共役反転を、現在の column code だけで証明する。
証明の中心は二つである。

1. 高さ `cut` で各列を切った下側面積 `truncatedMass`。
2. 高さ `cut` より上に残る面積 `excessMass`。

同面積ならこの二つは補数関係にある。dominance は上側 excess を一方向に比較し、
genuine Young 共役は下側 truncated mass を prefix mass に変える。
-/

/-- 各 part を高さ `cut` で切った下側の総面積。 -/
def truncatedMass (cut : ℕ) : List ℕ → ℕ
  | [] => 0
  | x :: xs => min cut x + truncatedMass cut xs

/-- 高さ `cut` より上に残る総面積。 -/
def excessMass (cut : ℕ) : List ℕ → ℕ
  | [] => 0
  | x :: xs => (x - cut) + excessMass cut xs

/-- 下側面積と上側 excess の和は元の総和。 -/
theorem truncatedMass_add_excessMass
    (cut : ℕ) :
    ∀ xs : List ℕ,
      truncatedMass cut xs + excessMass cut xs = xs.sum
  | [] => by
      rfl
  | x :: xs => by
      simp only [truncatedMass, excessMass, List.sum_cons]
      have hMin : min cut x + (x - cut) = x := by
        omega
      rw [← truncatedMass_add_excessMass cut xs]
      omega

/-- 任意 prefix の総和は、全 excess と `cut × prefix length` で上から抑えられる。 -/
theorem sum_take_le_excessMass_add
    (cut : ℕ) :
    ∀ (xs : List ℕ) (k : ℕ),
      (xs.take k).sum ≤ excessMass cut xs + cut * k
  | [], k => by
      simp [excessMass]
  | x :: xs, 0 => by
      simp [excessMass]
  | x :: xs, k + 1 => by
      simp only [List.take_succ_cons, List.sum_cons, excessMass]
      have hTail := sum_take_le_excessMass_add cut xs k
      have hx : x ≤ (x - cut) + cut := by
        omega
      calc
        x + (xs.take k).sum
            ≤ ((x - cut) + cut) +
                (excessMass cut xs + cut * k) :=
              Nat.add_le_add hx hTail
        _ = (x - cut) + excessMass cut xs + cut * (k + 1) := by
              rw [Nat.mul_succ]
              omega

/-- 非増加 part 列を head/tail の順序条件だけで持つ薄い predicate。 -/
def NonincreasingList : List ℕ → Prop
  | [] => True
  | x :: xs =>
      (∀ y ∈ xs, y ≤ x) ∧ NonincreasingList xs

/-- `repeatValue` に現れる値はすべて反復値そのもの。 -/
theorem eq_of_mem_repeatValue :
    ∀ {n h x : ℕ},
      x ∈ repeatValue n h → x = h
  | 0, h, x, hx => by
      simp [repeatValue] at hx
  | n + 1, h, x, hx => by
      simp only [repeatValue_succ, List.mem_cons] at hx
      rcases hx with rfl | hx
      · rfl
      · exact eq_of_mem_repeatValue hx

/-- width-drop code の任意の列高は全 drop sum 以下。 -/
theorem mem_columnList_le_dropSum :
    ∀ (c : WidthDropCode) {x : ℕ},
      x ∈ columnListFromWidthDropCode c →
        x ≤ codeDropSum c
  | [], x, hx => by
      simp [columnListFromWidthDropCode] at hx
  | (r, d) :: cs, x, hx => by
      simp only [columnListFromWidthDropCode, List.mem_append] at hx
      rcases hx with hx | hx
      · have hxEq : x = d + codeDropSum cs :=
          eq_of_mem_repeatValue hx
        subst x
        simp [codeDropSum, dropsOfCode]
      · have hTail := mem_columnList_le_dropSum cs hx
        rw [codeDropSum_cons]
        omega

/--
非増加 tail の前に、それ以上の一定高さを `n` 本付けても非増加性は保たれる。
-/
theorem nonincreasing_repeatValue_append
    (n h : ℕ)
    (xs : List ℕ)
    (hMono : NonincreasingList xs)
    (hBound : ∀ y ∈ xs, y ≤ h) :
    NonincreasingList (repeatValue n h ++ xs) := by
  induction n with
  | zero =>
      simpa [repeatValue] using hMono
  | succ n ih =>
      simp only [repeatValue_succ, List.cons_append, NonincreasingList]
      refine ⟨?_, ih⟩
      intro y hy
      simp only [List.mem_append] at hy
      rcases hy with hy | hy
      · have hyEq : y = h := eq_of_mem_repeatValue hy
        omega
      · exact hBound y hy

/-- width-drop code が表す column partition は非増加。 -/
theorem columnListFromWidthDropCode_nonincreasing :
    ∀ c : WidthDropCode,
      NonincreasingList (columnListFromWidthDropCode c)
  | [] => by
      trivial
  | (r, d) :: cs => by
      simp only [columnListFromWidthDropCode]
      apply nonincreasing_repeatValue_append
      · exact columnListFromWidthDropCode_nonincreasing cs
      · intro y hy
        have hTail := mem_columnList_le_dropSum cs hy
        omega

/-- cut より大きい part が先頭から何個続くか。非増加列では全 positive excess の幅になる。 -/
def abovePrefixLength (cut : ℕ) : List ℕ → ℕ
  | [] => 0
  | x :: xs =>
      if cut < x then
        1 + abovePrefixLength cut xs
      else
        0

/-- 全 part が `cut` 以下なら excess は `0`。 -/
theorem excessMass_eq_zero_of_forall_le
    (cut : ℕ) :
    ∀ (xs : List ℕ),
      (∀ x ∈ xs, x ≤ cut) →
      excessMass cut xs = 0
  | [], _h => by
      rfl
  | x :: xs, h => by
      have hx : x ≤ cut := h x (by simp)
      have hTail : ∀ y ∈ xs, y ≤ cut := by
        intro y hy
        exact h y (by simp [hy])
      simp [excessMass, Nat.sub_eq_zero_of_le hx,
        excessMass_eq_zero_of_forall_le cut xs hTail]

/--
非増加列では、cut より上にある part は先頭に連続する。
その prefix sum は `excess + cut × width` に exact に等しい。
-/
theorem sum_take_abovePrefixLength_eq_excessMass_add
    (cut : ℕ) :
    ∀ (xs : List ℕ),
      NonincreasingList xs →
      (xs.take (abovePrefixLength cut xs)).sum =
        excessMass cut xs + cut * abovePrefixLength cut xs
  | [], _hMono => by
      rfl
  | x :: xs, hMono => by
      rcases hMono with ⟨hHead, hTailMono⟩
      by_cases hx : cut < x
      · simp only [abovePrefixLength, hx, ite_eq_left, excessMass]
        rw [Nat.one_add]
        simp only [List.take_succ_cons, List.sum_cons]
        rw [
          sum_take_abovePrefixLength_eq_excessMass_add
            cut xs hTailMono
        ]
        have hxEq : x = (x - cut) + cut := by
          omega
        rw [hxEq, Nat.mul_succ]
        omega
      · have hxLe : x ≤ cut := le_of_not_gt hx
        have hTailLe : ∀ y ∈ xs, y ≤ cut := by
          intro y hy
          exact le_trans (hHead y hy) hxLe
        have hTailZero :=
          excessMass_eq_zero_of_forall_le cut xs hTailLe
        simp [abovePrefixLength, hx, excessMass,
          Nat.sub_eq_zero_of_le hxLe, hTailZero]

/--
classical dominance は、被 dominance 側が非増加なら全 cut で excess を逆向きに比較する。
-/
theorem excessMass_le_of_classicalDominates
    {lambda mu : List ℕ}
    (hMonoMu : NonincreasingList mu)
    (hDom : ClassicalDominatesList lambda mu)
    (cut : ℕ) :
    excessMass cut mu ≤ excessMass cut lambda := by
  let t := abovePrefixLength cut mu
  have hMu :=
    sum_take_abovePrefixLength_eq_excessMass_add cut mu hMonoMu
  have hDomT := hDom t
  have hLambda := sum_take_le_excessMass_add cut lambda t
  have hChain :
      excessMass cut mu + cut * t ≤
        excessMass cut lambda + cut * t := by
    calc
      excessMass cut mu + cut * t
          = (mu.take t).sum := by
              simpa [t] using hMu.symm
      _ ≤ (lambda.take t).sum := hDomT
      _ ≤ excessMass cut lambda + cut * t := hLambda
  exact le_of_add_le_add_right hChain

/--
同面積の partition では dominance により truncated mass は逆向きに比較される。
-/
theorem truncatedMass_le_of_classicalDominates_of_sum_eq
    {lambda mu : List ℕ}
    (hMonoMu : NonincreasingList mu)
    (hDom : ClassicalDominatesList lambda mu)
    (hSum : lambda.sum = mu.sum)
    (cut : ℕ) :
    truncatedMass cut lambda ≤ truncatedMass cut mu := by
  have hEx := excessMass_le_of_classicalDominates hMonoMu hDom cut
  have hLambda := truncatedMass_add_excessMass cut lambda
  have hMu := truncatedMass_add_excessMass cut mu
  omega

/-- `repeatValue` は標準 `List.replicate` と一致する。 -/
@[simp] theorem repeatValue_eq_replicate
    (n h : ℕ) :
    repeatValue n h = List.replicate n h := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [repeatValue, ih]
      rfl

/-- column list の `getD` は code の列高関数と exact に一致する。 -/
theorem getD_columnListFromWidthDropCode :
    ∀ (c : WidthDropCode) (k : ℕ),
      (columnListFromWidthDropCode c).getD k 0 =
        columnHeightFromWidthDropCode c k
  | [], k => by
      simp [columnListFromWidthDropCode, columnHeightFromWidthDropCode]
  | (r, d) :: cs, k => by
      let H := d + codeDropSum cs
      by_cases hk : k < r
      · have hLen : k < (repeatValue r H).length := by
          simpa using hk
        rw [columnListFromWidthDropCode]
        rw [List.getD_append _ _ _ _ hLen]
        rw [repeatValue_eq_replicate]
        simp [columnHeightFromWidthDropCode, hk, H]
      · have hle : (repeatValue r H).length ≤ k := by
          simp only [repeatValue_eq_replicate, List.length_replicate]
          exact le_of_not_gt hk
        rw [columnListFromWidthDropCode]
        rw [List.getD_append_right _ _ _ _ hle]
        simp only [repeatValue_length]
        rw [getD_columnListFromWidthDropCode cs (k - r)]
        simp [columnHeightFromWidthDropCode, hk]

/-- cut より高い列の本数。 -/
def countAbove (cut : ℕ) : List ℕ → ℕ
  | [] => 0
  | x :: xs =>
      (if cut < x then 1 else 0) + countAbove cut xs

/-- `countAbove` は append に分配する。 -/
theorem countAbove_append
    (cut : ℕ) :
    ∀ xs ys : List ℕ,
      countAbove cut (xs ++ ys) =
        countAbove cut xs + countAbove cut ys
  | [], ys => by
      simp [countAbove]
  | x :: xs, ys => by
      simp only [List.cons_append, countAbove]
      rw [countAbove_append cut xs ys]
      exact Nat.add_assoc _ _ _ |>.symm

/-- 一定高さの plateau における `countAbove`。 -/
theorem countAbove_repeatValue
    (cut n h : ℕ) :
    countAbove cut (repeatValue n h) =
      if cut < h then n else 0 := by
  induction n with
  | zero =>
      simp [countAbove, repeatValue]
  | succ n ih =>
      rw [repeatValue_succ]
      rw [countAbove]
      by_cases hh : cut < h
      · have ih' :
            countAbove cut (repeatValue n h) = n := by
          simpa [hh] using ih
        simp only [ite_eq_left hh, ih']
        omega
      · have ih' :
            countAbove cut (repeatValue n h) = 0 := by
          simpa [hh] using ih
        simp only [ite_eq_right hh, ih']

/-- 全 part が cut 以下なら `countAbove = 0`。 -/
theorem countAbove_eq_zero_of_forall_le
    (cut : ℕ) :
    ∀ xs : List ℕ,
      (∀ x ∈ xs, x ≤ cut) →
      countAbove cut xs = 0
  | [], _h => by
      rfl
  | x :: xs, h => by
      have hx : ¬ cut < x := not_lt_of_ge (h x (by simp))
      have hTail : ∀ y ∈ xs, y ≤ cut := by
        intro y hy
        exact h y (by simp [hy])
      simp [countAbove, hx, countAbove_eq_zero_of_forall_le cut xs hTail]

/--
genuine 共役の第 `cut` 列高は、元図形で cut より高い列の本数そのもの。
-/
theorem genuineConjugateColumnHeight_eq_countAbove :
    ∀ (c : WidthDropCode) (cut : ℕ),
      genuineConjugateColumnHeight c cut =
        countAbove cut (columnListFromWidthDropCode c)
  | [], cut => by
      rfl
  | (r, d) :: cs, cut => by
      rw [columnListFromWidthDropCode]
      rw [countAbove_append, countAbove_repeatValue]
      rw [← genuineConjugateColumnHeight_eq_countAbove cs cut]
      by_cases h0 : cut < codeDropSum cs
      · have h1 : cut < d + codeDropSum cs := by omega
        simp [genuineConjugateColumnHeight, h0, h1]
      · have hTailLe : ∀ y ∈ columnListFromWidthDropCode cs, y ≤ cut := by
          intro y hy
          have hyLe := mem_columnList_le_dropSum cs hy
          omega
        have hZero :=
          countAbove_eq_zero_of_forall_le cut
            (columnListFromWidthDropCode cs) hTailLe
        have hGZero : genuineConjugateColumnHeight cs cut = 0 := by
          rw [genuineConjugateColumnHeight_eq_countAbove]
          exact hZero
        by_cases h1 : cut < d + codeDropSum cs
        · simp [genuineConjugateColumnHeight, h0, h1, hGZero]
        · simp [genuineConjugateColumnHeight, h0, h1, hGZero]

/-- truncated mass を cut から cut+1 へ上げる差は `countAbove cut`。 -/
theorem truncatedMass_succ
    (cut : ℕ) :
    ∀ xs : List ℕ,
      truncatedMass (cut + 1) xs =
        truncatedMass cut xs + countAbove cut xs
  | [] => by
      rfl
  | x :: xs => by
      by_cases hx : cut < x
      · have hCut : cut ≤ x := le_of_lt hx
        have hSucc : cut + 1 ≤ x := by omega
        simp [truncatedMass, countAbove, hx,
          min_eq_left hCut,
          truncatedMass_succ cut xs]
        omega
      · have hxLe : x ≤ cut := le_of_not_gt hx
        have hxSucc : x ≤ cut + 1 := by omega
        simp only [truncatedMass, min_eq_right hxSucc, truncatedMass_succ cut xs, min_eq_right hxLe,
           countAbove, hx,↓reduceIte, zero_add]
        exact
          (Nat.add_assoc
            x
            (truncatedMass cut xs)
            (countAbove cut xs)).symm

/-- prefix sum を一列伸ばしたときの `getD` 版差分公式。 -/
theorem sum_take_succ_eq_sum_take_add_getD
    (xs : List ℕ) :
    ∀ k : ℕ,
      (xs.take (k + 1)).sum =
        (xs.take k).sum + xs.getD k 0
  | 0 => by
      cases xs <;> simp
  | k + 1 => by
      cases xs with
      | nil =>
          simp
      | cons x xs =>
          simp only [List.take_succ_cons, List.sum_cons, List.getD_cons_succ]
          rw [sum_take_succ_eq_sum_take_add_getD xs k]
          omega

@[simp] theorem truncatedMass_zero :
    ∀ xs : List ℕ,
      truncatedMass 0 xs = 0
  | [] => by
      rfl
  | x :: xs => by
      simp [truncatedMass, truncatedMass_zero xs]

/--
共役図形の最初の `k` 列の cell 数は、元図形を高さ `k` で切った truncated mass。
これは genuine cell transpose の prefix-sum 版である。
-/
theorem prefixColumnMass_conjugate_eq_truncatedMass
    (c : WidthDropCode) :
    ∀ k : ℕ,
      prefixColumnMass (conjugateWidthDropCode c) k =
        truncatedMass k (columnPartitionOfCode c)
  | 0 => by
      simp [
        prefixColumnMass,
        columnPartitionOfCode,
        truncatedMass_zero
      ]
  | k + 1 => by
      unfold prefixColumnMass
      rw [sum_take_succ_eq_sum_take_add_getD]
      change
        prefixColumnMass (conjugateWidthDropCode c) k +
            (columnListFromWidthDropCode
              (conjugateWidthDropCode c)).getD k 0 =
          truncatedMass (k + 1) (columnPartitionOfCode c)
      rw [prefixColumnMass_conjugate_eq_truncatedMass c k]
      rw [getD_columnListFromWidthDropCode]
      rw [← genuineConjugateColumnHeight_eq_coordinate c k]
      rw [genuineConjugateColumnHeight_eq_countAbove]
      rw [truncatedMass_succ]
      rfl

/-- 全 part が cut 以下なら truncated mass は元の総和。 -/
theorem truncatedMass_eq_sum_of_forall_le
    (cut : ℕ) :
    ∀ xs : List ℕ,
      (∀ x ∈ xs, x ≤ cut) →
      truncatedMass cut xs = xs.sum
  | [], _h => by
      rfl
  | x :: xs, h => by
      have hx : x ≤ cut := h x (by simp)
      have hTail : ∀ y ∈ xs, y ≤ cut := by
        intro y hy
        exact h y (by simp [hy])
      simp [truncatedMass, min_eq_right hx,
        truncatedMass_eq_sum_of_forall_le cut xs hTail]

/-- genuine Young 共役は cell 数を保存する。 -/
theorem codeArea_conjugate
    (c : WidthDropCode) :
    codeArea (conjugateWidthDropCode c) = codeArea c := by
  calc
    codeArea (conjugateWidthDropCode c)
        = prefixColumnMass
            (conjugateWidthDropCode c)
            (codeWidth (conjugateWidthDropCode c)) := by
              exact (prefixColumnMass_full
                (conjugateWidthDropCode c)).symm
    _ = prefixColumnMass
          (conjugateWidthDropCode c)
          (codeDropSum c) := by
            rw [codeWidth_conjugate]
    _ = truncatedMass
          (codeDropSum c)
          (columnPartitionOfCode c) :=
            prefixColumnMass_conjugate_eq_truncatedMass c (codeDropSum c)
    _ = (columnPartitionOfCode c).sum := by
          apply truncatedMass_eq_sum_of_forall_le
          intro x hx
          exact mem_columnList_le_dropSum c hx
    _ = codeArea c := by
          exact columnListFromWidthDropCode_sum c

/--
同面積なら classical dominance は Young 共役で反転する。

`A` が `B` を dominate するとき、共役側では `B'` が `A'` を dominate する。
-/
theorem columnDominates_conjugate_reverse_of_equalArea
    (A B : WidthDropCode)
    (hArea : codeArea A = codeArea B)
    (hDom : ColumnDominates A B) :
    ColumnDominates
      (conjugateWidthDropCode B)
      (conjugateWidthDropCode A) := by
  intro k
  rw [
    prefixColumnMass_conjugate_eq_truncatedMass,
    prefixColumnMass_conjugate_eq_truncatedMass
  ]
  apply truncatedMass_le_of_classicalDominates_of_sum_eq
  · exact columnListFromWidthDropCode_nonincreasing B
  · exact
      (columnDominates_iff_classicalDominates_columnPartition A B).1 hDom
  · simpa [columnPartitionOfCode,
      columnListFromWidthDropCode_sum] using hArea

/--
古典的な共役 dominance 反転の exact iff 版。
同じ cell 数を持つ二図形について

  A dominates B
    ↔
  B' dominates A'

が成立する。
-/
theorem columnDominates_iff_conjugate_reverse_of_equalArea
    (A B : WidthDropCode)
    (hArea : codeArea A = codeArea B) :
    ColumnDominates A B ↔
      ColumnDominates
        (conjugateWidthDropCode B)
        (conjugateWidthDropCode A) := by
  constructor
  · exact columnDominates_conjugate_reverse_of_equalArea A B hArea
  · intro hConj
    have hAreaConj :
        codeArea (conjugateWidthDropCode B) =
          codeArea (conjugateWidthDropCode A) := by
      rw [codeArea_conjugate, codeArea_conjugate]
      exact hArea.symm
    have hBack :=
      columnDominates_conjugate_reverse_of_equalArea
        (conjugateWidthDropCode B)
        (conjugateWidthDropCode A)
        hAreaConj hConj
    simpa using hBack

end YoungFerrersRestricted

namespace GenericRecordFerrers
namespace RecordFerrers

open YoungFerrersRestricted

/-- RecordFerrers の column partition に対する classical dominance。 -/
def RankClassicalColumnDominates
    {β : ℕ → ℕ}
    {m : ℕ}
    (R S : RecordFerrers β m) : Prop :=
  ClassicalDominatesList
    (columnPartitionOfCode R.plateauWidthDropCode)
    (columnPartitionOfCode S.plateauWidthDropCode)

/-- 既存 `RankColumnDominates` は classical column dominance と exact に同じ。 -/
theorem rankColumnDominates_iff_classical
    {β : ℕ → ℕ}
    {m : ℕ}
    (R S : RecordFerrers β m) :
    RankColumnDominates R S ↔
      RankClassicalColumnDominates R S := by
  rfl

/-- RecordFerrers の row-length convention に対する classical dominance。 -/
def RankClassicalRowDominates
    {β : ℕ → ℕ}
    {m : ℕ}
    (R S : RecordFerrers β m) : Prop :=
  RowClassicalDominates R.plateauWidthDropCode S.plateauWidthDropCode

/-- row dominance は共役 plateau code 上の column dominance と exact に一致する。 -/
theorem rankClassicalRowDominates_iff_conjugateColumnDominates
    {β : ℕ → ℕ}
    {m : ℕ}
    (R S : RecordFerrers β m) :
    RankClassicalRowDominates R S ↔
      ColumnDominates R.conjugatePlateauCode S.conjugatePlateauCode := by
  rfl

/--
RecordFerrers 版の古典 dominance 反転。
Young cell count が等しい二つの rank-envelope 図形では、
元の column dominance と共役側の逆向き dominance が exact に同値。
-/
theorem rankColumnDominates_iff_conjugate_reverse_of_equalCellCount
    {β : ℕ → ℕ}
    {m : ℕ}
    (R S : RecordFerrers β m)
    (hArea : R.youngCellCount = S.youngCellCount) :
    RankColumnDominates R S ↔
      ColumnDominates S.conjugatePlateauCode R.conjugatePlateauCode := by
  simpa [
    RankColumnDominates,
    youngCellCount,
    conjugatePlateauCode
  ] using
    (columnDominates_iff_conjugate_reverse_of_equalArea
      R.plateauWidthDropCode S.plateauWidthDropCode hArea)

end RecordFerrers
end GenericRecordFerrers
end Experimental2
end Collatz3
