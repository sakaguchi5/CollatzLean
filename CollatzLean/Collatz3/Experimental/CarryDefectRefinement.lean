import CollatzLean.Collatz3.Experimental.RecordCarryBudget

/-!
# Collatz3 experimental: carry defect と refinement

第三段の前半実験。

`HasUnitCarry β` の有限 block 合成で現れる carry 総和を、
屋根の加法 defect として読み直す。

ここでは次を調べる。

* defect = carry `1` の個数
* Record 型 budget `length - 1` は carry `0` をちょうど一個だけ強制する
* block の並べ替えは defect を変えない
* 一つの block `b+d` を `b,d` に割ると defect は `c(b,d)` だけ増える
* refinement tree の defect が最大なら全内部 split carry は `1`

現行 `RecordFerrers` / `Critical` は import しない。
-/

namespace Collatz3
namespace Experimental

/--
start `a` と block 列 `rs` に対する global roof defect。

`HasUnitCarry β` の下では、これは `carryListFrom β a rs` の総和と exact に一致する。
-/
def roofDefect
    (β : ℕ → ℕ)
    (a : ℕ)
    (rs : List ℕ) : ℕ :=
  β (a + rs.sum) - (β a + (rs.map β).sum)

/-- 有限幅の二分 refinement tree。leaf は最終 block 幅を持つ。 -/
inductive WidthRefinement where
  | leaf (r : ℕ)
  | node (left right : WidthRefinement)
  deriving Repr

namespace WidthRefinement

/-- refinement tree 全体の幅。 -/
def width : WidthRefinement → ℕ
  | .leaf r => r
  | .node l r => width l + width r

/-- 左から並べた leaf 幅。 -/
def leaves : WidthRefinement → List ℕ
  | .leaf r => [r]
  | .node l r => leaves l ++ leaves r

/-- 内部 split 数。 -/
def internalCount : WidthRefinement → ℕ
  | .leaf _ => 0
  | .node l r => internalCount l + internalCount r + 1

/--
各内部 split `(left.width, right.width)` で生じる carry。
root, left subtree, right subtree の順に並べる。
-/
def internalCarries
    (β : ℕ → ℕ) : WidthRefinement → List ℕ
  | .leaf _ => []
  | .node l r =>
      roofCarry β (width l) (width r) ::
        (internalCarries β l ++ internalCarries β r)

@[simp] theorem leaves_sum :
    ∀ t : WidthRefinement,
      t.leaves.sum = t.width
  | .leaf r => by
      simp [leaves, width]
  | .node l r => by
      simp [leaves, width, leaves_sum l, leaves_sum r]

@[simp] theorem internalCarries_length
    {β : ℕ → ℕ} :
    ∀ t : WidthRefinement,
      (t.internalCarries β).length = t.internalCount
  | .leaf r => by
      simp [internalCarries, internalCount]
  | .node l r => by
      simp [internalCarries, internalCount,
        internalCarries_length (β := β) l,
        internalCarries_length (β := β) r]

end WidthRefinement

namespace HasUnitCarry

/-- global roof defect は carry 総和そのもの。 -/
theorem roofDefect_eq_carrySum
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (a : ℕ)
    (rs : List ℕ) :
    roofDefect β a rs = (carryListFrom β a rs).sum := by
  have hExact := U.roof_add_sum_eq_blockRoofs_add_carries a rs
  unfold roofDefect
  omega

/-- defect は block 数以下。 -/
theorem roofDefect_le_length
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (a : ℕ)
    (rs : List ℕ) :
    roofDefect β a rs ≤ rs.length := by
  rw [U.roofDefect_eq_carrySum]
  exact U.carryListFrom_sum_le_length a rs

/--
0/1 列では `sum + zero count = length`。
carry 数と non-carry 数の保存則として後で使う。
-/
theorem list_sum_add_count_zero_eq_length_of_mem_le_one :
    ∀ xs : List ℕ,
      (∀ c : ℕ, c ∈ xs → c ≤ 1) →
      xs.sum + xs.count 0 = xs.length
  | [], _h => by
      simp
  | x :: xs, h => by
      have hx : x ≤ 1 := h x (by simp)
      have hTail : ∀ c : ℕ, c ∈ xs → c ≤ 1 := by
        intro c hc
        exact h c (by simp [hc])
      have hIH :=
        list_sum_add_count_zero_eq_length_of_mem_le_one xs hTail
      have hxCases : x = 0 ∨ x = 1 := by
        omega
      rcases hxCases with hx | hx
      · subst x
        simp
        omega
      · subst x
        simp
        omega

/-- carry 総和 + carry `0` の個数 = block 数。 -/
theorem carrySum_add_zeroCount_eq_length
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (a : ℕ)
    (rs : List ℕ) :
    (carryListFrom β a rs).sum +
        (carryListFrom β a rs).count 0 = rs.length := by
  have hList :=
    list_sum_add_count_zero_eq_length_of_mem_le_one
      (carryListFrom β a rs)
      (by
        intro c hc
        exact U.carryListFrom_mem_le_one hc)
  simpa using hList

/--
非空 block 列で carry budget が `length - 1` なら、carry `0` はちょうど一個。
まだその位置は特定しない。
-/
theorem carryZeroCount_eq_one_of_sum_eq_length_sub_one
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (a : ℕ)
    (rs : List ℕ)
    (hNonempty : rs ≠ [])
    (hBudget :
      (carryListFrom β a rs).sum = rs.length - 1) :
    (carryListFrom β a rs).count 0 = 1 := by
  have hCount := U.carrySum_add_zeroCount_eq_length a rs
  have hPos : 0 < rs.length := List.length_pos_iff.mpr hNonempty
  omega

/--
normalized Record 型 factorization は、terminal 条件をまだ使わなくても
canonical carry 列中の `0` を exact に一個へ固定する。
-/
theorem normalizedFactorization_forces_uniqueZeroCount
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (hOne : β 1 = 1)
    {m : ℕ}
    (rs : List ℕ)
    (hNonempty : rs ≠ [])
    (hCover : m = 1 + rs.sum)
    (hFactor :
      β m = (rs.map β).sum + rs.length) :
    (carryListFrom β 1 rs).count 0 = 1 := by
  have hBudget :=
    U.normalizedFactorization_carrySum_eq_length_sub_one
      hOne rs hCover hFactor
  exact
    U.carryZeroCount_eq_one_of_sum_eq_length_sub_one
      1 rs hNonempty hBudget
/-- 自然数リストの和は permutation で不変。 -/
theorem list_sum_eq_of_perm
    {xs ys : List ℕ}
    (hPerm : xs.Perm ys) :
    xs.sum = ys.sum := by
  induction hPerm with
  | nil =>
      rfl
  | cons x hPerm ih =>
      simp [ih]
  | swap x y xs =>
      simp only [List.sum_cons, Nat.add_left_comm]
  | trans h₁ h₂ ih₁ ih₂ =>
      exact ih₁.trans ih₂
/--
block 長を並べ替えても global defect は変わらない。
carry の位置は変わり得るが、carry の総数は不変。
-/
theorem roofDefect_eq_of_perm
    {β : ℕ → ℕ}
    (a : ℕ)
    {rs ts : List ℕ}
    (hPerm : rs.Perm ts) :
    roofDefect β a rs = roofDefect β a ts := by
  have hWidth : rs.sum = ts.sum :=
    list_sum_eq_of_perm hPerm
  have hRoofPerm : (rs.map β).Perm (ts.map β) :=
    hPerm.map β
  have hRoofSum : (rs.map β).sum = (ts.map β).sum :=
    list_sum_eq_of_perm hRoofPerm
  simp [roofDefect, hWidth, hRoofSum]

/--
`HasUnitCarry` の下では、block の並べ替えは carry 総和も変えない。
-/
theorem carrySum_eq_of_perm
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (a : ℕ)
    {rs ts : List ℕ}
    (hPerm : rs.Perm ts) :
    (carryListFrom β a rs).sum =
      (carryListFrom β a ts).sum := by
  rw [← U.roofDefect_eq_carrySum, ← U.roofDefect_eq_carrySum]
  exact roofDefect_eq_of_perm a hPerm

/--
一つの block `b+d` を二つ `b,d` に split すると、
defect の増分は start `a` と無関係に exact に `c(b,d)`。
-/
theorem roofDefect_split_two
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (a b d : ℕ) :
    roofDefect β a [b + d] + roofCarry β b d =
      roofDefect β a [b, d] := by
  rw [U.roofDefect_eq_carrySum, U.roofDefect_eq_carrySum]
  simp only [carryListFrom, List.sum_cons, List.sum_nil, Nat.add_zero]
  have hCocycle := U.carry_cocycle a b d
  omega

/-- refinement tree の各内部 carry も 0/1。 -/
theorem refinement_internalCarries_mem_le_one
    {β : ℕ → ℕ}
    (U : HasUnitCarry β) :
    ∀ {t : WidthRefinement} {c : ℕ},
      c ∈ t.internalCarries β → c ≤ 1
  | .leaf r, c, hMem => by
      simp [WidthRefinement.internalCarries] at hMem
  | .node l r, c, hMem => by
      simp only [WidthRefinement.internalCarries, List.mem_cons,
        List.mem_append] at hMem
      rcases hMem with hRoot | hLeft | hRight
      · subst c
        exact U.carry_le_one l.width r.width
      · exact U.refinement_internalCarries_mem_le_one hLeft
      · exact U.refinement_internalCarries_mem_le_one hRight

/--
refinement tree の exact roof factorization。

`β(total width) = Σ β(leaf width) + Σ internal carry`。
結合順序を tree として明示しても、追加情報は internal carry 総和だけ。
-/
theorem refinement_roof_eq_leafRoofs_add_internalCarries
    {β : ℕ → ℕ}
    (U : HasUnitCarry β) :
    ∀ t : WidthRefinement,
      β t.width =
        (t.leaves.map β).sum + (t.internalCarries β).sum
  | .leaf r => by
      simp [WidthRefinement.width, WidthRefinement.leaves,
        WidthRefinement.internalCarries]
  | .node l r => by
      have hAdd := U.add_eq l.width r.width
      have hLeft := U.refinement_roof_eq_leafRoofs_add_internalCarries l
      have hRight := U.refinement_roof_eq_leafRoofs_add_internalCarries r
      simp only [WidthRefinement.width, WidthRefinement.leaves,
        WidthRefinement.internalCarries, List.map_append,
        List.sum_append, List.sum_cons]
      omega

/--
0/1 列が最大総和 `length` を取るなら全成分 1。
-/
theorem list_eq_replicate_one_of_sum_eq_length_of_mem_le_one :
    ∀ xs : List ℕ,
      (∀ c : ℕ, c ∈ xs → c ≤ 1) →
      xs.sum = xs.length →
      xs = List.replicate xs.length 1
  | [], _hLe, _hSum => by
      simp
  | x :: xs, hLe, hSum => by
      have hx : x ≤ 1 := hLe x (by simp)
      have hTailLe : ∀ c : ℕ, c ∈ xs → c ≤ 1 := by
        intro c hc
        exact hLe c (by simp [hc])
      have hTailBound :=
        list_sum_add_count_zero_eq_length_of_mem_le_one xs hTailLe
      have hxOne : x = 1 := by
        simp only [List.sum_cons, List.length_cons] at hSum
        omega
      have hTailSum : xs.sum = xs.length := by
        simp only [List.sum_cons, List.length_cons] at hSum
        omega
      have hIH :=
        list_eq_replicate_one_of_sum_eq_length_of_mem_le_one
          xs hTailLe hTailSum
      subst x
      have hCons :
          1 :: xs = 1 :: List.replicate xs.length 1 :=
        congrArg (fun ys => 1 :: ys) hIH
      simpa only [List.length_cons, List.replicate_succ] using hCons

/--
refinement tree の defect が内部 split 数の最大値に達したなら、
全内部 split carry は `1`。

したがって「最大 defect refinement」は局所的にも全 split が carry-1 で飽和している。
-/
theorem refinement_all_internalCarries_one_of_maximal
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    (t : WidthRefinement)
    (hMax :
      (t.internalCarries β).sum = t.internalCount) :
    t.internalCarries β = List.replicate t.internalCount 1 := by
  have hLe :
      ∀ c : ℕ, c ∈ t.internalCarries β → c ≤ 1 := by
    intro c hc
    exact U.refinement_internalCarries_mem_le_one hc
  have hLen :
      (t.internalCarries β).length = t.internalCount :=
    WidthRefinement.internalCarries_length (β := β) t
  have hSumLen :
      (t.internalCarries β).sum =
        (t.internalCarries β).length := by
    rw [hLen]
    exact hMax
  have hAll :=
    list_eq_replicate_one_of_sum_eq_length_of_mem_le_one
      (t.internalCarries β) hLe hSumLen
  simpa [hLen] using hAll

end HasUnitCarry
end Experimental
end Collatz3
