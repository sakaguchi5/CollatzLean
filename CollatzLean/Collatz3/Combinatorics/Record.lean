import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic

/-!
# Collatz3: generic record decomposition vocabulary

このファイルにも Collatz 固有の量を入れない。

`record` は「Ferrers」という名前に埋め込まず、任意の整数値 rank 関数に対する
新しい strict minimum と、その間の excursion として定義する。

完全な有限分解では、strict record blocks の後に terminal tail を分離する。
terminal endpoint 自体を新しい strict record と要求しないことが重要である。

後段の `Critical.RecordFerrers` は、この generic record 語彙へ
critical profile から導いた rank を渡すだけにする。
-/

namespace Collatz3
namespace Combinatorics

/-- `k` がそれ以前の全 index より strict に低い record index。 -/
def IsRecordLow
    (rank : ℕ → ℤ)
    (k : ℕ) : Prop :=
  ∀ j : ℕ, j < k → rank k < rank j

/-- index `0` は空の前歴に対して常に record。 -/
theorem isRecordLow_zero
    (rank : ℕ → ℤ) :
    IsRecordLow rank 0 := by
  intro j hj
  omega

/--
start `a` から長さ `r` の一つの record excursion。

* `r > 0`
* interior は start rank より strict に上
* endpoint で start rank より strict に下

だけを持つ。minimality や Collatz actuality は定義に入れない。
-/
def IsRecordBlock
    (rank : ℕ → ℤ)
    (a r : ℕ) : Prop :=
  0 < r ∧
    (∀ j : ℕ, 0 < j → j < r → rank a < rank (a + j)) ∧
    rank (a + r) < rank a

namespace IsRecordBlock

/-- record block の長さは正。 -/
theorem length_pos
    {rank : ℕ → ℤ}
    {a r : ℕ}
    (B : IsRecordBlock rank a r) :
    0 < r :=
  B.1

/-- record block interior は start rank より上。 -/
theorem interior
    {rank : ℕ → ℤ}
    {a r : ℕ}
    (B : IsRecordBlock rank a r)
    {j : ℕ}
    (hjPos : 0 < j)
    (hjLt : j < r) :
    rank a < rank (a + j) :=
  B.2.1 j hjPos hjLt

/-- record block endpoint は start rank より下。 -/
theorem end_drop
    {rank : ℕ → ℤ}
    {a r : ℕ}
    (B : IsRecordBlock rank a r) :
    rank (a + r) < rank a :=
  B.2.2

/--
start が global record なら、record block の endpoint も新しい global record。
これは record の一般論であり、Ferrers や Collatz を使わない。
-/
theorem end_recordLow
    {rank : ℕ → ℤ}
    {a r : ℕ}
    (B : IsRecordBlock rank a r)
    (ha : IsRecordLow rank a) :
    IsRecordLow rank (a + r) := by
  intro j hj
  have hEnd :
      rank (a + r) < rank a :=
    end_drop B
  by_cases hja : j < a
  · have hPrev :
        rank a < rank j :=
      ha j hja
    omega
  by_cases hEq : j = a
  · subst j
    exact hEnd
  have haj : a < j := by
    omega
  let t : ℕ := j - a
  have htPos : 0 < t := by
    dsimp [t]
    omega
  have htLt : t < r := by
    dsimp [t]
    omega
  have hInt :
      rank a < rank (a + t) :=
    interior B htPos htLt
  have hAj : a + t = j := by
    dsimp [t]
    omega
  rw [hAj] at hInt
  omega

end IsRecordBlock

/--
最後の strict record cut `a` から terminal index までの closing tail。

terminal 自身を新しい record low とは要求しない。
interior に start rank より低い点がないことだけを要求する。
`a = terminalIndex` の退化 tail も generic 語彙としては許す。
-/
def IsTerminalTail
    (rank : ℕ → ℤ)
    (a terminalIndex : ℕ) : Prop :=
  a ≤ terminalIndex ∧
    ∀ j : ℕ,
      a < j →
      j < terminalIndex →
      rank a ≤ rank j

namespace IsTerminalTail

/-- terminal tail の start は terminal を越えない。 -/
theorem start_le_terminal
    {rank : ℕ → ℤ}
    {a terminalIndex : ℕ}
    (T : IsTerminalTail rank a terminalIndex) :
    a ≤ terminalIndex :=
  T.1

/-- terminal tail interior には start rank より低い点がない。 -/
theorem interior_not_below
    {rank : ℕ → ℤ}
    {a terminalIndex j : ℕ}
    (T : IsTerminalTail rank a terminalIndex)
    (haj : a < j)
    (hjt : j < terminalIndex) :
    rank a ≤ rank j :=
  T.2 j haj hjt

/-- pointwise equal な rank では terminal tail 条件も変わらない。 -/
theorem congr
    {rank rank' : ℕ → ℤ}
    {a terminalIndex : ℕ}
    (hEq : ∀ k : ℕ, rank k = rank' k) :
    IsTerminalTail rank a terminalIndex ↔
      IsTerminalTail rank' a terminalIndex := by
  constructor
  · intro T
    refine ⟨T.1, ?_⟩
    intro j haj hjt
    simpa [hEq a, hEq j] using T.2 j haj hjt
  · intro T
    refine ⟨T.1, ?_⟩
    intro j haj hjt
    simpa [hEq a, hEq j] using T.2 j haj hjt

end IsTerminalTail

/--
record block の長さだけを保持する骨格。
ここには rank も Ferrers decoration も保存しない。
-/
structure RecordSkeleton where
  lengths : List ℕ
  positive : ∀ r ∈ lengths, 0 < r

namespace RecordSkeleton

/-- skeleton が覆う総横幅。 -/
def totalLength
    (S : RecordSkeleton) : ℕ :=
  S.lengths.sum

/--
長さ列が rank 上で start `a` から順に record blocks を実現する、という純粋な再帰 predicate。
-/
def realizesLengthsFrom
    (rank : ℕ → ℤ) : ℕ → List ℕ → Prop
  | _a, [] => True
  | a, r :: rs =>
      IsRecordBlock rank a r ∧
        realizesLengthsFrom rank (a + r) rs

/-- skeleton が rank 上で start `a` から record 分解を実現する。 -/
def RealizesFrom
    (S : RecordSkeleton)
    (rank : ℕ → ℤ)
    (a : ℕ) : Prop :=
  realizesLengthsFrom rank a S.lengths

/--
非空の record block 列を実現すると、最後の cut rank は開始 rank より strict に低い。
terminal tail を record block 列から分離すべき理由を generic に表す補題でもある。
-/
theorem realizesLengthsFrom_end_drop
    {rank : ℕ → ℤ}
    {a : ℕ}
    {rs : List ℕ}
    (h : realizesLengthsFrom rank a rs)
    (hne : rs ≠ []) :
    rank (a + rs.sum) < rank a := by
  induction rs generalizing a with
  | nil =>
      exact False.elim (hne rfl)
  | cons r rs ih =>
      change
        IsRecordBlock rank a r ∧
          realizesLengthsFrom rank (a + r) rs
        at h
      rcases h with ⟨hBlock, hTail⟩
      by_cases hEmpty : rs = []
      · subst rs
        simpa using hBlock.end_drop
      · have hTailDrop := ih (a := a + r) hTail hEmpty
        have hFirstDrop := hBlock.end_drop
        have hIndex :
            a + (r :: rs).sum = (a + r) + rs.sum := by
          simp [Nat.add_assoc]
        calc
          rank (a + (r :: rs).sum)
              = rank ((a + r) + rs.sum) := by
                  rw [hIndex]
          _ < rank (a + r) := hTailDrop
          _ < rank a := hFirstDrop

/-- skeleton 版の終端 strict drop。 -/
theorem end_drop_of_realizesFrom
    (S : RecordSkeleton)
    {rank : ℕ → ℤ}
    {a : ℕ}
    (h : S.RealizesFrom rank a)
    (hne : S.lengths ≠ []) :
    rank (a + S.totalLength) < rank a := by
  unfold RealizesFrom at h
  unfold totalLength
  exact realizesLengthsFrom_end_drop h hne

/-- rank が pointwise に等しければ record realization は変わらない。 -/
theorem realizesLengthsFrom_congr
    {rank rank' : ℕ → ℤ}
    (hEq : ∀ k : ℕ, rank k = rank' k) :
    ∀ a rs,
      realizesLengthsFrom rank a rs ↔
        realizesLengthsFrom rank' a rs := by
  intro a rs
  induction rs generalizing a with
  | nil =>
      simp [realizesLengthsFrom]
  | cons r rs ih =>
      constructor
      · intro h
        rcases h with ⟨hBlock, hTail⟩
        refine ⟨?_, (ih (a + r)).1 hTail⟩
        rcases hBlock with ⟨hrPos, hInterior, hEnd⟩
        refine ⟨hrPos, ?_, ?_⟩
        · intro j hjPos hjLt
          simpa [hEq a, hEq (a + j)] using hInterior j hjPos hjLt
        · simpa [hEq (a + r), hEq a] using hEnd
      · intro h
        rcases h with ⟨hBlock, hTail⟩
        refine ⟨?_, (ih (a + r)).2 hTail⟩
        rcases hBlock with ⟨hrPos, hInterior, hEnd⟩
        refine ⟨hrPos, ?_, ?_⟩
        · intro j hjPos hjLt
          simpa [hEq a, hEq (a + j)] using hInterior j hjPos hjLt
        · simpa [hEq (a + r), hEq a] using hEnd

/-- pointwise equal な rank では skeleton realization も同値。 -/
theorem realizesFrom_congr
    (S : RecordSkeleton)
    {rank rank' : ℕ → ℤ}
    {a : ℕ}
    (hEq : ∀ k : ℕ, rank k = rank' k) :
    S.RealizesFrom rank a ↔ S.RealizesFrom rank' a := by
  exact realizesLengthsFrom_congr hEq a S.lengths

end RecordSkeleton

end Combinatorics
end Collatz3
