import CollatzLean.Collatz3.Core.PrefixDepth
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Tactic.Ring

/-!
# Collatz3 Bridge: exponent word と parity composition

odd-only exponent word `[e₁, ..., e_m]` は、binary parity word

`1 0^(e₁-1) 1 0^(e₂-1) ... 1 0^(e_m-1)`

の run length を保存した composition と同一視できる。

このファイルでは binary list 自体を primitive data にせず、mathlib の
`Composition n` を parity code の正本として使う。

`Composition n` は positive blocks の列で総和が `n` なので、
`Word.Valid` かつ `Word.twoSteps = n` という exponent word と exact に同値である。

さらに positive depth `n` の parity code に末尾 bit `0/1` を一つ加える操作を作る。

* `0` : 最後の run を 1 延長する。
* `1` : 新しい長さ 1 の run を追加する。

これにより `Composition n × Bool ≃ Composition (n+1)` を得る。
-/

namespace Collatz3
namespace Bridge

/-- total two-depth `n` を持つ valid exponent word。 -/
abbrev ValidExponentWordAtDepth (n : ℕ) :=
  {w : Word // Word.Valid w ∧ Word.twoSteps w = n}

/-- binary parity word の run-length code。 -/
abbrev ParityComposition (n : ℕ) := Composition n

/-- valid exponent word と parity composition の exact equivalence。 -/
def validExponentWordEquivParityComposition
    (n : ℕ) :
    ValidExponentWordAtDepth n ≃ ParityComposition n where
  toFun w :=
    ⟨w.1,
      by
        intro e he
        exact w.2.1 e he,
      by
        simpa [Word.twoSteps] using w.2.2⟩
  invFun c :=
    ⟨c.blocks,
      by
        constructor
        · intro e he
          exact c.blocks_pos he
        · simp only [Word.twoSteps, Composition.blocks_sum]⟩
  left_inv w := by
    apply Subtype.ext
    rfl
  right_inv c := by
    apply Composition.ext
    rfl

/-- composition の block 数は exponent word の odd-step 数。 -/
@[simp] theorem oddSteps_blocks
    {n : ℕ}
    (c : ParityComposition n) :
    Word.oddSteps c.blocks = c.length := by
  rfl

/-- composition の総和は exponent word の total two-depth。 -/
@[simp] theorem twoSteps_blocks
    {n : ℕ}
    (c : ParityComposition n) :
    Word.twoSteps c.blocks = n := by
  simp only [Word.twoSteps, Composition.blocks_sum]

/-- composition の `sizeUpTo` は exponent word の prefix two-depth そのもの。 -/
@[simp] theorem prefixTwoDepth_blocks_eq_sizeUpTo
    {n : ℕ}
    (c : ParityComposition n)
    (k : ℕ) :
    Word.prefixTwoDepth c.blocks k = c.sizeUpTo k := by
  rfl

/-- positive total depth の composition は block list が非空。 -/
theorem parityComposition_blocks_ne_nil
    {n : ℕ}
    (hn : 0 < n)
    (c : ParityComposition n) :
    c.blocks ≠ [] := by
  intro h
  have h0 := (c.blocks_eq_nil).1 h
  omega

/-- positive total depth の composition の最後の block。 -/
def parityLastBlock
    {n : ℕ}
    (hn : 0 < n)
    (c : ParityComposition n) : ℕ :=
  c.blocks.getLast (parityComposition_blocks_ne_nil hn c)

/-- 最後の block は正。 -/
theorem parityLastBlock_pos
    {n : ℕ}
    (hn : 0 < n)
    (c : ParityComposition n) :
    0 < parityLastBlock hn c := by
  unfold parityLastBlock
  apply c.blocks_pos
  exact List.getLast_mem _

/--
末尾 bit `0` を加える。
最後の positive run の長さを 1 増やす。
-/
def parityAppendZero
    {n : ℕ}
    (hn : 0 < n)
    (c : ParityComposition n) :
    ParityComposition (n + 1) := by
  let hne := parityComposition_blocks_ne_nil hn c
  let a := c.blocks.getLast hne
  refine
    ⟨c.blocks.dropLast ++ [a + 1], ?_, ?_⟩
  · intro e he
    rw [List.mem_append] at he
    rcases he with he | he
    · apply c.blocks_pos
      rw [← List.dropLast_append_getLast hne]
      simp [he]
    · simp only [List.mem_singleton] at he
      subst e
      exact Nat.succ_pos a
  · have hSplit : c.blocks.dropLast.sum + a = c.blocks.sum := by
      have h := congrArg List.sum (List.dropLast_append_getLast hne)
      simpa [a, List.sum_append] using h
    calc
      (c.blocks.dropLast ++ [a + 1]).sum
          = c.blocks.dropLast.sum + (a + 1) := by simp [List.sum_append]
      _ = (c.blocks.dropLast.sum + a) + 1 := by omega
      _ = c.blocks.sum + 1 := by rw [hSplit]
      _ = n + 1 := by rw [c.blocks_sum]

/-- 末尾 bit `1` を加える。新しい長さ 1 の run を追加する。 -/
def parityAppendOne
    {n : ℕ}
    (c : ParityComposition n) :
    ParityComposition (n + 1) := by
  exact c.append (Composition.single 1 (by omega))

/-- append-zero では block 数は変わらない。 -/
@[simp] theorem parityAppendZero_length
    {n : ℕ}
    (hn : 0 < n)
    (c : ParityComposition n) :
    (parityAppendZero hn c).length = c.length := by
  let hne := parityComposition_blocks_ne_nil hn c
  have hLen := congrArg List.length (List.dropLast_append_getLast hne)
  change (c.blocks.dropLast ++ [c.blocks.getLast hne + 1]).length = c.blocks.length
  simpa using hLen

/-- append-one では block 数が 1 増える。 -/
@[simp] theorem parityAppendOne_length
    {n : ℕ}
    (c : ParityComposition n) :
    (parityAppendOne c).length = c.length + 1 := by
  change (c.blocks ++ [1]).length = c.blocks.length + 1
  simp

/-- append-zero の最後の block は元の最後の block + 1。 -/
@[simp] theorem parityAppendZero_lastBlock
    {n : ℕ}
    (hn : 0 < n)
    (c : ParityComposition n) :
    parityLastBlock (by omega : 0 < n + 1) (parityAppendZero hn c) =
      parityLastBlock hn c + 1 := by
  unfold parityLastBlock parityAppendZero
  simp only [ne_eq, List.cons_ne_self, not_false_eq_true,
          List.getLast_append_of_ne_nil,List.getLast_singleton]

/-- append-one の最後の block は `1`。 -/
@[simp] theorem parityAppendOne_lastBlock
    {n : ℕ}
    (c : ParityComposition n) :
    parityLastBlock (by omega : 0 < n + 1) (parityAppendOne c) = 1 := by
  unfold parityLastBlock parityAppendOne
  simp [Composition.append_blocks]

/-- append-one は proper block prefix の size を保存する。 -/
theorem parityAppendOne_sizeUpTo
    {n : ℕ}
    (c : ParityComposition n)
    {k : ℕ}
    (hk : k ≤ c.length) :
    (parityAppendOne c).sizeUpTo k = c.sizeUpTo k := by
  unfold Composition.sizeUpTo parityAppendOne
  simp only [Composition.append_blocks, Composition.single]
  rw [List.take_append_of_le_length]
  simpa [Composition.length] using hk

/-- append-zero は最後の block より手前の prefix size を保存する。 -/
theorem parityAppendZero_sizeUpTo
    {n : ℕ}
    (hn : 0 < n)
    (c : ParityComposition n)
    {k : ℕ}
    (hk : k < c.length) :
    (parityAppendZero hn c).sizeUpTo k = c.sizeUpTo k := by
  let hne := parityComposition_blocks_ne_nil hn c
  have hLen := congrArg List.length (List.dropLast_append_getLast hne)
  have hkDrop : k ≤ c.blocks.dropLast.length := by
    have hLen' :
        c.blocks.dropLast.length + 1 = c.blocks.length := by
      simpa using hLen
    change k < c.blocks.length at hk
    omega
  unfold Composition.sizeUpTo parityAppendZero
  rw [List.take_append_of_le_length hkDrop]
  have hTake : c.blocks.dropLast.take k = c.blocks.take k := by
    rw [List.dropLast_eq_take]
    rw [List.take_take]
    have hk' : k ≤ c.blocks.length - 1 := by
      change k < c.blocks.length at hk
      omega
    rw [Nat.min_eq_left hk']
  rw [hTake]

/--
positive depth の child composition から末尾 bit を一つ取り除く parent。
最後の run が `1` ならその run を落とし、`>1` なら 1 短くする。
-/
def parityParent
    {n : ℕ}
    (c : ParityComposition (n + 1)) :
    ParityComposition n := by
  let hne : c.blocks ≠ [] := parityComposition_blocks_ne_nil (by omega) c
  let a := c.blocks.getLast hne
  by_cases ha : a = 1
  · refine ⟨c.blocks.dropLast, ?_, ?_⟩
    · intro e he
      apply c.blocks_pos
      rw [← List.dropLast_append_getLast hne]
      simp [he]
    · have hSplit : c.blocks.dropLast.sum + a = c.blocks.sum := by
        have h := congrArg List.sum (List.dropLast_append_getLast hne)
        simpa [a, List.sum_append] using h
      rw [ha] at hSplit
      rw [c.blocks_sum] at hSplit
      omega
  · have haPos : 0 < a := by
      dsimp [a]
      apply c.blocks_pos
      exact List.getLast_mem _
    refine ⟨c.blocks.dropLast ++ [a - 1], ?_, ?_⟩
    · intro e he
      rw [List.mem_append] at he
      rcases he with he | he
      · apply c.blocks_pos
        rw [← List.dropLast_append_getLast hne]
        simp [he]
      · simp only [List.mem_singleton] at he
        subst e
        omega
    · have hSplit : c.blocks.dropLast.sum + a = c.blocks.sum := by
        have h := congrArg List.sum (List.dropLast_append_getLast hne)
        simpa [a, List.sum_append] using h
      rw [c.blocks_sum] at hSplit
      simp only [List.sum_append, List.sum_singleton]
      omega

/-- child の最後に追加された parity bit。 -/
def parityLastBit
    {n : ℕ}
    (c : ParityComposition (n + 1)) : Bool :=
  decide (parityLastBlock (by omega : 0 < n + 1) c = 1)

/-- append-zero 後の block list の具体形。 -/
@[simp] theorem parityAppendZero_blocks
    {n : ℕ}
    (hn : 0 < n)
    (c : ParityComposition n) :
    (parityAppendZero hn c).blocks =
      c.blocks.dropLast ++ [parityLastBlock hn c + 1] := by
  unfold parityAppendZero parityLastBlock
  rfl

/-- append-zero 後に最後の block を落とすと、元の dropLast に戻る。 -/
@[simp] theorem parityAppendZero_dropLast
    {n : ℕ}
    (hn : 0 < n)
    (c : ParityComposition n) :
    (parityAppendZero hn c).blocks.dropLast =
      c.blocks.dropLast := by
  rw [parityAppendZero_blocks]
  simp

/--
child の最後の block が `1` でなければ、
parent は最後の block を `1` だけ短くする。
-/
theorem parityParent_blocks_of_last_ne_one
    {n : ℕ}
    (c : ParityComposition (n + 1))
    (hLast :
      parityLastBlock (by omega : 0 < n + 1) c ≠ 1) :
    (parityParent c).blocks =
      c.blocks.dropLast ++
        [parityLastBlock (by omega : 0 < n + 1) c - 1] := by
  let hne :=
    parityComposition_blocks_ne_nil
      (by omega : 0 < n + 1) c
  have ha :
      c.blocks.getLast hne ≠ 1 := by
    intro h
    apply hLast
    unfold parityLastBlock
    simpa using h
  simp only [parityParent]
  simp [ha, parityLastBlock]

/-- append-zero を parent に戻すと元の composition。 -/
@[simp] theorem parityParent_appendZero
    {n : ℕ}
    (hn : 0 < n)
    (c : ParityComposition n) :
    parityParent (parityAppendZero hn c) = c := by
  apply Composition.ext
  have hLastPos :
      0 < parityLastBlock hn c :=
    parityLastBlock_pos hn c
  have hChildLastNe :
      parityLastBlock
          (by omega : 0 < n + 1)
          (parityAppendZero hn c) ≠ 1 := by
    rw [parityAppendZero_lastBlock]
    omega
  rw [parityParent_blocks_of_last_ne_one
        (parityAppendZero hn c) hChildLastNe]
  rw [parityAppendZero_dropLast]
  rw [parityAppendZero_lastBlock]
  simp only [Nat.add_sub_cancel]
  let hne := parityComposition_blocks_ne_nil hn c
  change
    c.blocks.dropLast ++ [c.blocks.getLast hne] =
      c.blocks
  exact List.dropLast_append_getLast hne

/--
child の最後の block が `1` なら、
parent は最後の block を一つ落とす。
-/
theorem parityParent_blocks_of_last_eq_one
    {n : ℕ}
    (c : ParityComposition (n + 1))
    (hLast :
      parityLastBlock (by omega : 0 < n + 1) c = 1) :
    (parityParent c).blocks = c.blocks.dropLast := by
  let hne :=
    parityComposition_blocks_ne_nil
      (by omega : 0 < n + 1) c
  have ha :
      c.blocks.getLast hne = 1 := by
    unfold parityLastBlock at hLast
    simpa using hLast
  simp only [parityParent]
  simp [ha]

/-- append-one を parent に戻すと元の composition。 -/
@[simp] theorem parityParent_appendOne
    {n : ℕ}
    (c : ParityComposition n) :
    parityParent (parityAppendOne c) = c := by
  apply Composition.ext
  rw [
    parityParent_blocks_of_last_eq_one
      (parityAppendOne c)
      (parityAppendOne_lastBlock c)
  ]
  change (c.blocks ++ [1]).dropLast = c.blocks
  simp

/-- append-zero の最後の bit は false。 -/
@[simp] theorem parityLastBit_appendZero
    {n : ℕ}
    (hn : 0 < n)
    (c : ParityComposition n) :
    parityLastBit (parityAppendZero hn c) = false := by
  unfold parityLastBit
  rw [parityAppendZero_lastBlock]
  simp only [Nat.add_eq_right, decide_eq_false_iff_not]
  exact Nat.ne_of_gt (parityLastBlock_pos hn c)

/-- append-one の最後の bit は true。 -/
@[simp] theorem parityLastBit_appendOne
    {n : ℕ}
    (c : ParityComposition n) :
    parityLastBit (parityAppendOne c) = true := by
  unfold parityLastBit
  rw [parityAppendOne_lastBlock]
  simp

/-- parent と最後の bit から child を exact に復元する。 -/
theorem append_parent_lastBit
    {n : ℕ}
    (hn : 0 < n)
    (c : ParityComposition (n + 1)) :
    (if parityLastBit c then
        parityAppendOne (parityParent c)
      else
        parityAppendZero hn (parityParent c)) = c := by
  let hcpos : 0 < n + 1 := by omega
  let hne : c.blocks ≠ [] :=
    parityComposition_blocks_ne_nil hcpos c
  by_cases hLast :
      parityLastBlock hcpos c = 1
  · -- 最後の block が 1 の場合は append-one 側。
    have hb : parityLastBit c = true := by
      unfold parityLastBit
      simp [hLast]
    simp only [hb, ↓reduceIte]
    apply Composition.ext
    -- append-one の block 列だけを露出する。
    change (parityParent c).blocks ++ [1] = c.blocks
    -- parent は最後の 1-block を落としたもの。
    rw [parityParent_blocks_of_last_eq_one c hLast]
    -- 元の getLast も 1 である。
    have hGetLast :
        c.blocks.getLast hne = 1 := by
      simpa [parityLastBlock] using hLast
    -- dropLast と最後の要素を再結合する。
    have hRestore :
        c.blocks.dropLast ++ [c.blocks.getLast hne] =
          c.blocks :=
      List.dropLast_append_getLast hne
    simpa [hGetLast] using hRestore
  · -- 最後の block が 1 でない場合は append-zero 側。
    have hb : parityLastBit c = false := by
      unfold parityLastBit
      simp [hLast]
    simp only [hb, Bool.false_eq_true, ↓reduceIte]
    apply Composition.ext
    -- parent の block 列。
    have hParent :
        (parityParent c).blocks =
          c.blocks.dropLast ++
            [parityLastBlock hcpos c - 1] :=
      parityParent_blocks_of_last_ne_one c hLast
    -- parent の最後の block は元の最後の block - 1。
    have hParentLast :
        parityLastBlock hn (parityParent c) =
          parityLastBlock hcpos c - 1 := by
      simp [parityLastBlock, hParent]
    -- append-zero の block 列を露出する。
    rw [parityAppendZero_blocks hn (parityParent c)]
    rw [hParent, hParentLast]
    -- 元の最後の block は正で、しかも 1 ではないので 2 以上。
    have hLastPos :
        0 < parityLastBlock hcpos c :=
      parityLastBlock_pos hcpos c
    have hLastGt :
        1 < parityLastBlock hcpos c := by
      omega
    have hSub :
        parityLastBlock hcpos c - 1 + 1 =
          parityLastBlock hcpos c := by
      omega
    -- 一度追加した末尾を dropLast すると元の dropLast に戻る。
    have hDrop :
        (c.blocks.dropLast ++
            [parityLastBlock hcpos c - 1]).dropLast =
          c.blocks.dropLast := by
      simp
    rw [hDrop, hSub]
    -- 最後に dropLast と元の最後の block を再結合する。
    have hRestore :
        c.blocks.dropLast ++ [c.blocks.getLast hne] =
          c.blocks :=
      List.dropLast_append_getLast hne
    simpa [parityLastBlock] using hRestore

/--
positive physical depth では「末尾 bit を一つ加える」ことが exact な二分木になる。
-/
noncomputable def parityCompositionBranchEquiv
    (n : ℕ)
    (hn : 0 < n) :
    (ParityComposition n × Bool) ≃ ParityComposition (n + 1) where
  toFun code := if code.2 then parityAppendOne code.1 else parityAppendZero hn code.1
  invFun c := (parityParent c, parityLastBit c)
  left_inv code := by
    rcases code with ⟨c, b⟩
    cases b <;> simp
  right_inv c := by
    exact append_parent_lastBit hn c

/-- positive depth `n` の parity compositions は `2^(n-1)` 個。 -/
theorem parityComposition_card
    (n : ℕ) :
    Fintype.card (ParityComposition n) = 2 ^ (n - 1) := by
  exact composition_card n

end Bridge
end Collatz3
