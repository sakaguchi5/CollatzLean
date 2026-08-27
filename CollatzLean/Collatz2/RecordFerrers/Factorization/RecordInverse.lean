import CollatzLean.Collatz2.RecordFerrers.Factorization.InitialAnchorFirstCrossing

/-!
# Record–Ferrers Phase A: record decomposition reconstruction

local minimal blocks と pure carry / global chord inequalities から、新しい
`RecordChain` / `RecordDecomposition` を legacy record 実装に依存せず逆構成する。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-- nonempty minimal block list の flatten は positive odd length を持つ。 -/
theorem oddSteps_flatten_pos_of_nonempty_minimal
    (bs : List Word)
    (hNonempty : bs ≠ [])
    (hMinimal : ∀ b ∈ bs, MinimalBlock b) :
    0 < oddSteps bs.flatten := by
  cases bs with
  | nil =>
      exact False.elim (hNonempty rfl)
  | cons b bs =>
      have hMb : MinimalBlock b := hMinimal b (by simp)
      change 0 < oddSteps (b ++ bs.flatten)
      rw [oddSteps_append]
      exact Nat.add_pos_left hMb.oddSteps_pos _

/-- append boundary の global height は左 word の total depth。 -/
theorem FiberPoint.height_at_append_boundary
    {p H : ℕ}
    (x : FiberPoint p H)
    (anchor tail : Word)
    (hWord : x.word = anchor ++ tail) :
    x.height (oddSteps anchor) = twoSteps anchor := by
  unfold FiberPoint.height
  rw [hWord]
  unfold prefixTwoDepth oddSteps
  simp

/-- carry 1 は roof anchor を次の roof anchor へ送る。 -/
theorem roof_append_of_carry_one
    (anchor b : Word)
    (M : MinimalBlock b)
    (hAnchorRoof : twoSteps anchor = criticalHeight (oddSteps anchor))
    (hCarry : criticalCarry (oddSteps anchor) (oddSteps b) = 1) :
    twoSteps (anchor ++ b) = criticalHeight (oddSteps (anchor ++ b)) := by
  have hCrit := criticalHeight_add_eq (oddSteps anchor) (oddSteps b)
  rw [hCarry] at hCrit
  rw [twoSteps_append, oddSteps_append, hAnchorRoof, M.minimalDepth]
  omega

/--
factorization の先頭 block は `blockWord` で正確に切り出される。
-/
theorem blockWord_eq_head_of_factorization
    {p H : ℕ}
    (x : FiberPoint p H)
    (anchor b : Word)
    (bs : List Word)
    (hWord : x.word = anchor ++ (b :: bs).flatten) :
    blockWord x (oddSteps anchor) (oddSteps b) = b := by
  unfold blockWord
  rw [hWord]
  simp [oddSteps]


/--
factorization boundary の height は anchor の two-depth。
anchor が roof 上なら、その boundary も critical roof 上にある。
-/
theorem height_at_anchor_eq_critical
    {p H : ℕ}
    (x : FiberPoint p H)
    (anchor suffix : Word)
    (hWord : x.word = anchor ++ suffix)
    (hAnchorRoof :
      twoSteps anchor = criticalHeight (oddSteps anchor)) :
    x.height (oddSteps anchor) =
      criticalHeight (oddSteps anchor) := by
  have hBoundary :=
    FiberPoint.height_at_append_boundary
      x anchor suffix hWord
  exact hBoundary.trans hAnchorRoof


/--
whole word が `anchor ++ b` で尽きるなら、
その右 endpoint は whole fiber の terminal。
-/
theorem oddSteps_add_eq_terminal_of_append
    {p H : ℕ}
    (x : FiberPoint p H)
    (anchor b : Word)
    (hWord : x.word = anchor ++ b) :
    oddSteps anchor + oddSteps b = p := by
  have hOdd :
      oddSteps x.word = oddSteps (anchor ++ b) := by
    rw [hWord]
  rw [x.oddSteps_eq, oddSteps_append] at hOdd
  exact hOdd.symm


/--
後ろに nonempty minimal tail が残っているなら、
現在の head block の右 endpoint は terminal より真に手前。
-/
theorem oddSteps_head_lt_terminal_of_nonempty_minimal_tail
    {p H : ℕ}
    (x : FiberPoint p H)
    (anchor b : Word)
    (tailBlocks : List Word)
    (hWord :
      x.word = (anchor ++ b) ++ tailBlocks.flatten)
    (hTailNonempty : tailBlocks ≠ [])
    (hTailMinimal :
      ∀ d ∈ tailBlocks, MinimalBlock d) :
    oddSteps anchor + oddSteps b < p := by
  have hTailPos :=
    oddSteps_flatten_pos_of_nonempty_minimal
      tailBlocks hTailNonempty hTailMinimal
  have hOdd :
      oddSteps x.word =
        oddSteps ((anchor ++ b) ++ tailBlocks.flatten) := by
    rw [hWord]
  rw [x.oddSteps_eq, oddSteps_append, oddSteps_append] at hOdd
  omega


/--
`anchor ++ b` が roof prefix なら、その factorization boundary の
whole-fiber height も同じ critical roof 上にある。
-/
theorem height_after_head_eq_critical
    {p H : ℕ}
    (x : FiberPoint p H)
    (anchor b suffix : Word)
    (hWord :
      x.word = (anchor ++ b) ++ suffix)
    (hNextRoof :
      twoSteps (anchor ++ b) =
        criticalHeight (oddSteps (anchor ++ b))) :
    x.height (oddSteps anchor + oddSteps b) =
      criticalHeight (oddSteps anchor + oddSteps b) := by
  have hBoundary :=
    FiberPoint.height_at_append_boundary
      x (anchor ++ b) suffix hWord
  have hRoofBoundary :=
    hBoundary.trans hNextRoof
  simpa [oddSteps_append] using hRoofBoundary

/--
factorization の minimal head block を `RecordBlock` に昇格する。

必要なのは
- start が critical roof 上、
- endpoint が fiber 内、
- global critical-below、
- local terminal drop、
- endpoint が interior なら再び roof 上、
だけ。
-/
theorem recordBlock_of_minimal_head
    {p H : ℕ}
    (x : FiberPoint p H)
    (anchor b : Word)
    (bs : List Word)
    (hWord :
      x.word = anchor ++ (b :: bs).flatten)
    (hMb : MinimalBlock b)
    (hAnchorRoof :
      twoSteps anchor =
        criticalHeight (oddSteps anchor))
    (hEnd :
      oddSteps anchor + oddSteps b ≤ p)
    (hCriticalBelow :
      ∀ j : ℕ,
        0 < j →
        p * criticalHeight j < H * j)
    (hDropB :
      H * oddSteps b <
        p * (criticalHeight (oddSteps b) + 1))
    (hEndRoof :
      oddSteps anchor + oddSteps b < p →
        x.height (oddSteps anchor + oddSteps b) =
          criticalHeight (oddSteps anchor + oddSteps b)) :
    RecordBlock x (oddSteps anchor) (oddSteps b) := by
  have hBlockEq :
      blockWord x (oddSteps anchor) (oddSteps b) = b :=
    blockWord_eq_head_of_factorization
      x anchor b bs hWord
  have hStartRoof :
      x.height (oddSteps anchor) =
        criticalHeight (oddSteps anchor) :=
    height_at_anchor_eq_critical
      x anchor (b :: bs).flatten hWord hAnchorRoof
  have hMBlock :
      MinimalBlock
        (blockWord x (oddSteps anchor) (oddSteps b)) := by
    rw [hBlockEq]
    exact hMb
  exact
    RecordBlock.ofMinimalAtRoof
      x
      hMb.oddSteps_pos
      hEnd
      hMBlock
      hStartRoof
      (fun j hjPos _hjLt =>
        hCriticalBelow j hjPos)
      hDropB
      hEndRoof

/--
minimal head が whole factorization の最後の block なら、
それ単独で terminal `RecordChain` を構成できる。
-/
theorem recordChain_last_of_minimal_head
    {p H : ℕ}
    (x : FiberPoint p H)
    (anchor b : Word)
    (hWord :
      x.word = anchor ++ (b :: []).flatten)
    (hMb : MinimalBlock b)
    (hAnchorRoof :
      twoSteps anchor =
        criticalHeight (oddSteps anchor))
    (hCriticalBelow :
      ∀ j : ℕ,
        0 < j →
        p * criticalHeight j < H * j)
    (hDropB :
      H * oddSteps b <
        p * (criticalHeight (oddSteps b) + 1)) :
    RecordChain
      x
      (oddSteps anchor)
      ([b].map oddSteps) := by
  have hWordLast :
      x.word = anchor ++ b := by
    simpa using hWord
  have hTerminal :
      oddSteps anchor + oddSteps b = p :=
    oddSteps_add_eq_terminal_of_append
      x anchor b hWordLast
  have hEnd :
      oddSteps anchor + oddSteps b ≤ p :=
    Nat.le_of_eq hTerminal
  let B :
      RecordBlock
        x
        (oddSteps anchor)
        (oddSteps b) :=
    recordBlock_of_minimal_head
      x
      anchor
      b
      []
      hWord
      hMb
      hAnchorRoof
      hEnd
      hCriticalBelow
      hDropB
      (by
        intro hInterior
        omega)
  exact RecordChain.last B hTerminal

/--
minimal head の後ろに nonempty minimal tail が残っているとする。

head の右 endpoint が次の critical roof 上にあり、
tail の `RecordChain` がすでに構成されていれば、
head block を prepend して whole `RecordChain` を構成できる。
-/
theorem recordChain_cons_of_minimal_head
    {p H : ℕ}
    (x : FiberPoint p H)
    (anchor b : Word)
    (tailBlocks : List Word)
    (hWord :
      x.word = anchor ++ (b :: tailBlocks).flatten)
    (hMb : MinimalBlock b)
    (hAnchorRoof :
      twoSteps anchor =
        criticalHeight (oddSteps anchor))
    (hTailNonempty :
      tailBlocks ≠ [])
    (hTailMinimal :
      ∀ d ∈ tailBlocks, MinimalBlock d)
    (hNextRoof :
      twoSteps (anchor ++ b) =
        criticalHeight (oddSteps (anchor ++ b)))
    (hCriticalBelow :
      ∀ j : ℕ,
        0 < j →
        p * criticalHeight j < H * j)
    (hDropB :
      H * oddSteps b <
        p * (criticalHeight (oddSteps b) + 1))
    (T :
      RecordChain
        x
        (oddSteps (anchor ++ b))
        (tailBlocks.map oddSteps)) :
    RecordChain
      x
      (oddSteps anchor)
      ((b :: tailBlocks).map oddSteps) := by
  have hWordTail :
      x.word =
        (anchor ++ b) ++ tailBlocks.flatten := by
    simpa [List.append_assoc] using hWord
  have hInterior :
      oddSteps anchor + oddSteps b < p :=
    oddSteps_head_lt_terminal_of_nonempty_minimal_tail
      x
      anchor
      b
      tailBlocks
      hWordTail
      hTailNonempty
      hTailMinimal
  have hEnd :
      oddSteps anchor + oddSteps b ≤ p :=
    Nat.le_of_lt hInterior
  have hNextHeight :
      x.height (oddSteps anchor + oddSteps b) =
        criticalHeight
          (oddSteps anchor + oddSteps b) :=
    height_after_head_eq_critical
      x
      anchor
      b
      tailBlocks.flatten
      hWordTail
      hNextRoof
  let B :
      RecordBlock
        x
        (oddSteps anchor)
        (oddSteps b) :=
    recordBlock_of_minimal_head
      x
      anchor
      b
      tailBlocks
      hWord
      hMb
      hAnchorRoof
      hEnd
      hCriticalBelow
      hDropB
      (fun _ => hNextHeight)
  have T' :
      RecordChain
        x
        (oddSteps anchor + oddSteps b)
        (tailBlocks.map oddSteps) := by
    simpa [oddSteps_append] using T
  exact RecordChain.cons B hInterior T'

/--
fixed whole fiber `x` の suffix factorization
`anchor ++ bs.flatten` から record chain を構成する。

再帰本体が使う情報は
- 各 block の minimality、
- interior carry、
- global critical-below、
- 各 local terminal drop、
だけ。
-/
theorem recordChain_of_minimalBlocks
    {p H : ℕ}
    (x : FiberPoint p H)
    (anchor : Word)
    (bs : List Word)
    (hWord : x.word = anchor ++ bs.flatten)
    (hNonempty : bs ≠ [])
    (hMinimal : ∀ b ∈ bs, MinimalBlock b)
    (hAnchorRoof :
      twoSteps anchor =
        criticalHeight (oddSteps anchor))
    (hCarry :
      Skeleton.interiorCarryConditionFrom
        (oddSteps anchor)
        (bs.map oddSteps))
    (hCriticalBelow :
      ∀ j : ℕ,
        0 < j →
        p * criticalHeight j < H * j)
    (hDrop :
      ∀ b ∈ bs,
        H * oddSteps b <
          p * (criticalHeight (oddSteps b) + 1)) :
    RecordChain
      x
      (oddSteps anchor)
      (bs.map oddSteps) := by
  induction bs generalizing anchor with
  | nil =>
      exact False.elim (hNonempty rfl)
  | cons b bs ih =>
      have hMb :
          MinimalBlock b :=
        hMinimal b (by simp)
      have hDropB :
          H * oddSteps b <
            p * (criticalHeight (oddSteps b) + 1) :=
        hDrop b (by simp)
      cases bs with
      /- 最後の block。再帰は不要。 -/
      | nil =>
          exact
            recordChain_last_of_minimal_head
              x
              anchor
              b
              hWord
              hMb
              hAnchorRoof
              hCriticalBelow
              hDropB
      /- 後ろに nonempty tail が残る場合。 -/
      | cons c cs =>
          have hTailNonempty :
              (c :: cs) ≠ [] := by
            simp
          have hTailMinimal :
              ∀ d ∈ c :: cs, MinimalBlock d := by
            intro d hd
            exact
              hMinimal d
                (List.mem_cons_of_mem b hd)
          change
            criticalCarry
                (oddSteps anchor)
                (oddSteps b) = 1 ∧
              Skeleton.interiorCarryConditionFrom
                (oddSteps anchor + oddSteps b)
                ((c :: cs).map oddSteps)
            at hCarry
          have hNextRoof :
              twoSteps (anchor ++ b) =
                criticalHeight
                  (oddSteps (anchor ++ b)) :=
            roof_append_of_carry_one
              anchor
              b
              hMb
              hAnchorRoof
              hCarry.1
          have hWordTail :
              x.word =
                (anchor ++ b) ++ (c :: cs).flatten := by
            simpa [List.append_assoc] using hWord
          have hTailCarry :
              Skeleton.interiorCarryConditionFrom
                (oddSteps (anchor ++ b))
                ((c :: cs).map oddSteps) := by
            simpa [oddSteps_append] using hCarry.2
          have hTailDrop :
              ∀ d ∈ c :: cs,
                H * oddSteps d <
                  p *
                    (criticalHeight (oddSteps d) + 1) := by
            intro d hd
            exact
              hDrop d
                (List.mem_cons_of_mem b hd)
          have T :
              RecordChain
                x
                (oddSteps (anchor ++ b))
                ((c :: cs).map oddSteps) :=
            ih
              (anchor := anchor ++ b)
              hWordTail
              hTailNonempty
              hTailMinimal
              hNextRoof
              hTailCarry
              hTailDrop
          exact
            recordChain_cons_of_minimal_head
              x
              anchor
              b
              (c :: cs)
              hWord
              hMb
              hAnchorRoof
              hTailNonempty
              hTailMinimal
              hNextRoof
              hCriticalBelow
              hDropB
              T


/-- generic inverse に whole FirstCrossing を加えた genuine record decomposition。 -/
def recordDecomposition_of_minimalBlocks
    {p H : ℕ}
    (x : FiberPoint p H)
    (anchor : Word)
    (bs : List Word)
    (hWord : x.word = anchor ++ bs.flatten)
    (hNonempty : bs ≠ [])
    (hMinimal : ∀ b ∈ bs, MinimalBlock b)
    (hAnchorRoof : twoSteps anchor = criticalHeight (oddSteps anchor))
    (hCarry :
      Skeleton.interiorCarryConditionFrom
        (oddSteps anchor) (bs.map oddSteps))
    (hCriticalBelow :
      ∀ j : ℕ, 0 < j → p * criticalHeight j < H * j)
    (hDrop :
      ∀ b ∈ bs,
        H * oddSteps b < p * (criticalHeight (oddSteps b) + 1))
    (hWhole : FirstCrossing x.word) :
    RecordDecomposition x (oddSteps anchor) :=
  { lengths := bs.map oddSteps
    chain := recordChain_of_minimalBlocks
      x anchor bs hWord hNonempty hMinimal hAnchorRoof hCarry
      hCriticalBelow hDrop
    whole_firstCrossing := hWhole }

end RecordFerrers
end Collatz2
