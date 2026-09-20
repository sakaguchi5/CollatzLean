import CollatzLean.Collatz3.Binary.Complexity
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic.Ring

/-!
# Collatz3 Binary: 固定幅 block と period-break

`Mersenne` 側の base `2^n` normal form を、既存の
`Binary.HasPeriodBreakAtMost` へ運ぶための純粋な list 層。

ここでは Collatz 固有の係数は導入しない。

* `padBlock` は短い LSB-first segment を固定幅まで上位 0 で埋める。
* `concatBlocks` は block 列を一つの LSB-first word に連結する。
* 最後の block だけは canonical bit length に合わせて短くしてよい。
* period が block 幅に一致すると、不一致は隣接 block の境界不一致だけになる。

この層を分けることで、target-two の wrapped / forward / reverse は
同じ binary bookkeeping を再利用できる。
-/

namespace Collatz3
namespace Binary

/-- 短い LSB-first segment を `width` bit まで上位 0 で埋める。 -/
def padBlock (width : ℕ) (segment : List Bool) : List Bool :=
  segment ++ List.replicate (width - segment.length) false

/-- block 列を LSB-first の一語へ連結する。 -/
def concatBlocks : List (List Bool) → List Bool
  | [] => []
  | b :: bs => b ++ concatBlocks bs

/-- 同じ full block を `count` 回並べる。 -/
def repeatBlock (block : List Bool) (count : ℕ) : List Bool :=
  concatBlocks (List.replicate count block)

/--
最後だけ短い canonical block にした `count` 個の同一 digit run。

`count=0` では空、`count=m+1` では full block を `m` 個並べ、最後だけ `last` を置く。
-/
def canonicalBlockList
    (block last : List Bool) : ℕ → List (List Bool)
  | 0 => []
  | m + 1 => List.replicate m block ++ [last]

/-- `canonicalBlockList` を実際の bit word にする。 -/
def canonicalRepeat
    (block last : List Bool) (count : ℕ) : List Bool :=
  concatBlocks (canonicalBlockList block last count)

/-- 隣接 block 間の bit mismatch の総和。 -/
def adjacentMismatchSum : List (List Bool) → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: bs => mismatchCount a b + adjacentMismatchSum (b :: bs)

/--
period 計算に必要な幅条件。

最後の block は canonical に短くてよい。それより前の block はすべて exactly `width`。
-/
def BlocksAtWidth (width : ℕ) : List (List Bool) → Prop
  | [] => True
  | [b] => b.length ≤ width
  | b :: c :: bs => b.length = width ∧ BlocksAtWidth width (c :: bs)

@[simp] theorem concatBlocks_nil : concatBlocks [] = [] := rfl

@[simp] theorem concatBlocks_cons (b : List Bool) (bs : List (List Bool)) :
    concatBlocks (b :: bs) = b ++ concatBlocks bs := rfl

/-- block 連結は list append と可換。 -/
theorem concatBlocks_append
    (xs ys : List (List Bool)) :
    concatBlocks (xs ++ ys) = concatBlocks xs ++ concatBlocks ys := by
  induction xs with
  | nil => simp [concatBlocks]
  | cons x xs ih =>
      simp [concatBlocks, ih, List.append_assoc]

/-- `repeatBlock` の一段展開。 -/
@[simp] theorem repeatBlock_zero (block : List Bool) :
    repeatBlock block 0 = [] := by
  simp [repeatBlock]

@[simp] theorem repeatBlock_succ (block : List Bool) (m : ℕ) :
    repeatBlock block (m + 1) = block ++ repeatBlock block m := by
  simp [repeatBlock, List.replicate_succ]

/-- padding 後の長さ。 -/
theorem padBlock_length
    {width : ℕ} {segment : List Bool}
    (h : segment.length ≤ width) :
    (padBlock width segment).length = width := by
  simp [padBlock]
  omega

/-- 上位に false を足しても値は変わらない。 -/
theorem padBlock_value
    {width : ℕ} {segment : List Bool} :
    valueLSB (padBlock width segment) = valueLSB segment := by
  rw [padBlock, valueLSB_append]
  simp

/-- 幅を右へ `extra` bit 広げることは、full block の上位に false を追加すること。 -/
theorem padBlock_add_right
    {width extra : ℕ} {segment : List Bool}
    (h : segment.length ≤ width) :
    padBlock (width + extra) segment =
      padBlock width segment ++ List.replicate extra false := by
  unfold padBlock
  have hSub :
      width + extra - segment.length =
        (width - segment.length) + extra := by
    omega
  rw [hSub, List.replicate_add]
  simp [List.append_assoc]

/-- 同じ block の反復長。 -/
theorem repeatBlock_length
    (block : List Bool) (count : ℕ) :
    (repeatBlock block count).length = count * block.length := by
  induction count with
  | zero => simp
  | succ m ih =>
      simp [ih, Nat.add_mul]
      omega

/-- 最後だけ短くした run の長さ。 -/
theorem canonicalRepeat_length
    (block last : List Bool) : ∀ count : ℕ,
    (canonicalRepeat block last count).length =
      match count with
      | 0 => 0
      | m + 1 => m * block.length + last.length
  | 0 => by
      simp [canonicalRepeat, canonicalBlockList]
  | m + 1 => by
      simp [canonicalRepeat, canonicalBlockList, concatBlocks_append]
      simpa [repeatBlock] using repeatBlock_length block m

/-- 連結語の値は block ごとの `valueLSB_append` を繰り返したもの。 -/
theorem valueLSB_concatBlocks : ∀ blocks : List (List Bool),
    valueLSB (concatBlocks blocks) =
      match blocks with
      | [] => 0
      | b :: bs => valueLSB b + 2 ^ b.length * valueLSB (concatBlocks bs)
  | [] => rfl
  | b :: bs => by simp [concatBlocks, valueLSB_append]

/-- 自分自身の後ろに何を付けても、短い自分との比較では mismatch は 0。 -/
theorem mismatchCount_append_self_right
    (xs tail : List Bool) :
    mismatchCount (xs ++ tail) xs = 0 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp [mismatchCount, ih]

/--
右側を延長すると、元の短い右側との mismatch 数は減らない。
`ys` が左側 `xs` より長くない範囲だけを使う。
-/
theorem mismatchCount_le_append_right_of_length_le
    {xs ys tail : List Bool}
    (h : ys.length ≤ xs.length) :
    mismatchCount xs ys ≤ mismatchCount xs (ys ++ tail) := by
  induction ys generalizing xs with
  | nil => simp
  | cons y ys ih =>
      cases xs with
      | nil => simp at h
      | cons x xs =>
          simp only [List.length_cons, add_le_add_iff_right] at h
          simp only [mismatchCount, List.cons_append, add_le_add_iff_left]
          exact ih h

/--
`right` と短い `segment` の mismatch が 0 なら、`segment` までで数えた
`left` の mismatch は `right` 全体との mismatch 以下。
-/
theorem mismatchCount_le_of_right_zero
    {left right segment : List Bool}
    (hLen : segment.length ≤ right.length)
    (hZero : mismatchCount right segment = 0) :
    mismatchCount left segment ≤ mismatchCount left right := by
  induction segment generalizing left right with
  | nil => simp
  | cons s ss ih =>
      cases right with
      | nil => simp at hLen
      | cons r rs =>
          simp only [List.length_cons, add_le_add_iff_right] at hLen
          have hrs : r = s := by
            by_contra hne
            simp [mismatchCount, hne] at hZero
          subst s
          have hZeroTail : mismatchCount rs ss = 0 := by
            simpa [mismatchCount] using hZero
          cases left with
          | nil => simp
          | cons l ls =>
              have hTail := ih (left := ls) (right := rs) hLen hZeroTail
              by_cases hlr : l = r <;> simp [mismatchCount, hlr, hTail]

/-- 同長 segment 同士の比較は、その後ろの比較と分離できる。 -/
theorem mismatchCount_append_of_length_eq
    {a b c d : List Bool}
    (h : a.length = b.length) :
    mismatchCount (a ++ c) (b ++ d) =
      mismatchCount a b + mismatchCount c d := by
  induction a generalizing b with
  | nil =>
      cases b with
      | nil => simp [mismatchCount]
      | cons _ _ => simp at h
  | cons x xs ih =>
      cases b with
      | nil => simp at h
      | cons y ys =>
          simp at h
          simp [mismatchCount, ih h]
          omega

/-- 同じだけ上位 0 を追加しても二 block 間の mismatch 数は変わらない。 -/
theorem mismatchCount_padBlock_add_right
    {width extra : ℕ} {p q : List Bool}
    (hp : p.length ≤ width)
    (hq : q.length ≤ width) :
    mismatchCount (padBlock (width + extra) p)
        (padBlock (width + extra) q) =
      mismatchCount (padBlock width p) (padBlock width q) := by
  rw [padBlock_add_right hp, padBlock_add_right hq]
  have hLen : (padBlock width p).length = (padBlock width q).length := by
    rw [padBlock_length hp, padBlock_length hq]
  rw [mismatchCount_append_of_length_eq hLen]
  simp

/-- 右側が左 segment より短ければ、左側の後続 tail は比較されない。 -/
theorem mismatchCount_append_left_of_right_length_le
    {a c b : List Bool}
    (h : b.length ≤ a.length) :
    mismatchCount (a ++ c) b = mismatchCount a b := by
  induction b generalizing a with
  | nil => simp
  | cons y ys ih =>
      cases a with
      | nil => simp at h
      | cons x xs =>
          simp at h
          simp [mismatchCount, ih h]

/-- `length` 個落とせば append の後半だけが残る。 -/
theorem drop_append_length
    (a b : List Bool) :
    (a ++ b).drop a.length = b := by
  induction a with
  | nil => simp
  | cons x xs ih => simp [ih]

/-- list 長以上を drop すれば空。 -/
theorem drop_eq_nil_of_length_le
    {xs : List Bool} {n : ℕ}
    (h : xs.length ≤ n) :
    xs.drop n = [] := by
  exact List.drop_eq_nil_iff.mpr h

/--
固定幅 block 列では、period `width` の mismatch は隣接 block mismatch の総和に一致する。
最後の block だけは `width` 以下なら短くてよい。
-/
theorem periodBreakCount_concatBlocks
    {width : ℕ} {blocks : List (List Bool)}
    (hWidth : BlocksAtWidth width blocks) :
    periodBreakCount width (concatBlocks blocks) =
      adjacentMismatchSum blocks := by
  induction blocks with
  | nil => simp [periodBreakCount, concatBlocks, adjacentMismatchSum]
  | cons a blocks ih =>
      cases blocks with
      | nil =>
          have ha : a.length ≤ width := by
            simpa [BlocksAtWidth] using hWidth
          have hDrop : a.drop width = [] := drop_eq_nil_of_length_le ha
          simp [periodBreakCount, concatBlocks, adjacentMismatchSum, hDrop]
      | cons b bs =>
          have ha : a.length = width := hWidth.1
          have hTail : BlocksAtWidth width (b :: bs) := hWidth.2
          have ihTail := ih hTail
          have hDropA :
              (a ++ concatBlocks (b :: bs)).drop width =
                concatBlocks (b :: bs) := by
            rw [← ha]
            exact drop_append_length a (concatBlocks (b :: bs))
          cases bs with
          | nil =>
              have hb : b.length ≤ width := by
                simpa [BlocksAtWidth] using hTail
              have hba : b.length ≤ a.length := by simpa [ha] using hb
              rw [periodBreakCount, concatBlocks, hDropA]
              simpa [concatBlocks, adjacentMismatchSum] using
                (mismatchCount_append_left_of_right_length_le hba)
          | cons c cs =>
              have hb : b.length = width := hTail.1
              have hDropB :
                  (concatBlocks (b :: c :: cs)).drop width =
                    concatBlocks (c :: cs) := by
                change (b ++ concatBlocks (c :: cs)).drop width = _
                rw [← hb]
                exact drop_append_length b (concatBlocks (c :: cs))
              rw [periodBreakCount, concatBlocks, hDropA]
              change
                mismatchCount
                    (a ++ (b ++ concatBlocks (c :: cs)))
                    (b ++ concatBlocks (c :: cs)) =
                  mismatchCount a b + adjacentMismatchSum (b :: c :: cs)
              rw [mismatchCount_append_of_length_eq
                (by omega : a.length = b.length)]
              have ihTail' := ihTail
              rw [periodBreakCount, hDropB] at ihTail'
              exact congrArg (fun n => mismatchCount a b + n) ihTail'

/-- 同一 block だけなら隣接 mismatch は 0。 -/
theorem adjacentMismatchSum_replicate
    (block : List Bool) : ∀ count : ℕ,
    adjacentMismatchSum (List.replicate count block) = 0
  | 0 => by simp [adjacentMismatchSum]
  | 1 => by simp [adjacentMismatchSum]
  | m + 2 => by
      rw [List.replicate_succ, List.replicate_succ]
      change
        mismatchCount block block +
          adjacentMismatchSum (List.replicate (m + 1) block) = 0
      simp [adjacentMismatchSum_replicate block (m + 1)]

/--
正個の同一 block run の直後に `next` が来ると、内部は消えて最後の境界だけが残る。
-/
theorem adjacentMismatchSum_replicate_append_cons
    {block next : List Bool} {tail : List (List Bool)} {count : ℕ}
    (hcount : 0 < count) :
    adjacentMismatchSum
        (List.replicate count block ++ next :: tail) =
      mismatchCount block next + adjacentMismatchSum (next :: tail) := by
  induction count with
  | zero => omega
  | succ count ih =>
      cases count with
      | zero => simp [adjacentMismatchSum]
      | succ m =>
          have ih' := ih (by omega)
          rw [List.replicate_succ]
          simp only [List.cons_append]
          rw [List.replicate_succ]
          simp only [List.cons_append, adjacentMismatchSum]
          rw [mismatchCount_self, Nat.zero_add]
          simpa [List.replicate_succ] using ih'

/-- canonical run の内部 mismatch は 0。 -/
theorem adjacentMismatchSum_canonicalBlockList
    {block last : List Bool} {count : ℕ}
    (hzero : mismatchCount block last = 0) :
    adjacentMismatchSum (canonicalBlockList block last count) = 0 := by
  cases count with
  | zero => simp [canonicalBlockList, adjacentMismatchSum]
  | succ m =>
      cases m with
      | zero => simp [canonicalBlockList, adjacentMismatchSum]
      | succ j =>
          rw [canonicalBlockList]
          have h := adjacentMismatchSum_replicate_append_cons
            (block := block) (next := last) (tail := [])
            (count := j + 1) (by omega)
          simpa [hzero, adjacentMismatchSum] using h

/-- full padded block と元 segment の mismatch は 0。 -/
theorem mismatchCount_padBlock_segment
    {width : ℕ} {segment : List Bool} :
    mismatchCount (padBlock width segment) segment = 0 := by
  unfold padBlock
  exact mismatchCount_append_self_right segment _

/-- short canonical segment との比較は、full padded block との比較以下。 -/
theorem mismatchCount_segment_le_padBlock
    {width : ℕ} {left segment : List Bool}
    (hLeft : left.length = width)
    (hSegment : segment.length ≤ width) :
    mismatchCount left segment ≤
      mismatchCount left (padBlock width segment) := by
  unfold padBlock
  apply mismatchCount_le_append_right_of_length_le
  simpa [hLeft] using hSegment

/-- `BlocksAtWidth` は full block を前に何個追加しても保存される。 -/
theorem BlocksAtWidth.replicate_append
    {width : ℕ} {block : List Bool} {tail : List (List Bool)}
    (hBlock : block.length = width)
    (hTail : BlocksAtWidth width tail) :
    ∀ count : ℕ,
      BlocksAtWidth width (List.replicate count block ++ tail)
  | 0 => by simpa using hTail
  | count + 1 => by
      have ih := BlocksAtWidth.replicate_append hBlock hTail count
      rw [List.replicate_succ]
      simp only [List.cons_append]
      cases hRest : List.replicate count block ++ tail with
      | nil =>
          simp [BlocksAtWidth, hBlock]
      | cons x xs =>
          change block.length = width ∧ BlocksAtWidth width (x :: xs)
          refine ⟨hBlock, ?_⟩
          simpa [hRest] using ih

/-- canonical run は `BlocksAtWidth` を満たす。 -/
theorem BlocksAtWidth.canonicalBlockList
    {width : ℕ} {block last : List Bool} {count : ℕ}
    (hBlock : block.length = width)
    (hLast : last.length ≤ width) :
    BlocksAtWidth width (canonicalBlockList block last count) := by
  cases count with
  | zero => trivial
  | succ m =>
      apply BlocksAtWidth.replicate_append hBlock
      simp [BlocksAtWidth, hLast]

/-- `canonicalBlockList` は count>0 なら非空。 -/
theorem canonicalBlockList_nonempty
    {block last : List Bool} {count : ℕ}
    (h : 0 < count) :
    canonicalBlockList block last count ≠ [] := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt h)
  simp [canonicalBlockList]

/--
正個の `left` run の後ろに正個の canonical `right` run を置くと、
隣接 mismatch は full block 同士の境界 mismatch 以下。
-/
theorem adjacentMismatchSum_replicate_canonical_le
    {width : ℕ}
    {left right last : List Bool}
    {leftCount rightCount : ℕ}
    (hLeftCount : 0 < leftCount)
    (hRightCount : 0 < rightCount)
    (hRightLen : right.length = width)
    (hLastLen : last.length ≤ width)
    (hRightLast : mismatchCount right last = 0) :
    adjacentMismatchSum
        (List.replicate leftCount left ++
          canonicalBlockList right last rightCount) ≤
      mismatchCount left right := by
  obtain ⟨m, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hRightCount)
  cases m with
  | zero =>
      have hBoundary :
          mismatchCount left last ≤ mismatchCount left right :=
        mismatchCount_le_of_right_zero
          (by simpa [hRightLen] using hLastLen) hRightLast
      have h := adjacentMismatchSum_replicate_append_cons
        (block := left) (next := last) (tail := [])
        (count := leftCount) hLeftCount
      have hEq :
          adjacentMismatchSum (List.replicate leftCount left ++ [last]) =
            mismatchCount left last := by
        simpa [adjacentMismatchSum] using h
      calc
        adjacentMismatchSum
            (List.replicate leftCount left ++
              canonicalBlockList right last 1) =
            mismatchCount left last := by
              simpa [canonicalBlockList] using hEq
        _ ≤ mismatchCount left right := hBoundary
  | succ j =>
      have hTailZero :
          adjacentMismatchSum
              (right ::
                (List.replicate j right ++ [last])) = 0 := by
        have hCanon := adjacentMismatchSum_canonicalBlockList
          (block := right) (last := last) (count := j + 2) hRightLast
        simpa [canonicalBlockList, List.replicate_succ] using hCanon
      have h := adjacentMismatchSum_replicate_append_cons
        (block := left) (next := right)
        (tail := List.replicate j right ++ [last])
        (count := leftCount) hLeftCount
      have hEq :
          adjacentMismatchSum
              (List.replicate leftCount left ++
                canonicalBlockList right last (j + 2)) =
            mismatchCount left right := by
        simpa [canonicalBlockList, List.replicate_succ, hTailZero] using h
      exact hEq.le

/--
三つの constant block run の canonical word。
最後に存在する run だけ final block を短くして leading zero を除く。
-/
def threeRunCanonicalBlocks
    (a aLast b bLast c cLast : List Bool)
    (qa qb qc : ℕ) : List (List Bool) :=
  if 0 < qc then
    List.replicate qa a ++ List.replicate qb b ++
      canonicalBlockList c cLast qc
  else if 0 < qb then
    List.replicate qa a ++ canonicalBlockList b bLast qb
  else
    canonicalBlockList a aLast qa

/-- `threeRunCanonicalBlocks` の bit word。 -/
def threeRunCanonicalWord
    (a aLast b bLast c cLast : List Bool)
    (qa qb qc : ℕ) : List Bool :=
  concatBlocks (threeRunCanonicalBlocks a aLast b bLast c cLast qa qb qc)

/-- 三 run word は最後の canonical segment が true で終われば whole word も true で終わる。 -/
theorem threeRunCanonicalWord_eq_append_true
    {a aLast b bLast c cLast : List Bool}
    {qa qb qc : ℕ}
    (hqa : 0 < qa)
    (ha : ∃ u, aLast = u ++ [true])
    (hb : ∃ u, bLast = u ++ [true])
    (hc : ∃ u, cLast = u ++ [true]) :
    ∃ u,
      threeRunCanonicalWord a aLast b bLast c cLast qa qb qc =
        u ++ [true] := by
  unfold threeRunCanonicalWord threeRunCanonicalBlocks
  by_cases hqc : 0 < qc
  · simp only [hqc, ↓reduceIte, List.append_assoc, concatBlocks_append]
    rcases hc with ⟨u, rfl⟩
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hqc)
    simp only [canonicalBlockList, concatBlocks_append, concatBlocks_cons,
             concatBlocks_nil, List.append_nil]
    refine ⟨concatBlocks (List.replicate qa a) ++
      concatBlocks (List.replicate qb b) ++
      concatBlocks (List.replicate m c) ++ u, ?_⟩
    simp [ List.append_assoc]
  · have hqc0 : qc = 0 := Nat.eq_zero_of_not_pos hqc
    subst qc
    by_cases hqb : 0 < qb
    · simp only [lt_self_iff_false, ↓reduceIte, hqb, concatBlocks_append]
      rcases hb with ⟨u, rfl⟩
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hqb)
      refine ⟨concatBlocks (List.replicate qa a) ++
        concatBlocks (List.replicate m b) ++ u, ?_⟩
      simp [canonicalBlockList, concatBlocks_append, List.append_assoc]
    · have hqb0 : qb = 0 := Nat.eq_zero_of_not_pos hqb
      subst qb
      rcases ha with ⟨u, rfl⟩
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hqa)
      refine ⟨concatBlocks (List.replicate m a) ++ u, ?_⟩
      simp [canonicalBlockList, concatBlocks_append, List.append_assoc]

/-- 任意の Bool word の値は `2^length` 未満。 -/
theorem valueLSB_lt_two_pow_length (bits : List Bool) :
    valueLSB bits < 2 ^ bits.length := by
  induction bits with
  | nil => simp
  | cons b bs ih =>
      cases b <;>
        simp [valueLSB, pow_succ] at ih ⊢ <;>
        omega

/-- true で終わる LSB-first word はその word 長を canonical bit length に持つ。 -/
theorem hasBitLength_valueLSB_append_true (segment : List Bool) :
    HasBitLength
      (valueLSB (segment ++ [true]))
      (segment ++ [true]).length := by
  constructor
  · simp
  constructor
  · rw [valueLSB_append]
    simp
  · exact valueLSB_lt_two_pow_length _

/--
三 run canonical word の値自身は、その word 長を bit length に持つ。
-/
theorem threeRunCanonicalWord_hasBitLength
    {a aLast b bLast c cLast : List Bool}
    {qa qb qc : ℕ}
    (hqa : 0 < qa)
    (ha : ∃ u, aLast = u ++ [true])
    (hb : ∃ u, bLast = u ++ [true])
    (hc : ∃ u, cLast = u ++ [true]) :
    HasBitLength
      (valueLSB (threeRunCanonicalWord a aLast b bLast c cLast qa qb qc))
      (threeRunCanonicalWord a aLast b bLast c cLast qa qb qc).length := by
  rcases threeRunCanonicalWord_eq_append_true hqa ha hb hc with ⟨u, hu⟩
  rw [hu]
  exact hasBitLength_valueLSB_append_true u

/--
三 run canonical block list は固定幅条件を満たす。
-/
theorem threeRunCanonicalBlocks_atWidth
    {width : ℕ}
    {a aLast b bLast c cLast : List Bool}
    {qa qb qc : ℕ}
    (ha : a.length = width)
    (hb : b.length = width)
    (hc : c.length = width)
    (haLast : aLast.length ≤ width)
    (hbLast : bLast.length ≤ width)
    (hcLast : cLast.length ≤ width) :
    BlocksAtWidth width
      (threeRunCanonicalBlocks a aLast b bLast c cLast qa qb qc) := by
  unfold threeRunCanonicalBlocks
  by_cases hqc : 0 < qc
  · rw [ite_eq_left hqc]
    simpa [List.append_assoc] using
      (BlocksAtWidth.replicate_append ha
        (BlocksAtWidth.replicate_append hb
          (BlocksAtWidth.canonicalBlockList hc hcLast) qb) qa)
  · rw [ite_eq_right hqc]
    by_cases hqb : 0 < qb
    · rw [ite_eq_left hqb]
      apply BlocksAtWidth.replicate_append ha
      exact BlocksAtWidth.canonicalBlockList hb hbLast
    · rw [ite_eq_right hqb]
      exact BlocksAtWidth.canonicalBlockList ha haLast

/--
三 run canonical word の period-break 上界。

* middle と upper がある場合は `A→B` と `B→C` の二境界。
* middle が空で upper がある場合は `A→C` の一境界。
* upper が空で middle がある場合は `A→B` の一境界。
* 最初の run だけなら 0。
-/
theorem threeRunCanonical_periodBreakCount_le
    {width bound : ℕ}
    {a aLast b bLast c cLast : List Bool}
    {qa qb qc : ℕ}
    (hqa : 0 < qa)
    (ha : a.length = width)
    (hb : b.length = width)
    (hc : c.length = width)
    (haLast : aLast.length ≤ width)
    (hbLast : bLast.length ≤ width)
    (hcLast : cLast.length ≤ width)
    (haa : mismatchCount a aLast = 0)
    (hbb : mismatchCount b bLast = 0)
    (hcc : mismatchCount c cLast = 0)
    (hABBC : mismatchCount a b + mismatchCount b c ≤ bound)
    (hAC : mismatchCount a c ≤ bound)
    (hAB : mismatchCount a b ≤ bound) :
    periodBreakCount width
      (threeRunCanonicalWord a aLast b bLast c cLast qa qb qc) ≤ bound := by
  have hWidth := threeRunCanonicalBlocks_atWidth
    (qa := qa) (qb := qb) (qc := qc)
    ha hb hc haLast hbLast hcLast
  rw [threeRunCanonicalWord, periodBreakCount_concatBlocks hWidth]
  unfold threeRunCanonicalBlocks
  by_cases hqc : 0 < qc
  · rw [ite_eq_left hqc]
    by_cases hqb : 0 < qb
    · have hTail :
          adjacentMismatchSum
            (List.replicate qb b ++ canonicalBlockList c cLast qc) ≤
            mismatchCount b c :=
        adjacentMismatchSum_replicate_canonical_le
          hqb hqc hc hcLast hcc
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hqb)
      have hBoundary := adjacentMismatchSum_replicate_append_cons
        (block := a) (next := b)
        (tail := List.replicate m b ++ canonicalBlockList c cLast qc)
        (count := qa) hqa
      have hBoundary' :
          adjacentMismatchSum
              (List.replicate qa a ++ List.replicate (m + 1) b ++
                canonicalBlockList c cLast qc) =
            mismatchCount a b +
              adjacentMismatchSum
                (List.replicate (m + 1) b ++
                  canonicalBlockList c cLast qc) := by
        simpa [List.replicate_succ, List.append_assoc] using hBoundary
      rw [hBoundary']
      exact le_trans (Nat.add_le_add_left hTail _) hABBC
    · have hqb0 : qb = 0 := Nat.eq_zero_of_not_pos hqb
      subst qb
      simpa using
        (adjacentMismatchSum_replicate_canonical_le
          (width := width)
          (left := a) (right := c) (last := cLast)
          (leftCount := qa) (rightCount := qc)
          hqa hqc hc hcLast hcc).trans hAC
  · rw [ite_eq_right hqc]
    by_cases hqb : 0 < qb
    · rw [ite_eq_left hqb]
      exact
        (adjacentMismatchSum_replicate_canonical_le
          (width := width)
          (left := a) (right := b) (last := bLast)
          (leftCount := qa) (rightCount := qb)
          hqa hqb hb hbLast hbb).trans hAB
    · rw [ite_eq_right hqb]
      rw [adjacentMismatchSum_canonicalBlockList haa]
      omega

/--
正 period では word の先頭を一 bit 削っても period-break 数は増えない。
これは wrapped branch で `2*x` の binary word から `x` へ戻すために使う。
-/
theorem periodBreakCount_tail_le_cons
    {period : ℕ}
    (hperiod : 0 < period)
    (b : Bool) (bits : List Bool) :
    periodBreakCount period bits ≤
      periodBreakCount period (b :: bits) := by
  obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hperiod)
  unfold periodBreakCount
  change
    mismatchCount bits (bits.drop (p + 1)) ≤
      mismatchCount (b :: bits) (bits.drop p)
  cases hDrop : bits.drop p with
  | nil =>
      have hDropSucc : bits.drop (p + 1) = [] := by
        rw [← List.drop_drop]
        simp [hDrop]
      rw [hDropSucc]
      simp
  | cons c cs =>
      have hDropSucc : bits.drop (p + 1) = cs := by
        rw [← List.drop_drop]
        simp [hDrop]
      rw [hDropSucc]
      simp [mismatchCount]

/--
`2*x` の canonical representation から最下位の 0 を除けば `x` の canonical representationになる。
period-break 上界は保存される。
-/
theorem HasPeriodBreakAtMost.of_two_mul
    {x period bound : ℕ}
    (hx : 0 < x)
    (hperiod : 0 < period)
    (h : HasPeriodBreakAtMost (2 * x) period bound) :
    HasPeriodBreakAtMost x period bound := by
  rcases h with ⟨bits, length, hRep, hLen, hBreak⟩
  have hLengthPos : 0 < length := hLen.pos
  cases bits with
  | nil =>
      simp [RepresentsAtLength] at hRep
      omega
  | cons bit tail =>
      have hBitFalse : bit = false := by
        cases bit with
        | false => rfl
        | true =>
            have hVal := hRep.value
            simp [valueLSB] at hVal
            omega
      subst bit
      have hValTail : valueLSB tail = x := by
        have hVal := hRep.value
        simp [valueLSB] at hVal
        omega
      have hLenWord : tail.length + 1 = length := by
        have hL := hRep.length
        simp at hL
        omega
      have hLengthTwo : 2 ≤ length := by
        by_contra hNot
        have hEqOne : length = 1 := by omega
        rw [hEqOne] at hLen
        simp [HasBitLength] at hLen
        omega
      have hTailLen : tail.length = length - 1 := by omega
      have hTailBitLength : HasBitLength x tail.length := by
        rw [hTailLen]
        constructor
        · omega
        constructor
        · have hLow := hLen.lower
          have hExp : length - 1 = (length - 2) + 1 := by omega
          rw [hExp, pow_succ] at hLow
          have hSub : length - 1 - 1 = length - 2 := by omega
          rw [hSub]
          omega
        · have hUp := hLen.upper
          have hExp : length = (length - 1) + 1 := by omega
          rw [hExp, pow_succ] at hUp
          omega
      refine ⟨tail, tail.length, ?_, hTailBitLength, ?_⟩
      · exact ⟨rfl, hValTail⟩
      · exact le_trans
          (periodBreakCount_tail_le_cons hperiod false tail)
          hBreak

end Binary
end Collatz3
