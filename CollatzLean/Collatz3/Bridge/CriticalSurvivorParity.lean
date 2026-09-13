import CollatzLean.Collatz3.Bridge.CriticalAdmissibleParity
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Collatz3 Bridge: parity survivor tree

physical depth `n` の parity composition がまだ first crossing を起こしていないことを

* terminal coefficient が expansion 側 `2^n ≤ 3^m`、
* 全 proper block endpoint も expansion 側、

で表す。

block の内部では odd-step 数が固定されたまま 2-depth だけが増えるので、
各 block の右端と terminal を確認すれば全 physical prefix の安全性を捉えられる。

positive depth `n` の survivor に末尾 bit `0/1` を一つ加えると、exact に

* depth `n+1` の survivor、または
* depth `n+1` で初めて crossing する code

のどちらかになる。これを type equivalence として閉じる。
-/

namespace Collatz3
namespace Bridge

/-- depth `n` まで coefficient boundary を越えていない parity composition。 -/
def IsSurvivorParityComposition
    {n : ℕ}
    (c : ParityComposition n) : Prop :=
  2 ^ n ≤ 3 ^ c.length ∧
    ∀ k : ℕ, k < c.length →
      2 ^ c.sizeUpTo k ≤ 3 ^ k

/-- depth `n` の survivor parity code。 -/
abbrev SurvivorParityCode (n : ℕ) :=
  {c : ParityComposition n // IsSurvivorParityComposition c}

namespace IsSurvivorParityComposition

/-- survivor terminal は expansion 側。 -/
theorem terminal_safe
    {n : ℕ}
    {c : ParityComposition n}
    (h : IsSurvivorParityComposition c) :
    2 ^ n ≤ 3 ^ c.length :=
  h.1

/-- survivor の proper block endpoint も expansion 側。 -/
theorem proper_safe
    {n : ℕ}
    {c : ParityComposition n}
    (h : IsSurvivorParityComposition c)
    {k : ℕ}
    (hk : k < c.length) :
    2 ^ c.sizeUpTo k ≤ 3 ^ k :=
  h.2 k hk

end IsSurvivorParityComposition

/-- append-zero 後の proper block 条件は親 survivor から従う。 -/
theorem appendZero_proper_safe
    {n : ℕ}
    (hn : 0 < n)
    {c : ParityComposition n}
    (h : IsSurvivorParityComposition c)
    {k : ℕ}
    (hk : k < (parityAppendZero hn c).length) :
    2 ^ (parityAppendZero hn c).sizeUpTo k ≤ 3 ^ k := by
  have hk' : k < c.length := by
    simpa using hk
  rw [parityAppendZero_sizeUpTo hn c hk']
  exact h.proper_safe hk'

/-- append-one 後の proper block 条件は親 survivor から従う。 -/
theorem appendOne_proper_safe
    {n : ℕ}
    (_hn : 0 < n)
    {c : ParityComposition n}
    (h : IsSurvivorParityComposition c)
    {k : ℕ}
    (hk : k < (parityAppendOne c).length) :
    2 ^ (parityAppendOne c).sizeUpTo k ≤ 3 ^ k := by
  rw [parityAppendOne_length] at hk
  by_cases hkm : k < c.length
  · rw [parityAppendOne_sizeUpTo c (Nat.le_of_lt hkm)]
    exact h.proper_safe hkm
  · have hkEq : k = c.length := by omega
    subst k
    rw [parityAppendOne_sizeUpTo c (le_refl _)]
    rw [c.sizeUpTo_length]
    exact h.terminal_safe

/-- append-zero child が survivor なら parent も survivor。 -/
theorem survivor_parent_of_appendZero_survivor
    {n : ℕ}
    (hn : 0 < n)
    {c : ParityComposition n}
    (hChild : IsSurvivorParityComposition (parityAppendZero hn c)) :
    IsSurvivorParityComposition c := by
  constructor
  · have hTerm := hChild.terminal_safe
    rw [parityAppendZero_length] at hTerm
    have hPow : 2 ^ n ≤ 2 ^ (n + 1) :=
      Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega)
    exact le_trans hPow hTerm
  · intro k hk
    have hChildSafe := hChild.proper_safe (by simpa using hk)
    rwa [parityAppendZero_sizeUpTo hn c hk] at hChildSafe

/-- append-one child が survivor なら parent も survivor。 -/
theorem survivor_parent_of_appendOne_survivor
    {n : ℕ}
    (_hn : 0 < n)
    {c : ParityComposition n}
    (hChild : IsSurvivorParityComposition (parityAppendOne c)) :
    IsSurvivorParityComposition c := by
  constructor
  · have hSafe := hChild.proper_safe (k := c.length) (by simp)
    rw [parityAppendOne_sizeUpTo c (le_refl _), c.sizeUpTo_length] at hSafe
    exact hSafe
  · intro k hk
    have hSafe := hChild.proper_safe (k := k) (by
      rw [parityAppendOne_length]
      omega)
    rwa [parityAppendOne_sizeUpTo c (Nat.le_of_lt hk)] at hSafe

/-- append-zero child が first crossing なら parent は survivor。 -/
theorem survivor_parent_of_appendZero_firstCrossing
    {n : ℕ}
    (hn : 0 < n)
    {c : ParityComposition n}
    (hChild : IsFirstCrossingParityComposition (parityAppendZero hn c)) :
    IsSurvivorParityComposition c := by
  constructor
  · have hPrev := hChild.1
    rw [parityAppendZero_length] at hPrev
    simpa using hPrev
  · intro k hk
    have hPow := hChild.2.2 k (by simpa using hk)
    rwa [parityAppendZero_sizeUpTo hn c hk] at hPow

/-- append-one child が first crossing なら parent は survivor。 -/
theorem survivor_parent_of_appendOne_firstCrossing
    {n : ℕ}
    (_hn : 0 < n)
    {c : ParityComposition n}
    (hChild : IsFirstCrossingParityComposition (parityAppendOne c)) :
    IsSurvivorParityComposition c := by
  constructor
  · have hPow := hChild.2.2 c.length (by simp)
    rw [parityAppendOne_sizeUpTo c (le_refl _), c.sizeUpTo_length] at hPow
    exact hPow
  · intro k hk
    have hPow := hChild.2.2 k (by
      rw [parityAppendOne_length]
      omega)
    rwa [parityAppendOne_sizeUpTo c (Nat.le_of_lt hk)] at hPow

/-- parent survivor の append-zero child は terminal 判定だけで survivor / crossing に分かれる。 -/
theorem survivor_or_firstCrossing_appendZero
    {n : ℕ}
    (hn : 0 < n)
    {c : ParityComposition n}
    (h : IsSurvivorParityComposition c) :
    IsSurvivorParityComposition (parityAppendZero hn c) ∨
      IsFirstCrossingParityComposition (parityAppendZero hn c) := by
  by_cases hTerm : 2 ^ (n + 1) ≤ 3 ^ (parityAppendZero hn c).length
  · left
    exact ⟨hTerm, fun k hk => appendZero_proper_safe hn h hk⟩
  · right
    constructor
    · rw [parityAppendZero_length]
      simpa using h.terminal_safe
    · constructor
      · exact Nat.lt_of_not_ge hTerm
      · intro k hk
        exact appendZero_proper_safe hn h hk

/-- parent survivor の append-one child も terminal 判定だけで survivor / crossing に分かれる。 -/
theorem survivor_or_firstCrossing_appendOne
    {n : ℕ}
    (hn : 0 < n)
    {c : ParityComposition n}
    (h : IsSurvivorParityComposition c) :
    IsSurvivorParityComposition (parityAppendOne c) ∨
      IsFirstCrossingParityComposition (parityAppendOne c) := by
  by_cases hTerm : 2 ^ (n + 1) ≤ 3 ^ (parityAppendOne c).length
  · left
    exact ⟨hTerm, fun k hk => appendOne_proper_safe hn h hk⟩
  · right
    constructor
    · rw [parityAppendOne_length]
      have hPow : 3 ^ c.length ≤ 3 ^ (c.length + 1) :=
        Nat.pow_le_pow_right (by decide : 0 < (3 : ℕ)) (by omega)
      exact le_trans h.terminal_safe hPow
    · constructor
      · exact Nat.lt_of_not_ge hTerm
      · intro k hk
        exact appendOne_proper_safe hn h hk

/-- child survivor の parent は survivor。末尾 bit の二場合をまとめた形。 -/
theorem survivor_parent_of_survivor
    {n : ℕ}
    (hn : 0 < n)
    {c : ParityComposition (n + 1)}
    (h : IsSurvivorParityComposition c) :
    IsSurvivorParityComposition (parityParent c) := by
  have hRebuild := append_parent_lastBit hn c
  cases hb : parityLastBit c with
  | false =>
      have hc : parityAppendZero hn (parityParent c) = c := by
        simpa [hb] using hRebuild
      rw [← hc] at h
      exact survivor_parent_of_appendZero_survivor hn h
  | true =>
      have hc : parityAppendOne (parityParent c) = c := by
        simpa [hb] using hRebuild
      rw [← hc] at h
      exact survivor_parent_of_appendOne_survivor hn h

/-- child first-crossing の parent も survivor。 -/
theorem survivor_parent_of_firstCrossing
    {n : ℕ}
    (hn : 0 < n)
    {c : ParityComposition (n + 1)}
    (h : IsFirstCrossingParityComposition c) :
    IsSurvivorParityComposition (parityParent c) := by
  have hRebuild := append_parent_lastBit hn c
  cases hb : parityLastBit c with
  | false =>
      have hc : parityAppendZero hn (parityParent c) = c := by
        simpa [hb] using hRebuild
      rw [← hc] at h
      exact survivor_parent_of_appendZero_firstCrossing hn h
  | true =>
      have hc : parityAppendOne (parityParent c) = c := by
        simpa [hb] using hRebuild
      rw [← hc] at h
      exact survivor_parent_of_appendOne_firstCrossing hn h

/-- 末尾 bit に従って parity composition を一段延長する。 -/
def parityAppendBit
    {n : ℕ}
    (hn : 0 < n)
    (c : ParityComposition n)
    (b : Bool) :
    ParityComposition (n + 1) :=
  if b then parityAppendOne c else parityAppendZero hn c

@[simp] theorem parityAppendBit_false
    {n : ℕ}
    (hn : 0 < n)
    (c : ParityComposition n) :
    parityAppendBit hn c false = parityAppendZero hn c := by
  rfl

@[simp] theorem parityAppendBit_true
    {n : ℕ}
    (hn : 0 < n)
    (c : ParityComposition n) :
    parityAppendBit hn c true = parityAppendOne c := by
  rfl

/-- survivor の任意の一 bit child は survivor または first-crossing。 -/
theorem survivor_or_firstCrossing_appendBit
    {n : ℕ}
    (hn : 0 < n)
    {c : ParityComposition n}
    (h : IsSurvivorParityComposition c)
    (b : Bool) :
    IsSurvivorParityComposition (parityAppendBit hn c b) ∨
      IsFirstCrossingParityComposition (parityAppendBit hn c b) := by
  cases b with
  | false =>
      simpa [parityAppendBit] using
        (survivor_or_firstCrossing_appendZero hn h)
  | true =>
      simpa [parityAppendBit] using
        (survivor_or_firstCrossing_appendOne hn h)

/-- append-bit の parent は元の composition。 -/
@[simp] theorem parityParent_appendBit
    {n : ℕ}
    (hn : 0 < n)
    (c : ParityComposition n)
    (b : Bool) :
    parityParent (parityAppendBit hn c b) = c := by
  cases b with
  | false =>
      simp only [parityAppendBit, Bool.false_eq_true, ↓reduceIte, parityParent_appendZero]
  | true =>
      simp only [parityAppendBit, ↓reduceIte, parityParent_appendOne]

/-- append-bit 後の最後の bit は追加した bit そのもの。 -/
@[simp] theorem parityLastBit_appendBit
    {n : ℕ}
    (hn : 0 < n)
    (c : ParityComposition n)
    (b : Bool) :
    parityLastBit (parityAppendBit hn c b) = b := by
  cases b with
  | false =>
      simp only [parityAppendBit, Bool.false_eq_true, ↓reduceIte, parityLastBit_appendZero]
  | true =>
      simp only [parityAppendBit, ↓reduceIte, parityLastBit_appendOne]

/-- parent と最後の bit から append-bit で child を exact に復元する。 -/
theorem parityAppendBit_parent_lastBit
    {n : ℕ}
    (hn : 0 < n)
    (c : ParityComposition (n + 1)) :
    parityAppendBit hn (parityParent c) (parityLastBit c) = c := by
  unfold parityAppendBit
  simpa using append_parent_lastBit hn c

/--
positive depth の survivor node と末尾 bit から、その child を分類する関数。

`Or` の証明から `Sum` を直接作ると Prop から Type への large elimination になるため、
ここでは survivor かどうかを `by_cases` で判定し、否定側でのみ
既存の survivor/crossing 二分法を Prop の証明として使用する。
-/
noncomputable def survivorParityBranch
    (n : ℕ)
    (hn : 0 < n) :
    SurvivorParityCode n × Bool →
      (SurvivorParityCode (n + 1) ⊕ FirstCrossingParityCode (n + 1)) := by
  classical
  intro code
  rcases code with ⟨P, b⟩
  let child := parityAppendBit hn P.1 b
  by_cases hs : IsSurvivorParityComposition child
  · exact Sum.inl ⟨child, hs⟩
  · have hf : IsFirstCrossingParityComposition child := by
      have hEither := survivor_or_firstCrossing_appendBit hn P.2 b
      rcases hEither with hs' | hf
      · exact False.elim (hs hs')
      · exact hf
    exact Sum.inr ⟨child, hf⟩

/-- classified child から parent と最後の bit を読む逆写像。 -/
def survivorParityUnbranch
    (n : ℕ)
    (hn : 0 < n) :
    (SurvivorParityCode (n + 1) ⊕ FirstCrossingParityCode (n + 1)) →
      SurvivorParityCode n × Bool
  | Sum.inl S =>
      (⟨parityParent S.1, survivor_parent_of_survivor hn S.2⟩,
        parityLastBit S.1)
  | Sum.inr F =>
      (⟨parityParent F.1, survivor_parent_of_firstCrossing hn F.2⟩,
        parityLastBit F.1)

/-- branch の直後に unbranch すると元の parent と bit に戻る。 -/
theorem survivorParityUnbranch_branch
    {n : ℕ}
    (hn : 0 < n)
    (code : SurvivorParityCode n × Bool) :
    survivorParityUnbranch n hn (survivorParityBranch n hn code) = code := by
  classical
  rcases code with ⟨P, b⟩
  by_cases hs : IsSurvivorParityComposition (parityAppendBit hn P.1 b)
  · simp [survivorParityBranch, survivorParityUnbranch, hs]
  · simp [survivorParityBranch, survivorParityUnbranch, hs]

/-- unbranch の直後に branch すると元の classified child に戻る。 -/
theorem survivorParityBranch_unbranch
    {n : ℕ}
    (hn : 0 < n)
    (code : SurvivorParityCode (n + 1) ⊕ FirstCrossingParityCode (n + 1)) :
    survivorParityBranch n hn (survivorParityUnbranch n hn code) = code := by
  classical
  rcases code with S | F
  · let P : SurvivorParityCode n :=
      ⟨parityParent S.1, survivor_parent_of_survivor hn S.2⟩
    let b : Bool := parityLastBit S.1
    have hRebuild : parityAppendBit hn P.1 b = S.1 := by
      dsimp [P, b]
      exact parityAppendBit_parent_lastBit hn S.1
    have hs : IsSurvivorParityComposition (parityAppendBit hn P.1 b) := by
      rw [hRebuild]
      exact S.2
    have hsS : IsSurvivorParityComposition S.1 := S.2
    simp [survivorParityBranch, survivorParityUnbranch, P, b, hRebuild, hsS]
  · let P : SurvivorParityCode n :=
      ⟨parityParent F.1, survivor_parent_of_firstCrossing hn F.2⟩
    let b : Bool := parityLastBit F.1
    have hRebuild : parityAppendBit hn P.1 b = F.1 := by
      dsimp [P, b]
      exact parityAppendBit_parent_lastBit hn F.1
    have hf : IsFirstCrossingParityComposition (parityAppendBit hn P.1 b) := by
      rw [hRebuild]
      exact F.2
    have hnots : ¬ IsSurvivorParityComposition (parityAppendBit hn P.1 b) := by
      intro hs
      have hSafe := hs.terminal_safe
      have hCross := hf.2.1
      omega
    have hnotsF : ¬ IsSurvivorParityComposition F.1 := by
      intro hsF
      apply hnots
      rw [hRebuild]
      exact hsF
    simp [survivorParityBranch, survivorParityUnbranch, P, b, hnotsF, hRebuild]

/--
positive depth の survivor tree の exact branch decomposition。
各 survivor node の二 children は survivor または new first-crossing に一意に分かれる。
-/
noncomputable def survivorParityBranchEquiv
    (n : ℕ)
    (hn : 0 < n) :
    (SurvivorParityCode n × Bool) ≃
      (SurvivorParityCode (n + 1) ⊕ FirstCrossingParityCode (n + 1)) where
  toFun := survivorParityBranch n hn
  invFun := survivorParityUnbranch n hn
  left_inv := survivorParityUnbranch_branch hn
  right_inv := survivorParityBranch_unbranch hn

/-- survivor code 数。 -/
noncomputable def survivorParityCount (n : ℕ) : ℕ :=
  Nat.card (SurvivorParityCode n)

/-- first-crossing code 数。 -/
noncomputable def firstCrossingParityCount (n : ℕ) : ℕ :=
  Nat.card (FirstCrossingParityCode n)

/-- depth `1` の survivor code の block list は必ず `[1]`。 -/
theorem survivorParityCode_one_blocks
    (S : SurvivorParityCode 1) :
    S.1.blocks = [1] := by
  have hle : S.1.length ≤ 1 := S.1.length_le
  cases hblocks : S.1.blocks with
  | nil =>
      have hsum := S.1.blocks_sum
      rw [hblocks] at hsum
      simp at hsum
  | cons a tail =>
      cases tail with
      | nil =>
          have hsum := S.1.blocks_sum
          rw [hblocks] at hsum
          simp at hsum
          subst a
          rfl
      | cons b tail =>
          have hbad : 2 ≤ S.1.length := by
            simp [Composition.length, hblocks]
          omega

/-- depth `1` の survivor code は unit と同値。 -/
noncomputable def survivorParityCodeOneEquivUnit :
    SurvivorParityCode 1 ≃ Unit where
  toFun _ := ()
  invFun _ := by
    let c : Composition 1 := Composition.single 1 (by omega)
    refine ⟨c, ?_⟩
    constructor
    · have hlen : c.length = 1 := by
        simp [c, Composition.length, Composition.single]
      rw [hlen]
      norm_num
    · intro k hk
      have hlen : c.length = 1 := by
        simp [c, Composition.length, Composition.single]
      rw [hlen] at hk
      have hk0 : k = 0 := by omega
      subst k
      simp [Composition.sizeUpTo]
  left_inv S := by
    apply Subtype.ext
    apply Composition.ext
    simpa [Composition.single] using (survivorParityCode_one_blocks S).symm
  right_inv u := by
    cases u
    rfl

/-- depth `1` には survivor code が exactly 一つある。 -/
theorem survivorParityCount_one : survivorParityCount 1 = 1 := by
  unfold survivorParityCount
  calc
    Nat.card (SurvivorParityCode 1) = Nat.card Unit :=
      Nat.card_congr survivorParityCodeOneEquivUnit
    _ = 1 := by simp

/--
branch equivalence の cardinal 版。

`2 S_n = S_(n+1) + F_(n+1)`。
-/
theorem two_mul_survivorParityCount_eq
    {n : ℕ}
    (hn : 0 < n) :
    2 * survivorParityCount n =
      survivorParityCount (n + 1) + firstCrossingParityCount (n + 1) := by
  unfold survivorParityCount firstCrossingParityCount
  have hCard := Nat.card_congr (survivorParityBranchEquiv n hn)
  have hBool : Nat.card Bool = 2 := by
    rw [Nat.card_eq_fintype_card]
    rfl
  simpa [Nat.card_prod, Nat.card_sum, hBool,
    Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hCard

end Bridge
end Collatz3
