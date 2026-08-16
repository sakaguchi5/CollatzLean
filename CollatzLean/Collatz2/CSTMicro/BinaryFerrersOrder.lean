import CollatzLean.Collatz2.CSTMicro.SturmianHeight

/-!
# General CST: binary Ferrers dominance

binary word の Ferrers order を prefix odd count の dominance として読む。

  lower <= upper

とは、length と total odd count が同じで、全 prefix で
lower の odd count が upper 以下であること。

この order の strict pair では、upper から一つ `10 -> 01` を下げても
lower より下へ落ちない predecessor が必ず存在する。
これは Ferrers-minimality と explicit Sturmian profile を結ぶ純組合せ論部分。
-/

namespace Collatz2
namespace CSTMicro

/-- head 一つを読んだ prefix odd count。 -/
theorem prefixOddCount_cons_succ_general
    (b : Bool) (v : ParityWord) (j : ℕ) :
    prefixOddCount (b :: v) (j + 1) =
      bitNat b + prefixOddCount v j := by
  exact prefixOddCount_cons_succ b v j

/-- append 境界の head 直後の prefix count。 -/
theorem prefixOddCount_append_cons_at
    (u : ParityWord) (b : Bool) (v : ParityWord) :
    prefixOddCount (u ++ b :: v) (u.length + 1) =
      oddCount u + bitNat b := by
  induction u with
  | nil => simp [prefixOddCount, oddCount]
  | cons c u ih =>
      simp only [List.cons_append, List.length_cons, prefixOddCount_cons_succ_general]
      rw [ih]
      cases c <;> simp [oddCount, bitNat, Nat.add_assoc]

/-- 任意 prefix の odd count は prefix length 以下。 -/
theorem prefixOddCount_le_index (v : ParityWord) (j : ℕ) :
    prefixOddCount v j ≤ j := by
  induction v generalizing j with
  | nil => simp [prefixOddCount, oddCount]
  | cons b v ih =>
      cases j with
      | zero => simp [prefixOddCount, oddCount]
      | succ j =>
          rw [prefixOddCount_cons_succ_general]
          have hb : bitNat b ≤ 1 := by cases b <;> simp [bitNat]
          have hv := ih j
          omega

/-- prefix odd count は whole odd count 以下。 -/
theorem prefixOddCount_le_oddCount (v : ParityWord) (j : ℕ) :
    prefixOddCount v j ≤ oddCount v := by
  induction v generalizing j with
  | nil =>
      simp [prefixOddCount, oddCount]
  | cons b v ih =>
      cases j with
      | zero =>
          simp [prefixOddCount, oddCount]
      | succ j =>
          rw [prefixOddCount_cons_succ_general]
          cases b <;> simp [oddCount, bitNat]
          · simpa [oddCount] using ih j
          · simpa [oddCount] using ih j

/-- same head を付けても prefix dominance はそのまま持ち上がる。 -/
def PrefixBelow (lower upper : ParityWord) : Prop :=
  lower.length = upper.length ∧
    oddCount lower = oddCount upper ∧
    ∀ j : ℕ, j ≤ lower.length →
      prefixOddCount lower j ≤ prefixOddCount upper j

namespace PrefixBelow

/-- reflexivity。 -/
theorem refl (v : ParityWord) : PrefixBelow v v := by
  refine ⟨rfl, rfl, ?_⟩
  intro j hj
  exact Nat.le_refl _

/-- same head の tail dominance。 -/
theorem tail_of_cons_same
    (b : Bool)
    {u v : ParityWord}
    (h : PrefixBelow (b :: u) (b :: v)) :
    PrefixBelow u v := by
  rcases h with ⟨hlen, hodd, hpre⟩
  have hlen' : u.length = v.length := by simpa using hlen
  have hodd' : oddCount u = oddCount v := by
    cases b <;> simpa using hodd
  refine ⟨hlen', hodd', ?_⟩
  intro j hj
  have hs := hpre (j + 1) (by simp; omega)
  simp only [prefixOddCount_cons_succ_general] at hs
  omega

/-- same head を付ければ tail dominance から whole dominance が得られる。 -/
theorem cons_same
    (b : Bool)
    {u v : ParityWord}
    (h : PrefixBelow u v) :
    PrefixBelow (b :: u) (b :: v) := by
  rcases h with ⟨hlen, hodd, hpre⟩
  refine ⟨by simp [hlen], ?_, ?_⟩
  · cases b <;> simp [hodd]
  · intro j hj
    cases j with
    | zero => simp [prefixOddCount]
    | succ j =>
        simp only [prefixOddCount_cons_succ_general]
        exact Nat.add_le_add_left (hpre j (by simp at hj; omega)) (bitNat b)

end PrefixBelow

/-- `01 -> 10` の prefix count 差は swap 直後の一 prefix だけ。 -/
theorem prefixOddCount_swap_exact
    (left right : ParityWord)
    (j : ℕ) :
    prefixOddCount (left ++ ([true, false] ++ right)) j =
      prefixOddCount (left ++ ([false, true] ++ right)) j +
        (if j = left.length + 1 then 1 else 0) := by
  induction left generalizing j with
  | nil =>
      cases j with
      | zero =>
          simp [prefixOddCount]
      | succ j =>
          cases j with
          | zero =>
              simp [bitNat]
          | succ j =>
              simp [bitNat]
  | cons b left ih =>
      cases j with
      | zero =>
          simp [prefixOddCount]
      | succ j =>
          simp only [
            List.cons_append,
            prefixOddCount_cons_succ_general
          ]
          change
            bitNat b +
                prefixOddCount
                  (left ++ ([true, false] ++ right)) j
              =
            bitNat b +
                prefixOddCount
                  (left ++ ([false, true] ++ right)) j +
              (if j + 1 = (b :: left).length + 1
               then 1 else 0)
          rw [ih j]
          have hiff :
              (j + 1 = (b :: left).length + 1) ↔
                (j = left.length + 1) := by
            simp only [List.length_cons]
            omega
          by_cases hj : j = left.length + 1
          · have hj' :
                j + 1 = (b :: left).length + 1 :=
              hiff.mpr hj
            simp [hj,Nat.add_assoc]
          · have hj' :
                ¬ (j + 1 = (b :: left).length + 1) := by
              intro h
              exact hj (hiff.mp h)
            simp [hj, Nat.add_assoc]

namespace AdjacentFerrersSwap

/-- swap position 直後では upper prefix count が exact に 1 大きい。 -/
theorem upper_prefix_eq_lower_prefix_add_one
    (S : AdjacentFerrersSwap) :
    prefixOddCount S.upperWord (S.position + 1) =
      prefixOddCount S.lowerWord (S.position + 1) + 1 := by
  unfold upperWord lowerWord position
  simpa using
    prefixOddCount_swap_exact
      S.leftContext S.rightContext (S.leftContext.length + 1)

end AdjacentFerrersSwap

/-- false を含む word は `true^n ++ false :: rest` に一意でなくとも分解できる。 -/
theorem exists_replicate_true_append_false_of_mem
    {v : ParityWord}
    (h : false ∈ v) :
    ∃ n : ℕ, ∃ r : ParityWord,
      v = List.replicate n true ++ false :: r := by
  induction v with
  | nil => simp at h
  | cons b v ih =>
      cases b
      · exact ⟨0, v, by simp⟩
      · have hv : false ∈ v := by simpa using h
        rcases ih hv with ⟨n, r, hr⟩
        refine ⟨n + 1, r, ?_⟩
        simp [List.replicate_succ, hr]

/-- false を含まない Bool word は全部 true。 -/
theorem eq_replicate_true_of_false_not_mem
    (v : ParityWord)
    (h : false ∉ v) :
    v = List.replicate v.length true := by
  induction v with
  | nil =>
      rfl
  | cons b v ih =>
      cases b
      · exfalso
        apply h
        simp
      · have hv : false ∉ v := by
          intro hf
          apply h
          simp only [List.mem_cons]
          exact Or.inr hf
        calc
          true :: v =
              true :: List.replicate v.length true :=
            congrArg (fun w => true :: w) (ih hv)
          _ =
              List.replicate (v.length + 1) true := by
            simp only [List.replicate_succ]
          _ =
              List.replicate (true :: v).length true := by
            simp only [List.length_cons]

@[simp] theorem oddCount_replicate_true (n : ℕ) :
    oddCount (List.replicate n true) = n := by
  induction n with
  | zero => simp [oddCount]
  | succ n ih =>
      simp [List.replicate_succ, oddCount, bitNat]
      ac_rfl

/-- true の replicate は同じ true なので末尾へ一個回しても同じ。 -/
theorem true_cons_replicate_eq_append (n : ℕ) :
    true :: List.replicate n true =
      List.replicate n true ++ [true] := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [List.replicate_succ]
      change
        true :: (true :: List.replicate n true) =
          true :: (List.replicate n true ++ [true])
      exact congrArg (fun w => true :: w) ih


/-- one Ferrers step を common head の下へ持ち上げる。 -/
def FerrersStep.cons
    (b : Bool)
    {lower upper : ParityWord}
    (S : FerrersStep lower upper) :
    FerrersStep (b :: lower) (b :: upper) := by
  let E : AdjacentFerrersSwap := {
    leftContext := b :: S.edge.leftContext
    rightContext := S.edge.rightContext
  }
  refine {
    edge := E
    lower_eq := ?_
    upper_eq := ?_
  }
  · simp [E, AdjacentFerrersSwap.lowerWord, S.lower_eq]
  · simp [E, AdjacentFerrersSwap.upperWord, S.upper_eq]

/--
upper へ入る adjacent Ferrers predecessor と、
その predecessor が lower 以上であることをまとめた witness。
-/
structure FerrersPredecessorData
    (lower upper : ParityWord) where
  pred : ParityWord
  step : FerrersStep pred upper
  below : PrefixBelow lower pred

namespace FerrersPredecessorData

/-- common head の下へ predecessor witness を持ち上げる。 -/
def cons
    (b : Bool)
    {lower upper : ParityWord}
    (D : FerrersPredecessorData lower upper) :
    FerrersPredecessorData (b :: lower) (b :: upper) := {
  pred := b :: D.pred
  step := FerrersStep.cons b D.step
  below := PrefixBelow.cons_same b D.below
}

end FerrersPredecessorData

/--
`false :: lower ≤ true :: upper` で total odd count も等しければ、
upper の tail には false が必ず存在する。
-/
theorem false_mem_of_prefixBelow_false_true
    {lower upper : ParityWord}
    (hdom : PrefixBelow (false :: lower) (true :: upper)) :
    false ∈ upper := by
  by_contra hnot
  have hall :
      upper = List.replicate upper.length true :=
    eq_replicate_true_of_false_not_mem upper hnot
  have hlowerBound :
      oddCount lower ≤ lower.length :=
    oddCount_le_length lower
  have hoddEq := hdom.2.1
  have hlenEq := hdom.1
  rw [hall] at hoddEq
  simp only [oddCount, List.map_cons, bitNat, List.sum_cons, zero_add, List.map_replicate,
    List.sum_replicate,smul_eq_mul, mul_one] at hoddEq
  simp at hlenEq
  have hoddEq' :
      oddCount lower = 1 + upper.length := by
    simpa only [oddCount] using hoddEq
  omega

/--
`true^n` の直後の `10` を `01` に戻す標準 adjacent swap。
-/
def leadingTrueFerrersSwap
    (n : ℕ)
    (r : ParityWord) :
    AdjacentFerrersSwap := {
  leftContext := List.replicate n true
  rightContext := r
}

/--
upper = true^n ++ false :: r なら、
その直前にある先頭 true を使った swap の upper word は
exact に true :: upper。
-/
theorem true_cons_eq_leadingTrueFerrersSwap_upperWord
    {upper : ParityWord}
    {n : ℕ}
    {r : ParityWord}
    (hupper :
      upper =
        List.replicate n true ++ false :: r) :
    true :: upper =
      (leadingTrueFerrersSwap n r).upperWord := by
  rw [hupper]
  unfold leadingTrueFerrersSwap
  unfold AdjacentFerrersSwap.upperWord
  calc
    true :: (List.replicate n true ++ false :: r)
        =
      (true :: List.replicate n true) ++ false :: r := rfl
    _ =
      (List.replicate n true ++ [true]) ++ false :: r := by
        rw [true_cons_replicate_eq_append]
    _ =
      List.replicate n true ++ ([true, false] ++ r) := by
        simp [List.append_assoc]

/--
leading-true swap の lower word は、
swap 位置直後までに exact に n 個の true を持つ。
-/
theorem leadingTrueFerrersSwap_lower_prefix
    (n : ℕ)
    (r : ParityWord) :
    prefixOddCount
        (leadingTrueFerrersSwap n r).lowerWord
        ((leadingTrueFerrersSwap n r).position + 1)
      =
    (leadingTrueFerrersSwap n r).position := by
  simpa [
    leadingTrueFerrersSwap,
    AdjacentFerrersSwap.lowerWord,
    AdjacentFerrersSwap.position,
    bitNat
  ] using
    prefixOddCount_append_cons_at
      (List.replicate n true)
      false
      (true :: r)
/--
false/true head の strict discrepancy に対し、
upper tail の最初の false を左へ一段戻した word は
なお original lower 以上にある。
-/
theorem prefixBelow_leadingTrueFerrersSwap_lowerWord
    {lower upper : ParityWord}
    (n : ℕ)
    (r : ParityWord)
    (hdom :
      PrefixBelow
        (false :: lower)
        (true :: upper))
    (hUpperEq :
      true :: upper =
        (leadingTrueFerrersSwap n r).upperWord) :
    PrefixBelow
      (false :: lower)
      (leadingTrueFerrersSwap n r).lowerWord := by
  let E := leadingTrueFerrersSwap n r
  have hUpperEqE :
      true :: upper = E.upperWord := by
    simpa [E] using hUpperEq
  refine ⟨?_, ?_, ?_⟩
  · -- length
    calc
      (false :: lower).length
          = (true :: upper).length :=
        hdom.1
      _ = E.upperWord.length :=
        congrArg List.length hUpperEqE
      _ = E.lowerWord.length := by
        rw [E.upperWord_length, E.lowerWord_length]
  · -- total odd count
    calc
      oddCount (false :: lower)
          = oddCount (true :: upper) :=
        hdom.2.1
      _ = oddCount E.upperWord :=
        congrArg oddCount hUpperEqE
      _ = oddCount E.lowerWord := by
        rw [E.upperWord_oddCount, E.lowerWord_oddCount]
  · -- every prefix
    intro j hj
    by_cases hspecial :
        j = E.position + 1
    · -- swap 直後だけ upper/lower の prefix count が 1 違う
      subst j
      have hpos : E.position = n := by
        simp [
          E,
          leadingTrueFerrersSwap,
          AdjacentFerrersSwap.position
        ]
      have hlower :
          prefixOddCount
              (false :: lower)
              (E.position + 1)
            ≤
          E.position := by
        rw [hpos]
        rw [prefixOddCount_cons_succ_general]
        simp only [bitNat, Nat.zero_add]
        exact prefixOddCount_le_index lower n
      have hpredEq :
          prefixOddCount
              E.lowerWord
              (E.position + 1)
            =
          E.position := by
        simpa [E] using
          leadingTrueFerrersSwap_lower_prefix n r
      rw [hpredEq]
      exact hlower
    · -- それ以外では swap 前後の prefix count は同一
      have hnePos :
          j ≠ n + 1 := by
        simpa [
          E,
          leadingTrueFerrersSwap,
          AdjacentFerrersSwap.position
        ] using hspecial
      have hSwap :=
        prefixOddCount_swap_exact
          (List.replicate n true)
          r
          j
      have heq :
          prefixOddCount E.upperWord j =
            prefixOddCount E.lowerWord j := by
        simpa [
          E,
          leadingTrueFerrersSwap,
          AdjacentFerrersSwap.upperWord,
          AdjacentFerrersSwap.lowerWord,
          hnePos
        ] using hSwap
      have hOrig :=
        hdom.2.2 j hj
      rw [hUpperEqE] at hOrig
      rw [← heq]
      exact hOrig

/--
`false :: lower < true :: upper` 型の head discrepancy では、
upper の最初の false の直前で一回 Ferrers swap を戻せば
lower 以上の predecessor が得られる。
-/
theorem exists_ferrersPredecessor_false_true
    {lower upper : ParityWord}
    (hdom :
      PrefixBelow
        (false :: lower)
        (true :: upper)) :
    Nonempty
      (FerrersPredecessorData
        (false :: lower)
        (true :: upper)) := by
  have hfalse : false ∈ upper :=
    false_mem_of_prefixBelow_false_true hdom
  rcases
      exists_replicate_true_append_false_of_mem hfalse
    with ⟨n, r, hupper⟩
  let E := leadingTrueFerrersSwap n r
  have hUpperEq :
      true :: upper = E.upperWord := by
    simpa [E] using
      true_cons_eq_leadingTrueFerrersSwap_upperWord
        hupper
  have S :
      FerrersStep E.lowerWord (true :: upper) := {
    edge := E
    lower_eq := rfl
    upper_eq := hUpperEq
  }
  have hBelow :
      PrefixBelow
        (false :: lower)
        E.lowerWord := by
    exact
      prefixBelow_leadingTrueFerrersSwap_lowerWord
        n r hdom
        (by simpa [E] using hUpperEq)
  exact ⟨{
    pred := E.lowerWord
    step := S
    below := hBelow
  }⟩

/--
strict prefix dominance なら upper には、
まだ lower 以上にある adjacent Ferrers predecessor が存在する。
-/
theorem exists_ferrersPredecessor_of_prefixBelow_ne :
    ∀ {lower upper : ParityWord},
      PrefixBelow lower upper →
      lower ≠ upper →
      Nonempty (FerrersPredecessorData lower upper) := by
  intro lower upper hdom hne
  induction upper generalizing lower with
  | nil =>
      have hzero : lower.length = 0 := by
        simpa using hdom.1
      have hl : lower = [] := by
        cases lower with
        | nil =>
            rfl
        | cons a tail =>
            simp at hzero
      exact (hne hl).elim
  | cons b upper ih =>
      cases lower with
      | nil =>
          have hlen := hdom.1
          simp at hlen
      | cons a lower =>
          cases a <;> cases b
          · -- false / false
            have htail :
                PrefixBelow lower upper :=
              PrefixBelow.tail_of_cons_same false hdom
            have hneTail :
                lower ≠ upper := by
              intro h
              apply hne
              simp [h]
            rcases ih htail hneTail with ⟨D⟩
            exact ⟨
              FerrersPredecessorData.cons false D
            ⟩
          · -- false / true
            exact
              exists_ferrersPredecessor_false_true hdom
          · -- true / false は prefix dominance に反する
            have h1 :=
              hdom.2.2 1 (by simp)
            simp [bitNat] at h1
          · -- true / true
            have htail :
                PrefixBelow lower upper :=
              PrefixBelow.tail_of_cons_same true hdom
            have hneTail :
                lower ≠ upper := by
              intro h
              apply hne
              simp [h]
            rcases ih htail hneTail with ⟨D⟩
            exact ⟨
              FerrersPredecessorData.cons true D
            ⟩


namespace IsFirstPassageWord

/-- first-passage condition は prefix dominance の上向きに保存される。 -/
theorem of_prefixBelow
    {lower upper : ParityWord}
    (hLower : IsFirstPassageWord lower)
    (hdom : PrefixBelow lower upper) :
    IsFirstPassageWord upper := by
  constructor
  · intro hnil
    have hzero : lower.length = 0 := by
      have hlen := hdom.1
      rw [hnil] at hlen
      simpa using hlen
    have hlowerNil : lower = [] := by
      cases lower with
      | nil => rfl
      | cons b v => simp at hzero
    exact hLower.1 hlowerNil
  · constructor
    · intro k hkPos hkLt
      have hkLower : k < lower.length := by
        rw [hdom.1]
        exact hkLt
      have hExp := hLower.2.1 k hkPos hkLower
      unfold CoefficientExpandingAt at hExp ⊢
      have hcount := hdom.2.2 k (by omega)
      have hpow :
          3 ^ prefixOddCount lower k ≤
            3 ^ prefixOddCount upper k :=
        Nat.pow_le_pow_right (by omega : 0 < (3 : ℕ)) hcount
      exact lt_of_lt_of_le hExp hpow
    · unfold CoefficientContracting
      rw [← hdom.1, ← hdom.2.1]
      exact hLower.2.2

end IsFirstPassageWord

end CSTMicro
end Collatz2
