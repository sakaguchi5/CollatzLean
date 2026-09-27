import CollatzLean.Collatz3.CSTCarry.WrapExceptions

import Mathlib.Tactic.Ring

/-!
# Collatz3 CSTCarry: 三進 complement と final carry budget

途中 wrap は存在し得るため、final boundedness は global invariant でも読む必要がある。
このファイルでは digit `a ∈ {0,1,2}` に対する complement digit `2-a` を導入し、

  M*C + S = 3^P*F

を

  F < M  ↔  S < M*(D+1)

へ exact に変形する。

ここで

* `C` は元の ternary digit value、
* `D` は complement digit value、
* `S` は Ferrers weighted defect。

従って final carry bound は「途中で一度も wrap しない」ことではなく、
Ferrers defect 全体が complement budget に収まることと同値である。
-/

namespace Collatz3
namespace CSTCarry

/-- digit `a` の ternary complement。valid digit なら `2-a` は `0,1,2`。 -/
def ternaryComplementDigit (a : ℕ) : ℕ :=
  2 - a

/-- low-digit-first complement digit list。 -/
def ternaryComplementDigits (digits : List ℕ) : List ℕ :=
  digits.map ternaryComplementDigit

/-- complement digit listを low-digit-first 三進数として読む。 -/
def ternaryComplementValue : List ℕ → ℕ
  | [] => 0
  | a :: as => ternaryComplementDigit a + 3 * ternaryComplementValue as

@[simp] theorem ternaryComplementValue_nil :
    ternaryComplementValue [] = 0 := rfl

@[simp] theorem ternaryComplementValue_cons
    (a : ℕ) (as : List ℕ) :
    ternaryComplementValue (a :: as) =
      ternaryComplementDigit a + 3 * ternaryComplementValue as := rfl

/--
Ferrers weighted defect が ternary complement の global budget に収まるという条件。
final carry boundedness の global な正規形として使う。
-/
def ComplementBudget
    (M : ℕ)
    (rows : List FerrersRow)
    (digits : List ℕ) : Prop :=
  ferrersWeightedDefect rows <
    M * (ternaryComplementValue digits + 1)

/-- valid ternary digit は元 digit と complement digit の和が exact に 2。 -/
theorem digit_add_complement_eq_two
    {a : ℕ}
    (ha : a < 3) :
    a + ternaryComplementDigit a = 2 := by
  unfold ternaryComplementDigit
  omega

/--
valid digit list では元 value と complement value の和が `3^P-1`。
-/
theorem ternaryValue_add_complementValue
    {digits : List ℕ}
    (hDigits : ∀ a ∈ digits, a < 3) :
    ternaryDigitsValue digits + ternaryComplementValue digits =
      3 ^ digits.length - 1 := by
  induction digits with
  | nil =>
      simp
  | cons a as ih =>
      have ha : a < 3 :=
        hDigits a (by simp)
      have hTail : ∀ b ∈ as, b < 3 := by
        intro b hb
        exact hDigits b (by simp [hb])
      have hIH := ih hTail
      simp only [ternaryDigitsValue_cons, ternaryComplementValue_cons,
        List.length_cons, pow_succ]
      have hDigit := digit_add_complement_eq_two ha
      have hPowPos : 0 < 3 ^ as.length :=
        pow_pos (by decide : 0 < (3 : ℕ)) as.length
      omega

/-- valid P-digit ternary value は `3^P` 未満。 -/
theorem ternaryDigitsValue_lt_pow
    {digits : List ℕ}
    (hDigits : ∀ a ∈ digits, a < 3) :
    ternaryDigitsValue digits < 3 ^ digits.length := by
  have hComp := ternaryValue_add_complementValue hDigits
  have hPowPos : 0 < 3 ^ digits.length :=
    pow_pos (by decide : 0 < (3 : ℕ)) digits.length
  omega

/-- `2` で終わる digit list の complement list は `0` で終わる。 -/
theorem complementDigits_endsWithZero_of_endsWithTwo
    {digits : List ℕ}
    (hEnds : ∃ initDigits : List ℕ, digits = initDigits ++ [2]) :
    ∃ initDigits : List ℕ,
      ternaryComplementDigits digits = initDigits ++ [0] := by
  rcases hEnds with ⟨initDigits, rfl⟩
  refine ⟨ternaryComplementDigits initDigits, ?_⟩
  simp [ternaryComplementDigits, ternaryComplementDigit, List.map_append]

namespace CarryRealizes

/-- carry realization 自身から ternary value の canonical range を得る。 -/
theorem ternaryDigitsValue_lt_pow
    {M : ℕ}
    {rows : List FerrersRow}
    {E F : ℕ}
    {digits : List ℕ}
    (h : CarryRealizes M rows E digits F) :
    ternaryDigitsValue digits < 3 ^ rows.length := by
  have hDigits := CSTCarry.ternaryDigitsValue_lt_pow h.digit_lt_three
  rw [h.digits_length_eq] at hDigits
  exact hDigits

/--
初期 carry `0` の global invariant を complement budget へ exact に変形する。

`F < M` と

`ferrersWeightedDefect rows < M * (ternaryComplementValue digits + 1)`

は同値。
-/
theorem final_lt_modulus_iff_defect_lt_complementBudget
    {M : ℕ}
    {rows : List FerrersRow}
    {digits : List ℕ}
    {F : ℕ}
    (h : CarryRealizes M rows 0 digits F) :
    F < M ↔ ComplementBudget M rows digits := by
  unfold ComplementBudget
  let C := ternaryDigitsValue digits
  let D := ternaryComplementValue digits
  let S := ferrersWeightedDefect rows
  let P := rows.length
  have hInv : M * C + S = 3 ^ P * F := by
    simpa [C, S, P] using h.invariant_zero
  have hCompRaw := ternaryValue_add_complementValue h.digit_lt_three
  have hLen := h.digits_length_eq
  have hComp : C + D + 1 = 3 ^ P := by
    dsimp [C, D, P]
    rw [hLen] at hCompRaw
    have hPowPos : 0 < 3 ^ rows.length :=
      pow_pos (by decide : 0 < (3 : ℕ)) rows.length
    omega
  have hRight :
      3 ^ P * M = M * C + M * (D + 1) := by
    rw [← hComp]
    ring
  have hPowPos : 0 < 3 ^ P :=
    pow_pos (by decide : 0 < (3 : ℕ)) rows.length
  constructor
  · intro hF
    have hScaled : 3 ^ P * F < 3 ^ P * M :=
      (Nat.mul_lt_mul_left hPowPos).2 hF
    rw [← hInv, hRight] at hScaled
    have hBudget : S < M * (D + 1) := by
      exact Nat.add_lt_add_iff_left.mp hScaled
    simpa [S, D] using hBudget
  · intro hBudget
    have hAdd : M * C + S < M * C + M * (D + 1) := by
      --dsimp [S, D] at hBudget
      exact Nat.add_lt_add_left hBudget (M * C)
    have hScaled : 3 ^ P * F < 3 ^ P * M := by
      rw [← hInv, hRight]
      exact hAdd
    exact (Nat.mul_lt_mul_left hPowPos).1 hScaled

/--
final wrap なら complement digit list の最後は `0`。
`RowsInsideBitWidth` の下で、terminal wrapped interval が ternary `2` run になることの
complement 側の最小表現。
-/
theorem final_wrap_complement_endsWithZero_of_insideBitWidth
    {H : ℕ}
    {rows : List FerrersRow}
    {digits : List ℕ}
    {F : ℕ}
    (h : CarryRealizes (2 ^ H) rows 0 digits F)
    (hRows : RowsInsideBitWidth H rows)
    (hFinalWrap : 2 ^ H ≤ F) :
    ∃ initDigits : List ℕ,
      ternaryComplementDigits digits = initDigits ++ [0] := by
  apply complementDigits_endsWithZero_of_endsWithTwo
  exact h.final_wrap_endsWithTwo_of_insideBitWidth hRows hFinalWrap

end CarryRealizes
end CSTCarry
end Collatz3
