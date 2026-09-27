import Mathlib.Tactic.Ring

/-!
# Collatz3 CSTCarry: Ferrers row と三進 carry

critical boundary の odd position `e` と actual position `d ≤ e` の差を、
一行の Ferrers defect として保存する。

row を terminal 側から読むと、各 row は

  E + B + M*a = 3*E'

という一桁の三進 carry equation を作る。
`a < 3` がその row で確定する三進 digit である。

巨大な完成 structure は作らず、row / digit encoding / recursive relation だけを置く。
-/

namespace Collatz3
namespace CSTCarry

/-- 一つの Ferrers row。`actual ≤ boundary` だけを primitive data とする。 -/
structure FerrersRow where
  boundary : ℕ
  actual : ℕ
  actual_le_boundary : actual ≤ boundary

namespace FerrersRow

/-- 一 row が affine defect に与える純 2 冪差。 -/
def defect (R : FerrersRow) : ℕ :=
  2 ^ R.boundary - 2 ^ R.actual

/-- defect は非負自然数として定義されている。 -/
theorem defect_le_twoPow_boundary (R : FerrersRow) :
    R.defect ≤ 2 ^ R.boundary := by
  simp [defect]

end FerrersRow

/--
bottom-to-top row list `B₀,B₁,...` を
`B₀ + 3 B₁ + 3² B₂ + ...` と読む。
-/
def ferrersWeightedDefect : List FerrersRow → ℕ
  | [] => 0
  | R :: Rs => R.defect + 3 * ferrersWeightedDefect Rs

/-- 三進 digit listを low digit first で自然数へ読む。 -/
def ternaryDigitsValue : List ℕ → ℕ
  | [] => 0
  | a :: as => a + 3 * ternaryDigitsValue as

@[simp] theorem ferrersWeightedDefect_nil :
    ferrersWeightedDefect [] = 0 := rfl

@[simp] theorem ferrersWeightedDefect_cons
    (R : FerrersRow) (Rs : List FerrersRow) :
    ferrersWeightedDefect (R :: Rs) =
      R.defect + 3 * ferrersWeightedDefect Rs := rfl

@[simp] theorem ternaryDigitsValue_nil :
    ternaryDigitsValue [] = 0 := rfl

@[simp] theorem ternaryDigitsValue_cons
    (a : ℕ) (as : List ℕ) :
    ternaryDigitsValue (a :: as) =
      a + 3 * ternaryDigitsValue as := rfl

/--
Ferrers rows を terminal 側から読んだ exact carry relation。

`CarryRealizes M rows E digits F` は current carry `E` から開始し、
row ごとに digit `a<3` を一桁確定して final carry `F` に到達することを表す。
-/
inductive CarryRealizes (M : ℕ) :
    List FerrersRow → ℕ → List ℕ → ℕ → Prop
  | nil (E : ℕ) : CarryRealizes M [] E [] E
  | cons
      (R : FerrersRow)
      (Rs : List FerrersRow)
      (E a E' F : ℕ)
      (digits : List ℕ)
      (ha : a < 3)
      (hEq : E + R.defect + M * a = 3 * E')
      (hTail : CarryRealizes M Rs E' digits F) :
      CarryRealizes M (R :: Rs) E (a :: digits) F

namespace CarryRealizes

/-- carry realization では digit 数と row 数が一致する。 -/
theorem digits_length_eq
    {M : ℕ} {rows : List FerrersRow}
    {E F : ℕ} {digits : List ℕ}
    (h : CarryRealizes M rows E digits F) :
    digits.length = rows.length := by
  induction h with
  | nil => rfl
  | cons R Rs E a E' F digits ha hEq hTail ih =>
      simp [ih]

/-- carry realization の全 digit は `0,1,2` のいずれか。 -/
theorem digit_lt_three
    {M : ℕ} {rows : List FerrersRow}
    {E F : ℕ} {digits : List ℕ}
    (h : CarryRealizes M rows E digits F) :
    ∀ a ∈ digits, a < 3 := by
  induction h with
  | nil => simp
  | cons R Rs E a E' F digits ha hEq hTail ih =>
      intro b hb
      simp only [List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact ha
      · exact ih b hb

/--
row recurrence の global invariant。

`E + M*C + S = 3^P*F`

ここで
* `C` は low-digit-first 三進 digit の値、
* `S` は Ferrers weighted defect、
* `P` は row 数。
-/
theorem invariant
    {M : ℕ} {rows : List FerrersRow}
    {E F : ℕ} {digits : List ℕ}
    (h : CarryRealizes M rows E digits F) :
    E + M * ternaryDigitsValue digits + ferrersWeightedDefect rows =
      3 ^ rows.length * F := by
  induction h with
  | nil E => simp
  | cons R Rs E a E' F digits ha hEq hTail ih =>
      simp only [ternaryDigitsValue_cons, ferrersWeightedDefect_cons,
        List.length_cons, pow_succ]
      calc
        E + M * (a + 3 * ternaryDigitsValue digits) +
              (R.defect + 3 * ferrersWeightedDefect Rs)
            = (E + R.defect + M * a) +
                3 * (M * ternaryDigitsValue digits +
                  ferrersWeightedDefect Rs) := by ring
        _ = 3 * E' +
                3 * (M * ternaryDigitsValue digits +
                  ferrersWeightedDefect Rs) := by rw [hEq]
        _ = 3 *
              (E' + M * ternaryDigitsValue digits +
                ferrersWeightedDefect Rs) := by ring
        _ = 3 * (3 ^ Rs.length * F) := by rw [ih]
        _ = (3 ^ Rs.length * 3) * F := by ring

/-- 初期 carry `0` なら、会話中の exact identity `M*C+S=3^P*F` を得る。 -/
theorem invariant_zero
    {M : ℕ} {rows : List FerrersRow}
    {F : ℕ} {digits : List ℕ}
    (h : CarryRealizes M rows 0 digits F) :
    M * ternaryDigitsValue digits + ferrersWeightedDefect rows =
      3 ^ rows.length * F := by
  simpa using h.invariant

end CarryRealizes
end CSTCarry
end Collatz3
