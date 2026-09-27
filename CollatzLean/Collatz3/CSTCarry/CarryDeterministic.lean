import CollatzLean.Collatz3.CSTCarry.FerrersCarry
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Collatz3 CSTCarry: 三進 carry recurrence の決定的実現

`CarryRealizes` は relation として定義されているが、modulus が `2^H` なら
各 row の digit は mod 3 で一意に決まる。

一 row の equation

  E + defect + 2^H * a = 3 * E'

を mod 3 で読むと、`2^H` は unit なので `a ∈ {0,1,2}` が一意になる。
このファイルでは

1. `2^H` の mod 3 unit、
2. canonical digit、
3. digit range、
4. numerator の 3 divisibility、
5. canonical next carry、
6. deterministic run、
7. run が `CarryRealizes` を実現、
8. `CarryRealizes` の一意性、
9. existence + uniqueness、

を profile / first-passage 仮定なしで証明する。
-/

namespace Collatz3
namespace CSTCarry

/-- `2^H` を `ZMod 3` の unit として読む。 -/
def twoPowModThreeUnit (H : ℕ) : (ZMod 3)ˣ :=
  ZMod.unitOfCoprime
    (2 ^ H)
    ((by decide : Nat.Coprime 2 3).pow_left H)

/--
一 row の carry equation を満たす canonical ternary digit class。

`2^H * a = -(E + defect) (mod 3)` を unit inverse で解く。
-/
def canonicalCarryDigitClass
    (H E : ℕ)
    (R : FerrersRow) : ZMod 3 :=
  (↑((twoPowModThreeUnit H)⁻¹) : ZMod 3) *
    (-(((E + R.defect : ℕ) : ZMod 3)))

/-- canonical digit class は一 row の mod 3 equation を満たす。 -/
theorem canonicalCarryDigitClass_spec
    (H E : ℕ)
    (R : FerrersRow) :
    (((E + R.defect : ℕ) : ZMod 3)) +
        (((2 ^ H : ℕ) : ZMod 3) * canonicalCarryDigitClass H E R) = 0 := by
  have hleading :
      (((2 ^ H : ℕ) : ZMod 3)) =
        (↑(twoPowModThreeUnit H) : ZMod 3) := by
    simp [twoPowModThreeUnit]
  unfold canonicalCarryDigitClass
  rw [hleading]
  simp [← mul_assoc]

/-- mod 3 equation の解 class は一意。 -/
theorem canonicalCarryDigitClass_unique
    (H E : ℕ)
    (R : FerrersRow)
    (x : ZMod 3)
    (hx :
      (((E + R.defect : ℕ) : ZMod 3)) +
          (((2 ^ H : ℕ) : ZMod 3) * x) = 0) :
    x = canonicalCarryDigitClass H E R := by
  have hleading :
      (((2 ^ H : ℕ) : ZMod 3)) =
        (↑(twoPowModThreeUnit H) : ZMod 3) := by
    simp [twoPowModThreeUnit]
  have hx' :
      (↑(twoPowModThreeUnit H) : ZMod 3) * x =
        -(((E + R.defect : ℕ) : ZMod 3)) := by
    rw [← hleading]
    exact eq_neg_of_add_eq_zero_right hx
  calc
    x =
        (↑((twoPowModThreeUnit H)⁻¹) : ZMod 3) *
          ((↑(twoPowModThreeUnit H) : ZMod 3) * x) := by
            simp [← mul_assoc]
    _ =
        (↑((twoPowModThreeUnit H)⁻¹) : ZMod 3) *
          (-(((E + R.defect : ℕ) : ZMod 3))) := by
            rw [hx']
    _ = canonicalCarryDigitClass H E R := rfl

/-- canonical ternary digit は class の最小非負代表。 -/
def canonicalCarryDigit
    (H E : ℕ)
    (R : FerrersRow) : ℕ :=
  (canonicalCarryDigitClass H E R).val

/-- canonical digit は必ず `0,1,2`。 -/
theorem canonicalCarryDigit_lt_three
    (H E : ℕ)
    (R : FerrersRow) :
    canonicalCarryDigit H E R < 3 := by
  exact ZMod.val_lt (canonicalCarryDigitClass H E R)

/--
任意の valid step equation に現れる digit は canonical digit と一致する。
これが局所一意性の中心補題。
-/
theorem canonicalCarryDigit_eq_of_step
    {H E : ℕ}
    {R : FerrersRow}
    {a E' : ℕ}
    (ha : a < 3)
    (hEq : E + R.defect + 2 ^ H * a = 3 * E') :
    a = canonicalCarryDigit H E R := by
  have hx :
      ((a : ℕ) : ZMod 3) = canonicalCarryDigitClass H E R := by
    apply canonicalCarryDigitClass_unique
    have hCast := congrArg (fun n : ℕ => (n : ZMod 3)) hEq
    have hThree : ((3 : ℕ) : ZMod 3) = 0 := by
      rfl
    have hZero : ((3 * E' : ℕ) : ZMod 3) = 0 := by
      rw [Nat.cast_mul]
      rw [hThree]
      simp
    rw [hZero] at hCast
    simpa using hCast
  have hVal := congrArg ZMod.val hx
  simpa [canonicalCarryDigit, ZMod.val_natCast, Nat.mod_eq_of_lt ha] using hVal

/-- canonical numerator は必ず 3 で割り切れる。 -/
theorem three_dvd_canonicalCarryNumerator
    (H E : ℕ)
    (R : FerrersRow) :
    3 ∣ E + R.defect + 2 ^ H * canonicalCarryDigit H E R := by
  rw [← ZMod.natCast_eq_zero_iff]
  have hSpec := canonicalCarryDigitClass_spec H E R
  simpa [canonicalCarryDigit, ZMod.natCast_zmod_val] using hSpec

/-- 一 row 後の canonical carry。 -/
def canonicalNextCarry
    (H E : ℕ)
    (R : FerrersRow) : ℕ :=
  (E + R.defect + 2 ^ H * canonicalCarryDigit H E R) / 3

/-- canonical digit / next carry は元の row equation を exact に満たす。 -/
theorem canonicalNextCarry_spec
    (H E : ℕ)
    (R : FerrersRow) :
    E + R.defect + 2 ^ H * canonicalCarryDigit H E R =
      3 * canonicalNextCarry H E R := by
  unfold canonicalNextCarry
  exact (Nat.mul_div_cancel' (three_dvd_canonicalCarryNumerator H E R)).symm

/--
row list 全体を決定的に走らせる。
返り値は `(digits, finalCarry)`。
-/
def canonicalCarryRun (H : ℕ) :
    List FerrersRow → ℕ → List ℕ × ℕ
  | [], E => ([], E)
  | R :: Rs, E =>
      let a := canonicalCarryDigit H E R
      let E' := canonicalNextCarry H E R
      let tail := canonicalCarryRun H Rs E'
      (a :: tail.1, tail.2)

/-- deterministic run の digit list。 -/
def canonicalCarryDigits
    (H : ℕ)
    (rows : List FerrersRow)
    (E : ℕ) : List ℕ :=
  (canonicalCarryRun H rows E).1

/-- deterministic run の final carry。 -/
def canonicalFinalCarry
    (H : ℕ)
    (rows : List FerrersRow)
    (E : ℕ) : ℕ :=
  (canonicalCarryRun H rows E).2

@[simp] theorem canonicalCarryDigits_nil
    (H E : ℕ) :
    canonicalCarryDigits H [] E = [] := by
  rfl

@[simp] theorem canonicalFinalCarry_nil
    (H E : ℕ) :
    canonicalFinalCarry H [] E = E := by
  rfl

@[simp] theorem canonicalCarryDigits_cons
    (H E : ℕ)
    (R : FerrersRow)
    (Rs : List FerrersRow) :
    canonicalCarryDigits H (R :: Rs) E =
      canonicalCarryDigit H E R ::
        canonicalCarryDigits H Rs (canonicalNextCarry H E R) := by
  rfl

@[simp] theorem canonicalFinalCarry_cons
    (H E : ℕ)
    (R : FerrersRow)
    (Rs : List FerrersRow) :
    canonicalFinalCarry H (R :: Rs) E =
      canonicalFinalCarry H Rs (canonicalNextCarry H E R) := by
  rfl

/-- deterministic run は `CarryRealizes` を構成する。 -/
theorem canonicalCarryRun_realizes
    (H : ℕ)
    (rows : List FerrersRow)
    (E : ℕ) :
    CarryRealizes (2 ^ H) rows E
      (canonicalCarryDigits H rows E)
      (canonicalFinalCarry H rows E) := by
  induction rows generalizing E with
  | nil =>
      exact CarryRealizes.nil E
  | cons R Rs ih =>
      refine CarryRealizes.cons
        (R := R) (Rs := Rs) (E := E)
        (a := canonicalCarryDigit H E R)
        (E' := canonicalNextCarry H E R)
        (F := canonicalFinalCarry H Rs (canonicalNextCarry H E R))
        (digits := canonicalCarryDigits H Rs (canonicalNextCarry H E R))
        ?_ ?_ ?_
      · exact canonicalCarryDigit_lt_three H E R
      · exact canonicalNextCarry_spec H E R
      · exact ih (canonicalNextCarry H E R)

namespace CarryRealizes

/--
任意の `CarryRealizes (2^H)` witness は deterministic run と exact に一致する。
-/
theorem eq_canonical_twoPow
    {H : ℕ}
    {rows : List FerrersRow}
    {E F : ℕ}
    {digits : List ℕ}
    (h : CarryRealizes (2 ^ H) rows E digits F) :
    digits = canonicalCarryDigits H rows E ∧
      F = canonicalFinalCarry H rows E := by
  induction h with
  | nil E =>
      simp
  | cons R Rs E a E' F digits ha hEq hTail ih =>
      have haEq : a = canonicalCarryDigit H E R :=
        canonicalCarryDigit_eq_of_step ha hEq
      have hCanonicalEq := canonicalNextCarry_spec H E R
      have hNext : E' = canonicalNextCarry H E R := by
        rw [haEq] at hEq
        omega
      subst E'
      constructor
      · simp [haEq, ih.1]
      · simpa using ih.2

/-- 同じ rows / initial carry に対する `CarryRealizes` witness は一意。 -/
theorem unique_twoPow
    {H : ℕ}
    {rows : List FerrersRow}
    {E F₁ F₂ : ℕ}
    {digits₁ digits₂ : List ℕ}
    (h₁ : CarryRealizes (2 ^ H) rows E digits₁ F₁)
    (h₂ : CarryRealizes (2 ^ H) rows E digits₂ F₂) :
    digits₁ = digits₂ ∧ F₁ = F₂ := by
  rcases h₁.eq_canonical_twoPow with ⟨hD₁, hF₁⟩
  rcases h₂.eq_canonical_twoPow with ⟨hD₂, hF₂⟩
  exact ⟨hD₁.trans hD₂.symm, hF₁.trans hF₂.symm⟩

end CarryRealizes

/-- 任意の rows / initial carry に canonical realization が存在する。 -/
theorem exists_carryRealizes_twoPow
    (H : ℕ)
    (rows : List FerrersRow)
    (E : ℕ) :
    ∃ digits F,
      CarryRealizes (2 ^ H) rows E digits F := by
  exact ⟨canonicalCarryDigits H rows E,
    canonicalFinalCarry H rows E,
    canonicalCarryRun_realizes H rows E⟩

/--
`CarryRealizes (2^H)` の `(digits, finalCarry)` pair は存在一意。
-/
theorem existsUnique_carryRealizes_twoPow
    (H : ℕ)
    (rows : List FerrersRow)
    (E : ℕ) :
    ∃! out : List ℕ × ℕ,
      CarryRealizes (2 ^ H) rows E out.1 out.2 := by
  let out : List ℕ × ℕ :=
    (canonicalCarryDigits H rows E, canonicalFinalCarry H rows E)
  refine ⟨out, ?_, ?_⟩
  · exact canonicalCarryRun_realizes H rows E
  · intro other hOther
    have hCan := hOther.eq_canonical_twoPow
    apply Prod.ext
    · simpa [out] using hCan.1
    · simpa [out] using hCan.2

end CSTCarry
end Collatz3
