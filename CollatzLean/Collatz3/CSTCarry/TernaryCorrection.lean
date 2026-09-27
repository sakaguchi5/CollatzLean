import CollatzLean.Collatz3.CSTCarry.CarryDeterministic
import CollatzLean.Collatz3.CSTCarry.CarryBudget
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Positivity

/-!
# Collatz3 CSTCarry: ternary correction の canonical residue 同定

初期 carry `0` の invariant

  2^H * C + S = 3^P * F

を mod `3^P` で読むと

  S + 2^H * C = 0  (mod 3^P)

となる。
`2^H` は `3^P` と互いに素なので、`C` は exact に

  C = - (2^H)^(-1) S  (mod 3^P)

の canonical representative である。

このファイルでは deterministic recurrence の digit value を、この global residue と同定する。
-/

namespace Collatz3
namespace CSTCarry

/-- `2^H` を `ZMod (3^P)` の unit として読む。 -/
def twoPowTernaryPowerUnit
    (H P : ℕ) : (ZMod (3 ^ P))ˣ :=
  ZMod.unitOfCoprime
    (2 ^ H)
    (((by decide : Nat.Coprime 2 3).pow_left H).pow_right P)

/--
Ferrers weighted defect `S` から決まる ternary correction class。

`S + 2^H*C = 0 (mod 3^P)` の解。
-/
def ternaryCorrectionClass
    (H P S : ℕ) : ZMod (3 ^ P) :=
  (↑((twoPowTernaryPowerUnit H P)⁻¹) : ZMod (3 ^ P)) *
    (-((S : ℕ) : ZMod (3 ^ P)))

/-- ternary correction class は defining congruence を満たす。 -/
theorem ternaryCorrectionClass_spec
    (H P S : ℕ) :
    ((S : ℕ) : ZMod (3 ^ P)) +
        (((2 ^ H : ℕ) : ZMod (3 ^ P)) *
          ternaryCorrectionClass H P S) = 0 := by
  have hleading :
      (((2 ^ H : ℕ) : ZMod (3 ^ P))) =
        (↑(twoPowTernaryPowerUnit H P) : ZMod (3 ^ P)) := by
    simp [twoPowTernaryPowerUnit]
  unfold ternaryCorrectionClass
  rw [hleading]
  simp [← mul_assoc]

/-- defining congruence の解 class は一意。 -/
theorem ternaryCorrectionClass_unique
    (H P S : ℕ)
    (x : ZMod (3 ^ P))
    (hx :
      ((S : ℕ) : ZMod (3 ^ P)) +
          (((2 ^ H : ℕ) : ZMod (3 ^ P)) * x) = 0) :
    x = ternaryCorrectionClass H P S := by
  have hleading :
      (((2 ^ H : ℕ) : ZMod (3 ^ P))) =
        (↑(twoPowTernaryPowerUnit H P) : ZMod (3 ^ P)) := by
    simp [twoPowTernaryPowerUnit]
  have hx' :
      (↑(twoPowTernaryPowerUnit H P) : ZMod (3 ^ P)) * x =
        -((S : ℕ) : ZMod (3 ^ P)) := by
    rw [← hleading]
    exact eq_neg_of_add_eq_zero_right hx
  calc
    x =
        (↑((twoPowTernaryPowerUnit H P)⁻¹) : ZMod (3 ^ P)) *
          ((↑(twoPowTernaryPowerUnit H P) : ZMod (3 ^ P)) * x) := by
            simp [← mul_assoc]
    _ =
        (↑((twoPowTernaryPowerUnit H P)⁻¹) : ZMod (3 ^ P)) *
          (-((S : ℕ) : ZMod (3 ^ P))) := by
            rw [hx']
    _ = ternaryCorrectionClass H P S := rfl

/-- ternary correction の最小非負代表。 -/
def ternaryCorrection
    (H P S : ℕ) : ℕ :=
  (ternaryCorrectionClass H P S).val

/-- ternary correction は P 桁の三進範囲に入る。 -/
theorem ternaryCorrection_lt_pow
    (H P S : ℕ) :
    ternaryCorrection H P S < 3 ^ P := by
  have : NeZero (3 ^ P) := ⟨by positivity⟩
  exact ZMod.val_lt (ternaryCorrectionClass H P S)

namespace CarryRealizes

/--
初期 carry 0 の realization の ternary digit value は correction class と mod `3^P` で一致。
-/
theorem ternaryDigitsValue_mod_eq_correctionClass
    {H : ℕ}
    {rows : List FerrersRow}
    {digits : List ℕ}
    {F : ℕ}
    (h : CarryRealizes (2 ^ H) rows 0 digits F) :
    ((ternaryDigitsValue digits : ℕ) : ZMod (3 ^ rows.length)) =
      ternaryCorrectionClass H rows.length (ferrersWeightedDefect rows) := by
  apply ternaryCorrectionClass_unique
  have hInv := h.invariant_zero
  have hCast := congrArg
    (fun n : ℕ => (n : ZMod (3 ^ rows.length))) hInv
  simpa [add_comm, add_left_comm, add_assoc] using hCast

/--
## ternary correction の exact 同定

valid digit value は `3^P` 未満なので、合同だけでなく自然数として exact に一致する。
-/
theorem ternaryDigitsValue_eq_ternaryCorrection
    {H : ℕ}
    {rows : List FerrersRow}
    {digits : List ℕ}
    {F : ℕ}
    (h : CarryRealizes (2 ^ H) rows 0 digits F) :
    ternaryDigitsValue digits =
      ternaryCorrection H rows.length (ferrersWeightedDefect rows) := by
  have hClass := h.ternaryDigitsValue_mod_eq_correctionClass
  have hVal := congrArg ZMod.val hClass
  have hLt := h.ternaryDigitsValue_lt_pow
  simpa [ternaryCorrection, ZMod.val_natCast, Nat.mod_eq_of_lt hLt] using hVal

end CarryRealizes

/-- deterministic run の digit value を witness 仮定なしで global correction と同定する。 -/
theorem ternaryDigitsValue_canonicalCarryDigits
    (H : ℕ)
    (rows : List FerrersRow) :
    ternaryDigitsValue (canonicalCarryDigits H rows 0) =
      ternaryCorrection H rows.length (ferrersWeightedDefect rows) := by
  exact (canonicalCarryRun_realizes H rows 0).ternaryDigitsValue_eq_ternaryCorrection

/-- deterministic final carry の global closed form。 -/
theorem canonicalFinalCarry_global_identity
    (H : ℕ)
    (rows : List FerrersRow) :
    2 ^ H * ternaryCorrection H rows.length (ferrersWeightedDefect rows) +
        ferrersWeightedDefect rows =
      3 ^ rows.length * canonicalFinalCarry H rows 0 := by
  have h := canonicalCarryRun_realizes H rows 0
  have hInv := h.invariant_zero
  rw [h.ternaryDigitsValue_eq_ternaryCorrection] at hInv
  exact hInv

end CSTCarry
end Collatz3
