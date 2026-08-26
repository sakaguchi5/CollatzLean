import CollatzLean.Collatz2.Canonical.SwapResidue

/-!
# Collatz2 Canonical: swap residue から得る thin carry

word-swap residue displacement の最小非負代表を取り、common modulus を跨ぐ回数を
`swapCarry` として読む。両 canonical start と displacement は modulus 未満なので、
carry は必ず `0` または `1`。
-/

namespace Collatz2
namespace Word

/-- Minimal nonnegative representative of canonical-start swap displacement. -/
def swapResidueDisplacement (u v : Word) : ℕ :=
  ZMod.val
    (((canonicalStart (u ++ v) : ℕ) :
        ZMod (residueModulus (u ++ v))) -
      ((canonicalStart (v ++ u) : ℕ) :
        ZMod (residueModulus (u ++ v))))

/-- Swap residue displacement is below the common modulus. -/
theorem swapResidueDisplacement_lt_modulus
    (u v : Word) :
    swapResidueDisplacement u v < residueModulus (u ++ v) := by
  have : NeZero (residueModulus (u ++ v)) :=
    ⟨Nat.ne_of_gt (residueModulus_pos (u ++ v))⟩
  unfold swapResidueDisplacement
  exact ZMod.val_lt _

/-- Cast displacement back to ZMod to recover canonical-start difference. -/
theorem swapResidueDisplacement_cast_eq_start_sub
    (u v : Word) :
    ((swapResidueDisplacement u v : ℕ) :
        ZMod (residueModulus (u ++ v))) =
      (((canonicalStart (u ++ v) : ℕ) :
          ZMod (residueModulus (u ++ v))) -
        ((canonicalStart (v ++ u) : ℕ) :
          ZMod (residueModulus (u ++ v)))) := by
  have : NeZero (residueModulus (u ++ v)) :=
    ⟨Nat.ne_of_gt (residueModulus_pos (u ++ v))⟩
  unfold swapResidueDisplacement
  exact ZMod.natCast_zmod_val _

/-- Same displacement is the modular shadow of transfer separation. -/
theorem swapResidueDisplacement_cast_eq_separation
    (u v : Word) :
    ((swapResidueDisplacement u v : ℕ) :
        ZMod (residueModulus (u ++ v))) =
      -((↑((leadingUnit (u ++ v))⁻¹) :
          ZMod (residueModulus (u ++ v))) *
        (((AffineTransfer.ofWord u).separation
          (AffineTransfer.ofWord v) : ℤ) :
            ZMod (residueModulus (u ++ v)))) := by
  rw [swapResidueDisplacement_cast_eq_start_sub]
  exact oddStartClass_swap_displacement u v

/-- Historical wording retained as a theorem alias. -/
theorem swapResidueDisplacement_cast_eq_omega
    (u v : Word) :
    ((swapResidueDisplacement u v : ℕ) :
        ZMod (residueModulus (u ++ v))) =
      -((↑((leadingUnit (u ++ v))⁻¹) :
          ZMod (residueModulus (u ++ v))) *
        (((AffineTransfer.ofWord u).separation
          (AffineTransfer.ofWord v) : ℤ) :
            ZMod (residueModulus (u ++ v)))) :=
  swapResidueDisplacement_cast_eq_separation u v

/-- Adding displacement and reducing gives the swapped canonical start. -/
theorem canonicalStart_swap_add_displacement_mod
    (u v : Word) :
    (canonicalStart (v ++ u) + swapResidueDisplacement u v) %
        residueModulus (u ++ v) =
      canonicalStart (u ++ v) := by
  let m := residueModulus (u ++ v)
  have : NeZero m :=
    ⟨Nat.ne_of_gt (by simp only [residueModulus_pos, m])⟩
  have hshift := swapResidueDisplacement_cast_eq_start_sub u v
  have hcast :
      (((canonicalStart (v ++ u) +
          swapResidueDisplacement u v : ℕ) : ZMod m)) =
        ((canonicalStart (u ++ v) : ℕ) : ZMod m) := by
    rw [Nat.cast_add]
    rw [hshift]
    ring
  have hval := congrArg ZMod.val hcast
  have hxlt : canonicalStart (u ++ v) < m := by
    simpa [m] using canonicalStart_lt_modulus (u ++ v)
  change
    (canonicalStart (v ++ u) + swapResidueDisplacement u v) % m =
      canonicalStart (u ++ v)
  calc
    (canonicalStart (v ++ u) + swapResidueDisplacement u v) % m
        =
        ((((canonicalStart (v ++ u) +
            swapResidueDisplacement u v : ℕ) : ZMod m)).val) := by
          symm
          exact ZMod.val_natCast m
            (canonicalStart (v ++ u) + swapResidueDisplacement u v)
    _ = (((canonicalStart (u ++ v) : ℕ) : ZMod m).val) := hval
    _ = canonicalStart (u ++ v) := by
        exact ZMod.val_natCast_of_lt hxlt

/-- Representative carry: zero if the modulus is not crossed, one otherwise. -/
def swapCarry (u v : Word) : ℕ :=
  if canonicalStart (v ++ u) + swapResidueDisplacement u v <
      residueModulus (u ++ v) then 0 else 1

/-- Carry is always zero or one. -/
theorem swapCarry_eq_zero_or_one
    (u v : Word) :
    swapCarry u v = 0 ∨ swapCarry u v = 1 := by
  unfold swapCarry
  split_ifs <;> simp

/-- Carry zero iff no modulus crossing. -/
theorem swapCarry_eq_zero_iff
    (u v : Word) :
    swapCarry u v = 0 ↔
      canonicalStart (v ++ u) + swapResidueDisplacement u v <
        residueModulus (u ++ v) := by
  unfold swapCarry
  split_ifs with h
  · simp [h]
  · simp [h]

/-- Carry one iff the common modulus is crossed once. -/
theorem swapCarry_eq_one_iff
    (u v : Word) :
    swapCarry u v = 1 ↔
      residueModulus (u ++ v) ≤
        canonicalStart (v ++ u) + swapResidueDisplacement u v := by
  unfold swapCarry
  split_ifs with h
  · simp [Nat.not_le_of_gt h]
  · have hle := Nat.le_of_not_gt h
    simp [hle]

/-- Exact representative carry equation. -/
theorem swapCarry_spec
    (u v : Word) :
    canonicalStart (v ++ u) + swapResidueDisplacement u v =
      canonicalStart (u ++ v) +
        swapCarry u v * residueModulus (u ++ v) := by
  let m := residueModulus (u ++ v)
  let x := canonicalStart (u ++ v)
  let y := canonicalStart (v ++ u)
  let s := swapResidueDisplacement u v
  have hmpos : 0 < m := by simp only [residueModulus_pos, m]
  have hxlt : x < m := by
    simpa [x, m] using canonicalStart_lt_modulus (u ++ v)
  have hylt : y < m := by
    have hy := canonicalStart_lt_modulus (v ++ u)
    have hmod := residueModulus_swap u v
    rw [hmod] at hy
    simpa [y, m] using hy
  have hslt : s < m := by
    simpa [s, m] using swapResidueDisplacement_lt_modulus u v
  have hmodEq : (y + s) % m = x := by
    simpa [x, y, s, m] using canonicalStart_swap_add_displacement_mod u v
  unfold swapCarry
  change y + s = x + (if y + s < m then 0 else 1) * m
  split_ifs with hlt
  · have hrem : (y + s) % m = y + s := Nat.mod_eq_of_lt hlt
    rw [hrem] at hmodEq
    simp only [zero_mul, add_zero]
    exact hmodEq
  · have hge : m ≤ y + s := Nat.le_of_not_gt hlt
    have hsumlt : y + s < 2 * m := by omega
    have hsubLt : y + s - m < m := by omega
    have hrem : (y + s) % m = y + s - m := by
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hsubLt]
    rw [hrem] at hmodEq
    simp
    omega

/-- Carry is at most one. -/
theorem swapCarry_le_one
    (u v : Word) :
    swapCarry u v ≤ 1 := by
  rcases swapCarry_eq_zero_or_one u v with h | h <;> simp [h]

/-- Carry zero requires no modulus correction. -/
theorem canonicalStart_swap_eq_of_carry_zero
    (u v : Word)
    (hcarry : swapCarry u v = 0) :
    canonicalStart (v ++ u) + swapResidueDisplacement u v =
      canonicalStart (u ++ v) := by
  have h := swapCarry_spec u v
  rw [hcarry] at h
  simpa using h

/-- Carry one requires exactly one common modulus correction. -/
theorem canonicalStart_swap_add_modulus_eq_of_carry_one
    (u v : Word)
    (hcarry : swapCarry u v = 1) :
    canonicalStart (v ++ u) + swapResidueDisplacement u v =
      canonicalStart (u ++ v) + residueModulus (u ++ v) := by
  have h := swapCarry_spec u v
  rw [hcarry] at h
  simpa using h

end Word
end Collatz2
