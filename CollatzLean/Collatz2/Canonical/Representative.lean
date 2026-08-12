import CollatzLean.Collatz2.Canonical.ResidueClass

/-!
# Collatz2: canonical representative derived from the residue class

canonical start は odd-start residue class の最小非負代表としてのみ定義する。
したがって canonicality は primitive な trajectory data ではなく、
同じ affine transfer を奇数 endpoint で実現する合同類からの corollary である。
-/

namespace Collatz2
namespace Word

/-- odd-start class の最小非負代表。 -/
def canonicalStart (w : Word) : ℕ :=
  (oddStartClass w).val

/-- canonical start は residue modulus より小さい。 -/
theorem canonicalStart_lt_modulus (w : Word) :
    canonicalStart w < residueModulus w := by
  haveI : NeZero (residueModulus w) := ⟨by simp [residueModulus]⟩
  exact ZMod.val_lt (oddStartClass w)

/-- canonical representative を modulus に戻すと元の odd-start class。 -/
theorem canonicalStart_cast (w : Word) :
    ((canonicalStart w : ℕ) : ZMod (residueModulus w)) = oddStartClass w := by
  haveI : NeZero (residueModulus w) := ⟨by simp [residueModulus]⟩
  exact ZMod.natCast_zmod_val (oddStartClass w)

/-- 奇数 endpoint realization の start の剰余は canonical representative。 -/
theorem Realizes.start_mod_eq_canonicalStart
    {w : Word} {x y : ℕ}
    (h : Realizes w x y)
    (hy : Odd y) :
    x % residueModulus w = canonicalStart w := by
  have hc := h.start_has_oddStartClass hy
  have hv := congrArg ZMod.val hc
  simpa [canonicalStart, ZMod.val_natCast] using hv

/-- canonical start は同じ odd-endpoint realization class の最小自然数 start。 -/
theorem Realizes.canonicalStart_le_start
    {w : Word} {x y : ℕ}
    (h : Realizes w x y)
    (hy : Odd y) :
    canonicalStart w ≤ x := by
  have hmod := h.start_mod_eq_canonicalStart hy
  have hdecomp := Nat.mod_add_div x (residueModulus w)
  rw [hmod] at hdecomp
  omega

/-- modulus 未満の odd-endpoint realization start は canonical start そのもの。 -/
theorem Realizes.eq_canonicalStart_of_lt_modulus
    {w : Word} {x y : ℕ}
    (h : Realizes w x y)
    (hy : Odd y)
    (hx : x < residueModulus w) :
    x = canonicalStart w := by
  have hmod := h.start_mod_eq_canonicalStart hy
  simpa [Nat.mod_eq_of_lt hx] using hmod

/-- canonical start を affine equation に代入した分子。 -/
def canonicalNumerator (w : Word) : ℕ :=
  3 ^ oddSteps w * canonicalStart w + affineConst w

/-- canonical numerator は modulus に対し `2^H` の剰余を持つ。 -/
theorem canonicalNumerator_mod_residueModulus (w : Word) :
    canonicalNumerator w % residueModulus w = 2 ^ twoSteps w := by
  haveI : NeZero (residueModulus w) := ⟨by simp [residueModulus]⟩
  have hcast :
      ((canonicalNumerator w : ℕ) : ZMod (residueModulus w)) =
        ((2 ^ twoSteps w : ℕ) : ZMod (residueModulus w)) := by
    calc
      ((canonicalNumerator w : ℕ) : ZMod (residueModulus w))
          =
          (((3 ^ oddSteps w : ℕ) : ZMod (residueModulus w)) *
              ((canonicalStart w : ℕ) : ZMod (residueModulus w))) +
            ((affineConst w : ℕ) : ZMod (residueModulus w)) := by
              simp [canonicalNumerator]
      _ =
          (((3 ^ oddSteps w : ℕ) : ZMod (residueModulus w)) *
              oddStartClass w) +
            ((affineConst w : ℕ) : ZMod (residueModulus w)) := by
              rw [canonicalStart_cast]
      _ = ((2 ^ twoSteps w : ℕ) : ZMod (residueModulus w)) :=
        oddStartClass_spec w
  have hval := congrArg ZMod.val hcast
  have hpowlt : 2 ^ twoSteps w < residueModulus w := by
    unfold residueModulus
    exact Nat.pow_lt_pow_right (by omega) (Nat.lt_succ_self _)
  calc
    canonicalNumerator w % residueModulus w
        =
        (((canonicalNumerator w : ℕ) : ZMod (residueModulus w))).val := by
            simp only [ZMod.val_natCast]
    _ =
        (((2 ^ twoSteps w : ℕ) : ZMod (residueModulus w))).val := hval
    _ = (2 ^ twoSteps w) % residueModulus w := by
      simp only [ZMod.val_natCast]
    _ = 2 ^ twoSteps w := Nat.mod_eq_of_lt hpowlt

/-- canonical start に対応する最小 odd-endpoint affine realization の endpoint。 -/
def canonicalEnd (w : Word) : ℕ :=
  2 * (canonicalNumerator w / residueModulus w) + 1

/-- canonical start/end は affine realization equation を満たす。 -/
theorem canonicalEnd_realizes (w : Word) :
    Realizes w (canonicalStart w) (canonicalEnd w) := by
  apply (realizes_iff w (canonicalStart w) (canonicalEnd w)).2
  change 2 ^ twoSteps w * canonicalEnd w = canonicalNumerator w
  have hdiv := Nat.mod_add_div (canonicalNumerator w) (residueModulus w)
  rw [canonicalNumerator_mod_residueModulus] at hdiv
  calc
    2 ^ twoSteps w * canonicalEnd w
        =
        2 ^ twoSteps w +
          residueModulus w * (canonicalNumerator w / residueModulus w) := by
            unfold canonicalEnd residueModulus
            rw [pow_succ]
            ring
    _ = canonicalNumerator w := by
      simpa [Nat.mul_comm] using hdiv

/-- canonical endpoint は odd。 -/
theorem canonicalEnd_odd (w : Word) : Odd (canonicalEnd w) := by
  refine ⟨canonicalNumerator w / residueModulus w, ?_⟩
  unfold canonicalEnd
  omega

/-- canonical endpoint は正。 -/
theorem canonicalEnd_pos (w : Word) : 0 < canonicalEnd w := by
  unfold canonicalEnd
  omega

end Word
end Collatz2
