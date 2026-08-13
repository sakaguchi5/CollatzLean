import CollatzLean.Collatz2.Global.PrimitiveReturnGap
import CollatzLean.Collatz2.Canonical.SwapCarry
import Mathlib.Data.ZMod.Basic

/-!
# Collatz2 Arithmetic: primitive kappa と 2-adic swap separation

源となる scalar は displacement-form separation である。
primitive `kappa = 1` は adjacent word-swap residue displacement を `4 mod 8` に強制し、
その2進 valuation が exact に `2` であることを表す。
-/

namespace Collatz2

private theorem four_mul_three_pow_eq_four_mod_eight (p : ℕ) :
    (4 : ZMod 8) * (3 : ZMod 8) ^ p = 4 := by
  induction p with
  | zero => norm_num
  | succ p ih =>
      rw [pow_succ, ← mul_assoc, ih]
      change (12 : ZMod 8) = 4
      decide

private theorem three_pow_sq_eq_one_mod_eight (p : ℕ) :
    ((3 : ZMod 8) ^ p) * ((3 : ZMod 8) ^ p) = 1 := by
  induction p with
  | zero => norm_num
  | succ p ih =>
      rw [pow_succ]
      calc
        ((3 : ZMod 8) ^ p * 3) * ((3 : ZMod 8) ^ p * 3)
            = (((3 : ZMod 8) ^ p) * ((3 : ZMod 8) ^ p)) * 9 := by ring
        _ = 1 := by rw [ih]; decide

private theorem four_mul_odd_eq_four_mod_eight
    {a : ℕ}
    (ha : Odd a) :
    (4 : ZMod 8) * (a : ZMod 8) = 4 := by
  rcases ha with ⟨k, hk⟩
  rw [hk]
  push_cast
  ring_nf
  have h8 : (8 : ZMod 8) = 0 := by decide
  rw [h8]
  ring

namespace AdjacentTransferChain

/-- Adjacent two-word common residue modulus is divisible by eight. -/
theorem eight_dvd_adjacentSwap_modulus
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) :
    8 ∣ Word.residueModulus (C.word n ++ C.word (n + 1)) := by
  have hHn : 0 < Word.twoSteps (C.word n) :=
    Word.twoSteps_pos_of_valid_nonempty (C.word_valid n) (C.word_nonempty n)
  have hHns : 0 < Word.twoSteps (C.word (n + 1)) :=
    Word.twoSteps_pos_of_valid_nonempty
      (C.word_valid (n + 1)) (C.word_nonempty (n + 1))
  let H := Word.twoSteps (C.word n ++ C.word (n + 1))
  have hH : 2 ≤ H := by
    dsimp [H]
    rw [Word.twoSteps_append]
    omega
  obtain ⟨k, hk⟩ : ∃ k : ℕ, H + 1 = k + 3 := by
    exact ⟨H - 2, by omega⟩
  refine ⟨2 ^ k, ?_⟩
  unfold Word.residueModulus
  change 2 ^ (H + 1) = 8 * 2 ^ k
  rw [hk, pow_add]
  ring

end AdjacentTransferChain

namespace Word

/-- Inverse-free residue identity: `3^P * swapDisplacement = -separation`. -/
theorem leadingCoeff_mul_swapResidueDisplacement_eq_neg_separation
    (u v : Word) :
    let m := residueModulus (u ++ v)
    (((3 ^ oddSteps (u ++ v) : ℕ) : ZMod m) *
        ((swapResidueDisplacement u v : ℕ) : ZMod m)) =
      -(((AffineTransfer.ofWord u).separation
        (AffineTransfer.ofWord v) : ℤ) : ZMod m) := by
  let m := residueModulus (u ++ v)
  have h := swapResidueDisplacement_cast_eq_separation u v
  have hleading :
      (((3 ^ oddSteps (u ++ v) : ℕ) : ZMod m)) =
        (↑(leadingUnit (u ++ v)) : ZMod m) := by
    dsimp [m]
    simp [leadingUnit]
  change
    (((3 ^ oddSteps (u ++ v) : ℕ) : ZMod m) *
      ((swapResidueDisplacement u v : ℕ) : ZMod m)) =
    -(((AffineTransfer.ofWord u).separation
        (AffineTransfer.ofWord v) : ℤ) : ZMod m)
  rw [hleading, h]
  simp [← mul_assoc]

/-- Historical wording retained as a theorem alias. -/
theorem leadingCoeff_mul_swapResidueDisplacement_eq_neg_omega
    (u v : Word) :
    let m := residueModulus (u ++ v)
    (((3 ^ oddSteps (u ++ v) : ℕ) : ZMod m) *
        ((swapResidueDisplacement u v : ℕ) : ZMod m)) =
      -(((AffineTransfer.ofWord u).separation
        (AffineTransfer.ofWord v) : ℤ) : ZMod m) :=
  leadingCoeff_mul_swapResidueDisplacement_eq_neg_separation u v

end Word

namespace AdjacentTransferChain

/-- Adjacent form of the inverse-free separation residue identity. -/
theorem leadingCoeff_mul_adjacentSwapDisplacement_eq_neg_separationAdjacent
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) :
    let m := Word.residueModulus (C.word n ++ C.word (n + 1))
    (((3 ^ Word.oddSteps (C.word n ++ C.word (n + 1)) : ℕ) : ZMod m) *
        ((Word.swapResidueDisplacement (C.word n) (C.word (n + 1)) : ℕ) : ZMod m)) =
      -((C.separationAdjacent n : ℤ) : ZMod m) := by
  simpa [AdjacentTransferChain.transfer,
    AdjacentTransferChain.separationAdjacent] using
    Word.leadingCoeff_mul_swapResidueDisplacement_eq_neg_separation
      (C.word n) (C.word (n + 1))

/-- Historical adjacent omega name. -/
theorem leadingCoeff_mul_adjacentSwapDisplacement_eq_neg_omegaAdjacent
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) :
    let m := Word.residueModulus (C.word n ++ C.word (n + 1))
    (((3 ^ Word.oddSteps (C.word n ++ C.word (n + 1)) : ℕ) : ZMod m) *
        ((Word.swapResidueDisplacement (C.word n) (C.word (n + 1)) : ℕ) : ZMod m)) =
      -((C.omegaAdjacent n : ℤ) : ZMod m) :=
  C.leadingCoeff_mul_adjacentSwapDisplacement_eq_neg_separationAdjacent n

/-- `kappa=1` gives separation `4 * odd * odd`. -/
theorem separationAdjacent_eq_four_mul_contents_of_primitiveKappa_eq_one
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n)
    (hNs : C.NegativeAt (n + 1))
    (hstart : 1 < C.startValue n)
    (hk : C.primitiveKappa n = 1) :
    C.separationAdjacent n =
      4 * (C.centerContent n : ℤ) *
        (C.centerContent (n + 1) : ℤ) := by
  have h := C.separationAdjacent_eq_four_mul_contents_mul_primitiveKappa hN hNs hstart
  rw [hk] at h
  simpa using h

/-- Historical omega factorization at kappa one. -/
theorem omegaAdjacent_eq_four_mul_contents_of_primitiveKappa_eq_one
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n)
    (hNs : C.NegativeAt (n + 1))
    (hstart : 1 < C.startValue n)
    (hk : C.primitiveKappa n = 1) :
    C.omegaAdjacent n =
      4 * (C.centerContent n : ℤ) *
        (C.centerContent (n + 1) : ℤ) :=
  C.separationAdjacent_eq_four_mul_contents_of_primitiveKappa_eq_one hN hNs hstart hk

/-- Reduce adjacent separation identity to `ZMod 8`. -/
theorem leadingCoeff_mul_adjacentSwapDisplacement_mod_eight_eq_neg_separationAdjacent
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) :
    ((3 : ZMod 8) ^
        Word.oddSteps (C.word n ++ C.word (n + 1))) *
        (Word.swapResidueDisplacement
          (C.word n) (C.word (n + 1)) : ZMod 8) =
      -((C.separationAdjacent n : ℤ) : ZMod 8) := by
  let m := Word.residueModulus (C.word n ++ C.word (n + 1))
  have hm8 : 8 ∣ m := by
    simpa [m] using C.eight_dvd_adjacentSwap_modulus n
  have hres := C.leadingCoeff_mul_adjacentSwapDisplacement_eq_neg_separationAdjacent n
  have hres8 := congrArg (ZMod.castHom hm8 (ZMod 8)) hres
  have hres8Nat :
      (((3 ^ Word.oddSteps (C.word n ++ C.word (n + 1)) : ℕ) : ZMod 8) *
        (Word.swapResidueDisplacement
          (C.word n) (C.word (n + 1)) : ZMod 8)) =
      -((C.separationAdjacent n : ℤ) : ZMod 8) := by
    simpa only [ZMod.castHom_apply, ZMod.cast_mul hm8,
      ZMod.cast_natCast hm8, ZMod.cast_neg hm8,
      ZMod.cast_intCast hm8] using hres8
  simpa only [Nat.cast_pow, Nat.cast_three] using hres8Nat

/-- Historical omega mod-eight theorem. -/
theorem leadingCoeff_mul_adjacentSwapDisplacement_mod_eight_eq_neg_omegaAdjacent
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) :
    ((3 : ZMod 8) ^
        Word.oddSteps (C.word n ++ C.word (n + 1))) *
        (Word.swapResidueDisplacement
          (C.word n) (C.word (n + 1)) : ZMod 8) =
      -((C.omegaAdjacent n : ℤ) : ZMod 8) :=
  C.leadingCoeff_mul_adjacentSwapDisplacement_mod_eight_eq_neg_separationAdjacent n

end AdjacentTransferChain

/-- Odd factors do not change `4 mod 8`. -/
theorem neg_four_mul_odd_mul_odd_eq_four_mod_eight
    {a b : ℕ}
    (ha : Odd a)
    (hb : Odd b) :
    -(((4 : ℤ) * (a : ℤ) * (b : ℤ) : ℤ) : ZMod 8) = 4 := by
  calc
    -(((4 : ℤ) * (a : ℤ) * (b : ℤ) : ℤ) : ZMod 8)
        = -((4 : ZMod 8) * (a : ZMod 8) * (b : ZMod 8)) := by norm_num
    _ = -((4 : ZMod 8) * (b : ZMod 8)) := by
      rw [four_mul_odd_eq_four_mod_eight ha]
    _ = -(4 : ZMod 8) := by
      rw [four_mul_odd_eq_four_mod_eight hb]
    _ = 4 := by decide

namespace AdjacentTransferChain

/-- Primitive `kappa=1`: negative separation is `4 mod 8`. -/
theorem neg_separationAdjacent_mod_eight_eq_four_of_primitiveKappa_eq_one
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n)
    (hNs : C.NegativeAt (n + 1))
    (hstart : 1 < C.startValue n)
    (hk : C.primitiveKappa n = 1) :
    -((C.separationAdjacent n : ℤ) : ZMod 8) = 4 := by
  have hsep := C.separationAdjacent_eq_four_mul_contents_of_primitiveKappa_eq_one hN hNs hstart hk
  have hhodd : Odd (C.centerContent n) := C.centerContent_odd_of_negativeAt hN
  have hhsodd : Odd (C.centerContent (n + 1)) := C.centerContent_odd_of_negativeAt hNs
  rw [hsep]
  exact neg_four_mul_odd_mul_odd_eq_four_mod_eight hhodd hhsodd

/-- Historical omega theorem. -/
theorem neg_omegaAdjacent_mod_eight_eq_four_of_primitiveKappa_eq_one
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n)
    (hNs : C.NegativeAt (n + 1))
    (hstart : 1 < C.startValue n)
    (hk : C.primitiveKappa n = 1) :
    -((C.omegaAdjacent n : ℤ) : ZMod 8) = 4 :=
  C.neg_separationAdjacent_mod_eight_eq_four_of_primitiveKappa_eq_one hN hNs hstart hk

end AdjacentTransferChain

/-- If `3^P*s=4 mod 8`, then `s=4 mod 8`. -/
theorem eq_four_of_three_pow_mul_eq_four_mod_eight
    (P s : ℕ)
    (h : ((3 : ZMod 8) ^ P) * (s : ZMod 8) = 4) :
    (s : ZMod 8) = 4 := by
  have hsq := three_pow_sq_eq_one_mod_eight P
  calc
    (s : ZMod 8) = 1 * (s : ZMod 8) := by simp
    _ = (((3 : ZMod 8) ^ P) * ((3 : ZMod 8) ^ P)) * (s : ZMod 8) := by rw [hsq]
    _ = ((3 : ZMod 8) ^ P) * (((3 : ZMod 8) ^ P) * (s : ZMod 8)) := by ring
    _ = ((3 : ZMod 8) ^ P) * 4 := by rw [h]
    _ = 4 := by
      simpa [mul_comm] using four_mul_three_pow_eq_four_mod_eight P

/-- Cast equality `s=4` in `ZMod 8` gives the natural remainder equality. -/
theorem nat_mod_eight_eq_four_of_cast_eq_four
    (s : ℕ)
    (h : (s : ZMod 8) = 4) :
    s % 8 = 4 := by
  have hmod := (ZMod.natCast_eq_natCast_iff' s 4 8).mp h
  norm_num at hmod ⊢
  exact hmod

namespace AdjacentTransferChain

/-- Primitive `kappa=1`: adjacent swap displacement is `4 mod 8`. -/
theorem adjacentSwapResidueDisplacement_mod_eight_eq_four_of_primitiveKappa_eq_one
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n)
    (hNs : C.NegativeAt (n + 1))
    (hstart : 1 < C.startValue n)
    (hk : C.primitiveKappa n = 1) :
    Word.swapResidueDisplacement
        (C.word n) (C.word (n + 1)) % 8 = 4 := by
  let P := Word.oddSteps (C.word n ++ C.word (n + 1))
  let s := Word.swapResidueDisplacement (C.word n) (C.word (n + 1))
  have hres :
      ((3 : ZMod 8) ^ P) * (s : ZMod 8) =
        -((C.separationAdjacent n : ℤ) : ZMod 8) := by
    simpa [P, s] using
      C.leadingCoeff_mul_adjacentSwapDisplacement_mod_eight_eq_neg_separationAdjacent n
  have hsep : -((C.separationAdjacent n : ℤ) : ZMod 8) = 4 :=
    C.neg_separationAdjacent_mod_eight_eq_four_of_primitiveKappa_eq_one hN hNs hstart hk
  have hweighted : ((3 : ZMod 8) ^ P) * (s : ZMod 8) = 4 := hres.trans hsep
  have hs : (s : ZMod 8) = 4 :=
    eq_four_of_three_pow_mul_eq_four_mod_eight P s hweighted
  have hsmod : s % 8 = 4 := nat_mod_eight_eq_four_of_cast_eq_four s hs
  simpa [s] using hsmod

/-- `kappa=1`: swap displacement has exact 2-adic valuation two. -/
theorem adjacentSwapResidueDisplacement_v2_exact_two_of_primitiveKappa_eq_one
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n)
    (hNs : C.NegativeAt (n + 1))
    (hstart : 1 < C.startValue n)
    (hk : C.primitiveKappa n = 1) :
    4 ∣ Word.swapResidueDisplacement (C.word n) (C.word (n + 1)) ∧
      ¬ 8 ∣ Word.swapResidueDisplacement (C.word n) (C.word (n + 1)) := by
  let s := Word.swapResidueDisplacement (C.word n) (C.word (n + 1))
  have hmod : s % 8 = 4 := by
    simpa [s] using
      C.adjacentSwapResidueDisplacement_mod_eight_eq_four_of_primitiveKappa_eq_one
        hN hNs hstart hk
  constructor
  · have hdecomp := Nat.mod_add_div s 8
    rw [hmod] at hdecomp
    refine ⟨1 + 2 * (s / 8), ?_⟩
    omega
  · intro h8
    have hz : s % 8 = 0 := Nat.mod_eq_zero_of_dvd h8
    omega

end AdjacentTransferChain
end Collatz2
