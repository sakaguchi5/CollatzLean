import CollatzLean.Collatz2.Synthesis.PrimitiveReturnGap
import CollatzLean.Collatz2.Synthesis.SwapCarry
import Mathlib.Data.ZMod.Basic

/-!
# Collatz2 Synthesis: kappa and 2-adic swap displacement

`omega = 4*h*h'*kappa` と word-swap residue/carry を接続する。
ここでは重い valuation object を導入せず、まず exact divisibility で読む。

特に primitive event `kappa = 1` では adjacent word swap の residue displacement は

  `4 ∣ displacement` かつ `8 ∤ displacement`

となり、2進 valuation が exact に `2` であることを表す。
-/

namespace Collatz2
namespace Synthesis

/-- ZMod 8 では `4 * 3^p = 4`。 -/
private theorem four_mul_three_pow_eq_four_mod_eight (p : ℕ) :
    (4 : ZMod 8) * (3 : ZMod 8) ^ p = 4 := by
  induction p with
  | zero =>
      norm_num
  | succ p ih =>
      rw [pow_succ, ← mul_assoc, ih]
      change (12 : ZMod 8) = 4
      decide

/-- ZMod 8 では `(3^p)^2 = 1`。 -/
private theorem three_pow_sq_eq_one_mod_eight (p : ℕ) :
    ((3 : ZMod 8) ^ p) * ((3 : ZMod 8) ^ p) = 1 := by
  induction p with
  | zero =>
      norm_num
  | succ p ih =>
      rw [pow_succ]
      calc
        ((3 : ZMod 8) ^ p * 3) * ((3 : ZMod 8) ^ p * 3)
            = (((3 : ZMod 8) ^ p) * ((3 : ZMod 8) ^ p)) * 9 := by
              ring
        _ = 1 := by
          rw [ih]
          decide

/-- odd natural number は ZMod 8 で `4` を変えない。 -/
private theorem four_mul_odd_eq_four_mod_eight
    {a : ℕ}
    (ha : Odd a) :
    (4 : ZMod 8) * (a : ZMod 8) = 4 := by
  rcases ha with ⟨k, hk⟩
  rw [hk]
  push_cast
  ring_nf
  have h8 : (8 : ZMod 8) = 0 := by
    decide
  rw [h8]
  ring


/-- adjacent two-word common residue modulus は `8` の倍数。 -/
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

/--
swap displacement は inverse を消去すると
`3^P * displacement = -omega` という exact residue identity を満たす。
-/
theorem leadingCoeff_mul_swapResidueDisplacement_eq_neg_omega
    (u v : Word) :
    let m := Word.residueModulus (u ++ v)
    (((3 ^ Word.oddSteps (u ++ v) : ℕ) : ZMod m) *
        ((swapResidueDisplacement u v : ℕ) : ZMod m)) =
      -((MatrixAnalysis.omega
        (AffineTransfer.ofWord u)
        (AffineTransfer.ofWord v) : ℤ) : ZMod m) := by
  let m := Word.residueModulus (u ++ v)
  have h := swapResidueDisplacement_cast_eq_omega u v
  have hleading :
      (((3 ^ Word.oddSteps (u ++ v) : ℕ) : ZMod m)) =
        (↑(Word.leadingUnit (u ++ v)) : ZMod m) := by
    dsimp [m]
    simp [Word.leadingUnit]
  change
    (((3 ^ Word.oddSteps (u ++ v) : ℕ) : ZMod m) *
      ((swapResidueDisplacement u v : ℕ) : ZMod m)) =
    -((MatrixAnalysis.omega
        (AffineTransfer.ofWord u)
        (AffineTransfer.ofWord v) : ℤ) : ZMod m)
  rw [hleading, h]
  simp [← mul_assoc]

/-- adjacent version。 -/
theorem leadingCoeff_mul_adjacentSwapDisplacement_eq_neg_omegaAdjacent
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) :
    let m := Word.residueModulus (C.word n ++ C.word (n + 1))
    (((3 ^ Word.oddSteps (C.word n ++ C.word (n + 1)) : ℕ) : ZMod m) *
        ((swapResidueDisplacement (C.word n) (C.word (n + 1)) : ℕ) : ZMod m)) =
      -((AdjacentTransferChain.omegaAdjacent C n : ℤ) : ZMod m) := by
  simpa [AdjacentTransferChain.transfer, AdjacentTransferChain.omegaAdjacent] using
    leadingCoeff_mul_swapResidueDisplacement_eq_neg_omega
      (C.word n) (C.word (n + 1))

/-- `kappa=1` event では omega は `4 * odd * odd`。 -/
theorem omegaAdjacent_eq_four_mul_contents_of_primitiveKappa_eq_one
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n)
    (hNs : C.NegativeAt (n + 1))
    (hstart : 1 < C.startValue n)
    (hk : AdjacentTransferChain.primitiveKappa C n = 1) :
    AdjacentTransferChain.omegaAdjacent C n =
      4 * (AdjacentTransferChain.centerContent C n : ℤ) *
        (AdjacentTransferChain.centerContent C (n + 1) : ℤ) := by
  have h :=
    AdjacentTransferChain.omegaAdjacent_eq_four_mul_contents_mul_primitiveKappa C hN hNs hstart
  rw [hk] at h
  simpa using h
open AdjacentTransferChain

/--
adjacent swap の common-modulus residue identity を `ZMod 8` へ落とす。
-/
theorem leadingCoeff_mul_adjacentSwapDisplacement_mod_eight_eq_neg_omegaAdjacent
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) :
    ((3 : ZMod 8) ^
        Word.oddSteps (C.word n ++ C.word (n + 1))) *
        (swapResidueDisplacement
          (C.word n) (C.word (n + 1)) : ZMod 8) =
      -((omegaAdjacent C n : ℤ) : ZMod 8) := by
  let m :=
    Word.residueModulus (C.word n ++ C.word (n + 1))
  have hm8 : 8 ∣ m := by
    simpa [m] using eight_dvd_adjacentSwap_modulus C n
  have hres :=
    leadingCoeff_mul_adjacentSwapDisplacement_eq_neg_omegaAdjacent C n
  have hres8 :=
    congrArg (ZMod.castHom hm8 (ZMod 8)) hres
  have hres8Nat :
      (((3 ^ Word.oddSteps (C.word n ++ C.word (n + 1)) : ℕ) :
          ZMod 8) *
        (swapResidueDisplacement
          (C.word n) (C.word (n + 1)) : ZMod 8)) =
      -((omegaAdjacent C n : ℤ) : ZMod 8) := by
    simpa only [
      ZMod.castHom_apply,
      ZMod.cast_mul hm8,
      ZMod.cast_natCast hm8,
      ZMod.cast_neg hm8,
      ZMod.cast_intCast hm8
    ] using hres8
  simpa only [Nat.cast_pow, Nat.cast_three] using hres8Nat

/--
odd な二数 `a,b` に対して `-(4ab) = 4 mod 8`。
-/
theorem neg_four_mul_odd_mul_odd_eq_four_mod_eight
    {a b : ℕ}
    (ha : Odd a)
    (hb : Odd b) :
    -(((4 : ℤ) * (a : ℤ) * (b : ℤ) : ℤ) : ZMod 8) = 4 := by
  calc
    -(((4 : ℤ) * (a : ℤ) * (b : ℤ) : ℤ) : ZMod 8)
        =
        -((4 : ZMod 8) * (a : ZMod 8) * (b : ZMod 8)) := by
          norm_num
    _ = -((4 : ZMod 8) * (b : ZMod 8)) := by
      rw [four_mul_odd_eq_four_mod_eight ha]
    _ = -(4 : ZMod 8) := by
      rw [four_mul_odd_eq_four_mod_eight hb]
    _ = 4 := by
      decide

/--
primitive `kappa=1` なら adjacent omega の負値は `4 mod 8`。
-/
theorem neg_omegaAdjacent_mod_eight_eq_four_of_primitiveKappa_eq_one
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n)
    (hNs : C.NegativeAt (n + 1))
    (hstart : 1 < C.startValue n)
    (hk : primitiveKappa C n = 1) :
    -((omegaAdjacent C n : ℤ) : ZMod 8) = 4 := by
  have homega :=
    omegaAdjacent_eq_four_mul_contents_of_primitiveKappa_eq_one
      C hN hNs hstart hk
  have hhodd :
      Odd (centerContent C n) :=
    centerContent_odd_of_negativeAt C hN
  have hhsodd :
      Odd (centerContent C (n + 1)) :=
    centerContent_odd_of_negativeAt C hNs
  rw [homega]
  exact
    neg_four_mul_odd_mul_odd_eq_four_mod_eight
      hhodd hhsodd

/--
`3^P * s = 4 mod 8` なら `s = 4 mod 8`。
`3^P` は mod 8 で自己逆元。
-/
theorem eq_four_of_three_pow_mul_eq_four_mod_eight
    (P s : ℕ)
    (h :
      ((3 : ZMod 8) ^ P) * (s : ZMod 8) = 4) :
    (s : ZMod 8) = 4 := by
  have hsq :=
    three_pow_sq_eq_one_mod_eight P
  calc
    (s : ZMod 8)
        = 1 * (s : ZMod 8) := by simp
    _ =
        (((3 : ZMod 8) ^ P) *
          ((3 : ZMod 8) ^ P)) *
          (s : ZMod 8) := by
      rw [hsq]
    _ =
        ((3 : ZMod 8) ^ P) *
          (((3 : ZMod 8) ^ P) * (s : ZMod 8)) := by
      ring
    _ = ((3 : ZMod 8) ^ P) * 4 := by
      rw [h]
    _ = 4 := by
      simpa [mul_comm] using
        four_mul_three_pow_eq_four_mod_eight P

/--
`ZMod 8` で nat cast が `4` なら、元の Nat は `4 mod 8`。
-/
theorem nat_mod_eight_eq_four_of_cast_eq_four
    (s : ℕ)
    (h : (s : ZMod 8) = 4) :
    s % 8 = 4 := by
  have hmod :=
    (ZMod.natCast_eq_natCast_iff' s 4 8).mp h
  norm_num at hmod ⊢
  exact hmod

/--
primitive `kappa=1` event では adjacent swap displacement は `4 mod 8`。
-/
theorem adjacentSwapResidueDisplacement_mod_eight_eq_four_of_primitiveKappa_eq_one
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n)
    (hNs : C.NegativeAt (n + 1))
    (hstart : 1 < C.startValue n)
    (hk : primitiveKappa C n = 1) :
    swapResidueDisplacement
        (C.word n) (C.word (n + 1)) % 8 = 4 := by
  let P :=
    Word.oddSteps (C.word n ++ C.word (n + 1))
  let s :=
    swapResidueDisplacement
      (C.word n) (C.word (n + 1))
  have hres :
      ((3 : ZMod 8) ^ P) * (s : ZMod 8) =
        -((omegaAdjacent C n : ℤ) : ZMod 8) := by
    simpa [P, s] using
      leadingCoeff_mul_adjacentSwapDisplacement_mod_eight_eq_neg_omegaAdjacent
        C n
  have homega :
      -((omegaAdjacent C n : ℤ) : ZMod 8) = 4 :=
    neg_omegaAdjacent_mod_eight_eq_four_of_primitiveKappa_eq_one
      C hN hNs hstart hk
  have hweighted :
      ((3 : ZMod 8) ^ P) * (s : ZMod 8) = 4 :=
    hres.trans homega
  have hs :
      (s : ZMod 8) = 4 :=
    eq_four_of_three_pow_mul_eq_four_mod_eight
      P s hweighted
  have hsmod :
      s % 8 = 4 :=
    nat_mod_eight_eq_four_of_cast_eq_four s hs
  simpa [s] using hsmod

/-- `kappa=1` では swap displacement の2進 valuation は exact に2。 -/
theorem adjacentSwapResidueDisplacement_v2_exact_two_of_primitiveKappa_eq_one
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n)
    (hNs : C.NegativeAt (n + 1))
    (hstart : 1 < C.startValue n)
    (hk : primitiveKappa C n = 1) :
    4 ∣ swapResidueDisplacement (C.word n) (C.word (n + 1)) ∧
      ¬ 8 ∣ swapResidueDisplacement (C.word n) (C.word (n + 1)) := by
  let s := swapResidueDisplacement (C.word n) (C.word (n + 1))
  have hmod : s % 8 = 4 := by
    simpa [s] using
      adjacentSwapResidueDisplacement_mod_eight_eq_four_of_primitiveKappa_eq_one
        C hN hNs hstart hk
  constructor
  · have hdecomp := Nat.mod_add_div s 8
    rw [hmod] at hdecomp
    refine ⟨1 + 2 * (s / 8), ?_⟩
    omega
  · intro h8
    have hz : s % 8 = 0 := Nat.mod_eq_zero_of_dvd h8
    omega

end Synthesis
end Collatz2
