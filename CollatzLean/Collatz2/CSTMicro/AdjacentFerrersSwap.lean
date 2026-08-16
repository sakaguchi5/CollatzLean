import CollatzLean.Collatz2.CSTMicro.InversePathSum

/-!
# General CST: adjacent Ferrers swap

同じ endpoint を持つ binary path の局所 cover

  lower : leftContext ++ 01 ++ rightContext
  upper : leftContext ++ 10 ++ rightContext

を一つの object として扱う。

odd step を一つ左へ動かすので、Ferrers diagram では一セル上側へ移る。
このとき

  B(lower) = B(upper) + 2^i 3^r

であり、2-adic representative は

  R(upper) ≡ R(lower) + 2^i 3^{-(a+1)}  (mod 2^k)

だけ変化する。
-/

namespace Collatz2
namespace CSTMicro

/-- odd count の append formula。 -/
theorem cstOddCount_append (u v : ParityWord) :
    oddCount (u ++ v) = oddCount u + oddCount v := by
  simp [oddCount, List.map_append]

/-- standard parity affine numerator の append formula。 -/
theorem cstAffineConst_append (u v : ParityWord) :
    affineConst (u ++ v) =
      3 ^ oddCount v * affineConst u +
        2 ^ u.length * affineConst v := by
  induction u with
  | nil =>
      simp [affineConst]
  | cons b u ih =>
      cases b
      · simp [affineConst, ih, pow_succ]
        ring
      · simp [affineConst, ih, cstOddCount_append, pow_add, pow_succ]
        ring

/-- 一つの Ferrers cover `01 -> 10`。 -/
structure AdjacentFerrersSwap where
  leftContext : ParityWord
  rightContext : ParityWord

namespace AdjacentFerrersSwap

/-- Ferrers cell を追加する前の word。 -/
def lowerWord (S : AdjacentFerrersSwap) : ParityWord :=
  S.leftContext ++ ([false, true] ++ S.rightContext)

/-- odd step を一つ左へ動かした word。 -/
def upperWord (S : AdjacentFerrersSwap) : ParityWord :=
  S.leftContext ++ ([true, false] ++ S.rightContext)

/-- swap の開始位置。 -/
def position (S : AdjacentFerrersSwap) : ℕ :=
  S.leftContext.length

/-- common length。 -/
def length (S : AdjacentFerrersSwap) : ℕ :=
  S.leftContext.length + 2 + S.rightContext.length

/-- common odd count。 -/
def oddTotal (S : AdjacentFerrersSwap) : ℕ :=
  oddCount S.leftContext + 1 + oddCount S.rightContext

/-- common parity modulus。 -/
def modulus (S : AdjacentFerrersSwap) : ℕ :=
  2 ^ S.length

/-- Archimedean affine change `2^i 3^r`。 -/
def deltaB (S : AdjacentFerrersSwap) : ℕ :=
  2 ^ S.position * 3 ^ oddCount S.rightContext

/-- 2-adic local change `2^i 3^{-(a+1)}`。 -/
def deltaClass (S : AdjacentFerrersSwap) : ZMod S.modulus := by
  change ZMod (2 ^ S.length)
  exact
    (2 : ZMod (2 ^ S.length)) ^ S.position *
      invThreePow S.length (oddCount S.leftContext + 1)

/-- local 2-adic change の ordinary representative。 -/
def deltaR (S : AdjacentFerrersSwap) : ℕ :=
  S.deltaClass.val

/-- lower word の least representative。 -/
def lowerR (S : AdjacentFerrersSwap) : ℕ :=
  leastRepresentative S.lowerWord

/-- upper word の least representative。 -/
def upperR (S : AdjacentFerrersSwap) : ℕ :=
  leastRepresentative S.upperWord

@[simp] theorem lowerWord_length (S : AdjacentFerrersSwap) :
    S.lowerWord.length = S.length := by
  simp [lowerWord, length]
  ac_rfl

@[simp] theorem upperWord_length (S : AdjacentFerrersSwap) :
    S.upperWord.length = S.length := by
  simp [upperWord, length]
  ac_rfl

@[simp] theorem lowerWord_oddCount (S : AdjacentFerrersSwap) :
    oddCount S.lowerWord = S.oddTotal := by
  simp [lowerWord, oddTotal, cstOddCount_append, Nat.add_assoc]
  ac_rfl

@[simp] theorem upperWord_oddCount (S : AdjacentFerrersSwap) :
    oddCount S.upperWord = S.oddTotal := by
  simp [upperWord, oddTotal, cstOddCount_append, Nat.add_assoc]
  ac_rfl

@[simp] theorem parityModulus_lowerWord (S : AdjacentFerrersSwap) :
    parityModulus S.lowerWord = S.modulus := by
  simp [parityModulus, modulus]

@[simp] theorem parityModulus_upperWord (S : AdjacentFerrersSwap) :
    parityModulus S.upperWord = S.modulus := by
  simp [parityModulus, modulus]

/-- `01 -> 10` の exact affine change。 -/
theorem lower_affineConst_eq_upper_add_deltaB
    (S : AdjacentFerrersSwap) :
    affineConst S.lowerWord =
      affineConst S.upperWord + S.deltaB := by
  unfold lowerWord upperWord deltaB position
  rw [cstAffineConst_append S.leftContext ([false, true] ++ S.rightContext)]
  rw [cstAffineConst_append S.leftContext ([true, false] ++ S.rightContext)]
  rw [cstAffineConst_append [false, true] S.rightContext]
  rw [cstAffineConst_append [true, false] S.rightContext]
  simp [affineConst, oddCount, bitNat, pow_succ]
  ring

/-- upper affine numerator は lower 以下。 -/
theorem upper_affineConst_le_lower (S : AdjacentFerrersSwap) :
    affineConst S.upperWord ≤ affineConst S.lowerWord := by
  rw [S.lower_affineConst_eq_upper_add_deltaB]
  omega

/-- local delta は common leading power で戻すと `deltaB` になる。 -/
theorem threePow_mul_deltaClass (S : AdjacentFerrersSwap) :
    (3 : ZMod S.modulus) ^ S.oddTotal * S.deltaClass =
      ((S.deltaB : ℕ) : ZMod S.modulus) := by
  change
    (3 : ZMod (2 ^ S.length)) ^
          (oddCount S.leftContext + 1 + oddCount S.rightContext) *
        ((2 : ZMod (2 ^ S.length)) ^ S.position *
          invThreePow S.length (oddCount S.leftContext + 1))
      =
    (((2 ^ S.position * 3 ^ oddCount S.rightContext : ℕ)) :
      ZMod (2 ^ S.length))
  rw [pow_add]
  have hInv :=
    threePow_mul_invThreePow S.length (oddCount S.leftContext + 1)
  push_cast
  calc
    ((3 : ZMod (2 ^ S.length)) ^ (oddCount S.leftContext + 1) *
          (3 : ZMod (2 ^ S.length)) ^ oddCount S.rightContext) *
        ((2 : ZMod (2 ^ S.length)) ^ S.position *
          invThreePow S.length (oddCount S.leftContext + 1))
        =
        (2 : ZMod (2 ^ S.length)) ^ S.position *
          ((3 : ZMod (2 ^ S.length)) ^ (oddCount S.leftContext + 1) *
            invThreePow S.length (oddCount S.leftContext + 1)) *
          (3 : ZMod (2 ^ S.length)) ^ oddCount S.rightContext := by ring
    _ =
        (2 : ZMod (2 ^ S.length)) ^ S.position *
          (3 : ZMod (2 ^ S.length)) ^ oddCount S.rightContext := by
            rw [hInv]
            ring

@[simp] theorem lowerR_lt_modulus (S : AdjacentFerrersSwap) :
    S.lowerR < S.modulus := by
  simpa [lowerR] using leastRepresentative_lt_modulus S.lowerWord

@[simp] theorem upperR_lt_modulus (S : AdjacentFerrersSwap) :
    S.upperR < S.modulus := by
  simpa [upperR] using leastRepresentative_lt_modulus S.upperWord

@[simp] theorem deltaR_lt_modulus (S : AdjacentFerrersSwap) :
    S.deltaR < S.modulus := by
  haveI : NeZero S.modulus := ⟨by simp [modulus]⟩
  exact ZMod.val_lt S.deltaClass

/-- `deltaR` を common modulus に戻すと `deltaClass`。 -/
theorem deltaR_cast (S : AdjacentFerrersSwap) :
    ((S.deltaR : ℕ) : ZMod S.modulus) = S.deltaClass := by
  haveI : NeZero S.modulus := ⟨by simp [modulus]⟩
  simp only [deltaR, ZMod.natCast_val, ZMod.cast_id', id_eq]

/-- lower representative の common-modulus defining equation。 -/
theorem lowerR_spec (S : AdjacentFerrersSwap) :
    (3 : ZMod S.modulus) ^ S.oddTotal *
        ((S.lowerR : ℕ) : ZMod S.modulus) +
      ((affineConst S.lowerWord : ℕ) : ZMod S.modulus) = 0 := by
  have hc := leastRepresentative_cast S.lowerWord
  have hs := parityStartClass_spec S.lowerWord
  rw [← hc] at hs
  rw [S.parityModulus_lowerWord] at hs
  simpa [lowerR] using hs

/-- upper representative の common-modulus defining equation。 -/
theorem upperR_spec (S : AdjacentFerrersSwap) :
    (3 : ZMod S.modulus) ^ S.oddTotal *
        ((S.upperR : ℕ) : ZMod S.modulus) +
      ((affineConst S.upperWord : ℕ) : ZMod S.modulus) = 0 := by
  have hc := leastRepresentative_cast S.upperWord
  have hs := parityStartClass_spec S.upperWord
  rw [← hc] at hs
  rw [S.parityModulus_upperWord] at hs
  simpa [upperR] using hs

/--
`01 -> 10` の 2-adic class change。

  R(upper) = R(lower) + 2^i 3^{-(a+1)}  in ZMod(2^k)
-/
theorem upperR_cast_eq_lowerR_add_deltaClass
    (S : AdjacentFerrersSwap) :
    ((S.upperR : ℕ) : ZMod S.modulus) =
      ((S.lowerR : ℕ) : ZMod S.modulus) + S.deltaClass := by
  have hl := S.lowerR_spec
  have hu := S.upperR_spec
  have hd := S.threePow_mul_deltaClass
  have hB := S.lower_affineConst_eq_upper_add_deltaB
  have hcand :
      (3 : ZMod S.modulus) ^ S.oddTotal *
          (((S.lowerR : ℕ) : ZMod S.modulus) + S.deltaClass) +
        ((affineConst S.upperWord : ℕ) : ZMod S.modulus) = 0 := by
    have hBcast := congrArg
      (fun n : ℕ => (n : ZMod S.modulus)) hB
    push_cast at hBcast
    calc
      (3 : ZMod S.modulus) ^ S.oddTotal *
            (((S.lowerR : ℕ) : ZMod S.modulus) + S.deltaClass) +
          ((affineConst S.upperWord : ℕ) : ZMod S.modulus)
          =
          ((3 : ZMod S.modulus) ^ S.oddTotal *
              ((S.lowerR : ℕ) : ZMod S.modulus) +
            ((affineConst S.lowerWord : ℕ) : ZMod S.modulus)) +
          ((3 : ZMod S.modulus) ^ S.oddTotal * S.deltaClass -
            ((S.deltaB : ℕ) : ZMod S.modulus)) := by
              rw [hBcast]
              ring
      _ = 0 := by rw [hl, hd]; ring
  have hu' :
      (3 : ZMod S.modulus) ^ S.oddTotal *
          ((S.upperR : ℕ) : ZMod S.modulus) =
        -((affineConst S.upperWord : ℕ) : ZMod S.modulus) := by
    exact eq_neg_of_add_eq_zero_left hu
  have hcand' :
      (3 : ZMod S.modulus) ^ S.oddTotal *
          (((S.lowerR : ℕ) : ZMod S.modulus) + S.deltaClass) =
        -((affineConst S.upperWord : ℕ) : ZMod S.modulus) := by
    exact eq_neg_of_add_eq_zero_left hcand
  have hmul :
      (3 : ZMod S.modulus) ^ S.oddTotal *
          ((S.upperR : ℕ) : ZMod S.modulus) =
        (3 : ZMod S.modulus) ^ S.oddTotal *
          (((S.lowerR : ℕ) : ZMod S.modulus) + S.deltaClass) := by
    exact hu'.trans hcand'.symm
  let q : ZMod S.modulus := by
    change ZMod (2 ^ S.length)
    exact invThreePow S.length S.oddTotal
  have hInv :=
    threePow_mul_invThreePow S.length S.oddTotal
  have hInv' :
      q * (3 : ZMod S.modulus) ^ S.oddTotal = 1 := by
    dsimp [q]
    change
      invThreePow S.length S.oddTotal *
          (3 : ZMod (2 ^ S.length)) ^ S.oddTotal = 1
    simpa [mul_comm] using hInv
  calc
    ((S.upperR : ℕ) : ZMod S.modulus)
        =
        (q * (3 : ZMod S.modulus) ^ S.oddTotal) *
          ((S.upperR : ℕ) : ZMod S.modulus) := by
            rw [hInv']
            ring
    _ =
        q *
          ((3 : ZMod S.modulus) ^ S.oddTotal *
            ((S.upperR : ℕ) : ZMod S.modulus)) := by
              ring
    _ =
        q *
          ((3 : ZMod S.modulus) ^ S.oddTotal *
            (((S.lowerR : ℕ) : ZMod S.modulus) + S.deltaClass)) := by
              rw [hmul]
    _ =
        (q * (3 : ZMod S.modulus) ^ S.oddTotal) *
          (((S.lowerR : ℕ) : ZMod S.modulus) + S.deltaClass) := by
              ring
    _ =
        ((S.lowerR : ℕ) : ZMod S.modulus) + S.deltaClass := by
          rw [hInv']
          ring

/-- ordinary representatives では addition modulo common modulus。 -/
theorem upperR_eq_mod_add (S : AdjacentFerrersSwap) :
    S.upperR = (S.lowerR + S.deltaR) % S.modulus := by
  haveI : NeZero S.modulus := ⟨by simp [modulus]⟩
  have hcast := S.upperR_cast_eq_lowerR_add_deltaClass
  rw [← S.deltaR_cast] at hcast
  have hcast' :
      ((S.upperR : ℕ) : ZMod S.modulus) =
        ((S.lowerR + S.deltaR : ℕ) : ZMod S.modulus) := by
    simpa using hcast
  have hv := congrArg ZMod.val hcast'
  simp only [ZMod.val_natCast] at hv
  rw [Nat.mod_eq_of_lt S.upperR_lt_modulus] at hv
  exact hv

end AdjacentFerrersSwap
end CSTMicro
end Collatz2
