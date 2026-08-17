import CollatzLean.Collatz2.CSTMicro.CarryGeometry.FirstFailureFareyGeometry

/-!
# General CST: first-failure Farey packet の actual extraction

`FirstFailureFareyGeometry` では、actual first-failure carry 側と
pure Farey packet 側を interface だけで分離していた。

このファイルではその残り bridge を閉じる。

一つの adjacent Ferrers swap に対して

  i = position,
  d = 2 + right.length,
  a = oddCount left + 1,
  r = oddCount right,

と置く。small modulus `2^d` における `3^{-a}` の least representative を
`u` とすると

  0 < u < 2^d,
  3^a * u = 1 + 2^d * q

となる。そこで

  h = 2^d - u,
  s = 3^a - q

と置けば

  2^d * s - 3^a * h = 1.

さらに full modulus `2^(i+d)` 上の local residue は exact に

  deltaR = 2^i * u

なので、carry complement は

  2^k - deltaR = 2^i * h

へ factor する。

これにより任意の `FirstFailureEdge` から `FirstFailureFareyData` を
無条件に構成できる。最後に既存の strict positive carry jump と結合し、
actual first failure の Farey residue `D` が strict positive であることまで証明する。
-/

namespace Collatz2
namespace CSTMicro

namespace AdjacentFerrersSwap

/-- swap position から terminal までの残り長さ `d = 2 + |right|`。 -/
def fareyTailDepth (S : AdjacentFerrersSwap) : ℕ :=
  2 + S.rightContext.length

/-- local inverse に現れる左側 exponent `a = oddCount(left)+1`。 -/
def fareyLeftExponent (S : AdjacentFerrersSwap) : ℕ :=
  oddCount S.leftContext + 1

/-- cell の右側 odd exponent `r`。 -/
def fareyRightExponent (S : AdjacentFerrersSwap) : ℕ :=
  oddCount S.rightContext

/-- small modulus `2^d` における `3^{-a}` の ordinary representative。 -/
def fareyLocalInverse (S : AdjacentFerrersSwap) : ℕ :=
  (invThreePow S.fareyTailDepth S.fareyLeftExponent).val

/-- `3^a*u = 1 + 2^d*q` の quotient `q`。 -/
def fareyLocalQuotient (S : AdjacentFerrersSwap) : ℕ :=
  (3 ^ S.fareyLeftExponent * S.fareyLocalInverse) /
    (2 ^ S.fareyTailDepth)

/-- carry complement の odd/Farey 側 factor `h = 2^d-u`。 -/
def fareyH (S : AdjacentFerrersSwap) : ℕ :=
  2 ^ S.fareyTailDepth - S.fareyLocalInverse

/-- determinant-one equation の companion coordinate `s = 3^a-q`。 -/
def fareyS (S : AdjacentFerrersSwap) : ℤ :=
  (3 : ℤ) ^ S.fareyLeftExponent - (S.fareyLocalQuotient : ℤ)

/-- full length は `i+d`。 -/
theorem length_eq_position_add_fareyTailDepth
    (S : AdjacentFerrersSwap) :
    S.length = S.position + S.fareyTailDepth := by
  unfold length position fareyTailDepth
  omega

/-- total odd count は `a+r`。 -/
theorem oddTotal_eq_fareyLeftExponent_add_fareyRightExponent
    (S : AdjacentFerrersSwap) :
    S.oddTotal = S.fareyLeftExponent + S.fareyRightExponent := by
  unfold oddTotal fareyLeftExponent fareyRightExponent
  omega

/-- tail depth は少なくとも 2。 -/
theorem two_le_fareyTailDepth
    (S : AdjacentFerrersSwap) :
    2 ≤ S.fareyTailDepth := by
  unfold fareyTailDepth
  omega

/-- small modulus `2^d` は 1 より大きい。 -/
theorem one_lt_twoPow_fareyTailDepth
    (S : AdjacentFerrersSwap) :
    1 < 2 ^ S.fareyTailDepth := by
  have hd := S.two_le_fareyTailDepth
  have hpow :
      2 ^ 2 ≤ 2 ^ S.fareyTailDepth :=
    Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hd
  exact lt_of_lt_of_le (by norm_num) hpow

/-- small inverse representative は modulus 未満。 -/
theorem fareyLocalInverse_lt
    (S : AdjacentFerrersSwap) :
    S.fareyLocalInverse < 2 ^ S.fareyTailDepth := by
  haveI : NeZero (2 ^ S.fareyTailDepth) := ⟨by positivity⟩
  unfold fareyLocalInverse
  exact ZMod.val_lt _

theorem fareyLocalInverse_pos
    (S : AdjacentFerrersSwap) :
    0 < S.fareyLocalInverse := by
  let d := S.fareyTailDepth
  let a := S.fareyLeftExponent
  have hmod : 1 < 2 ^ d := by
    simpa [d] using S.one_lt_twoPow_fareyTailDepth
  haveI : NeZero (2 ^ d) := ⟨by omega⟩
  haveI : Fact (1 < 2 ^ d) := ⟨hmod⟩
  have hInv := threePow_mul_invThreePow d a
  have hne : invThreePow d a ≠ 0 := by
    intro hz
    have hInv' := hInv
    rw [hz] at hInv'
    simp only [mul_zero] at hInv'
    exact zero_ne_one hInv'
  unfold fareyLocalInverse
  change 0 < (invThreePow d a).val
  exact (ZMod.val_pos).2 hne

/-- small inverse を cast し直すと元の inverse class に戻る。 -/
theorem fareyLocalInverse_cast
    (S : AdjacentFerrersSwap) :
    ((S.fareyLocalInverse : ℕ) :
        ZMod (2 ^ S.fareyTailDepth)) =
      invThreePow S.fareyTailDepth S.fareyLeftExponent := by
  haveI : NeZero (2 ^ S.fareyTailDepth) := ⟨by positivity⟩
  unfold fareyLocalInverse
  exact ZMod.natCast_zmod_val _

/-- small modulus 上で `3^a*u = 1`。 -/
theorem threePow_mul_fareyLocalInverse_cast
    (S : AdjacentFerrersSwap) :
    (3 : ZMod (2 ^ S.fareyTailDepth)) ^ S.fareyLeftExponent *
        ((S.fareyLocalInverse : ℕ) : ZMod (2 ^ S.fareyTailDepth)) = 1 := by
  rw [S.fareyLocalInverse_cast]
  exact threePow_mul_invThreePow
    S.fareyTailDepth S.fareyLeftExponent

/-- ordinary remainder として `3^a*u mod 2^d = 1`。 -/
theorem threePow_mul_fareyLocalInverse_mod
    (S : AdjacentFerrersSwap) :
    (3 ^ S.fareyLeftExponent * S.fareyLocalInverse) %
        (2 ^ S.fareyTailDepth) = 1 := by
  have hCast :
      (((3 ^ S.fareyLeftExponent * S.fareyLocalInverse : ℕ)) :
          ZMod (2 ^ S.fareyTailDepth)) =
        ((1 : ℕ) : ZMod (2 ^ S.fareyTailDepth)) := by
    push_cast
    simpa using S.threePow_mul_fareyLocalInverse_cast
  have hVal := congrArg ZMod.val hCast
  have hOne := S.one_lt_twoPow_fareyTailDepth
  simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hOne] using hVal

/--
small inverse の Euclidean division を exact equation に戻す。

  3^a*u = 1 + 2^d*q.
-/
theorem threePow_mul_fareyLocalInverse_eq_one_add
    (S : AdjacentFerrersSwap) :
    3 ^ S.fareyLeftExponent * S.fareyLocalInverse =
      1 + 2 ^ S.fareyTailDepth * S.fareyLocalQuotient := by
  have hmod := S.threePow_mul_fareyLocalInverse_mod
  have hdiv :=
    Nat.mod_add_div
      (3 ^ S.fareyLeftExponent * S.fareyLocalInverse)
      (2 ^ S.fareyTailDepth)
  rw [hmod] at hdiv
  unfold fareyLocalQuotient
  exact hdiv.symm

/-- `h = 2^d-u` の integer cast。 -/
theorem fareyH_cast
    (S : AdjacentFerrersSwap) :
    (S.fareyH : ℤ) =
      (2 : ℤ) ^ S.fareyTailDepth - (S.fareyLocalInverse : ℤ) := by
  have hu :
      S.fareyLocalInverse ≤ 2 ^ S.fareyTailDepth :=
    Nat.le_of_lt S.fareyLocalInverse_lt
  unfold fareyH
  rw [Nat.cast_sub hu]
  norm_num

/-- `h` は正。 -/
theorem fareyH_pos
    (S : AdjacentFerrersSwap) :
    0 < S.fareyH := by
  unfold fareyH
  exact Nat.sub_pos_of_lt S.fareyLocalInverse_lt

/--
small inverse quotient から determinant-one equation を得る。

  2^d*s - 3^a*h = 1.
-/
theorem farey_determinant_one
    (S : AdjacentFerrersSwap) :
    (2 : ℤ) ^ S.fareyTailDepth * S.fareyS -
        (3 : ℤ) ^ S.fareyLeftExponent * (S.fareyH : ℤ) = 1 := by
  have hNat := S.threePow_mul_fareyLocalInverse_eq_one_add
  have hInt :
      (3 : ℤ) ^ S.fareyLeftExponent * (S.fareyLocalInverse : ℤ) =
        1 + (2 : ℤ) ^ S.fareyTailDepth *
          (S.fareyLocalQuotient : ℤ) := by
    exact_mod_cast hNat
  have hH := S.fareyH_cast
  unfold fareyS
  rw [hH]
  calc
    (2 : ℤ) ^ S.fareyTailDepth *
          ((3 : ℤ) ^ S.fareyLeftExponent -
            (S.fareyLocalQuotient : ℤ)) -
        (3 : ℤ) ^ S.fareyLeftExponent *
          ((2 : ℤ) ^ S.fareyTailDepth -
            (S.fareyLocalInverse : ℤ))
        =
      (3 : ℤ) ^ S.fareyLeftExponent *
          (S.fareyLocalInverse : ℤ) -
        (2 : ℤ) ^ S.fareyTailDepth *
          (S.fareyLocalQuotient : ℤ) := by ring
    _ = 1 := by linarith

/-- `2^i*u` は full modulus 未満。 -/
theorem twoPow_mul_fareyLocalInverse_lt_modulus
    (S : AdjacentFerrersSwap) :
    2 ^ S.position * S.fareyLocalInverse < S.modulus := by
  have hu := S.fareyLocalInverse_lt
  have hp : 0 < 2 ^ S.position := Nat.pow_pos (by omega)
  have hmul :
      2 ^ S.position * S.fareyLocalInverse <
        2 ^ S.position * 2 ^ S.fareyTailDepth :=
    (Nat.mul_lt_mul_left hp).2 hu
  rw [← pow_add] at hmul
  rw [← S.length_eq_position_add_fareyTailDepth] at hmul
  simpa [modulus] using hmul

/--
small inverse equation を full modulus へ `2^i` 倍して持ち上げる。
-/
theorem threePow_mul_scaled_fareyLocalInverse_eq
    (S : AdjacentFerrersSwap) :
    3 ^ S.fareyLeftExponent *
        (2 ^ S.position * S.fareyLocalInverse) =
      2 ^ S.position +
        2 ^ S.length * S.fareyLocalQuotient := by
  have hsmall := S.threePow_mul_fareyLocalInverse_eq_one_add
  calc
    3 ^ S.fareyLeftExponent *
          (2 ^ S.position * S.fareyLocalInverse)
        =
      2 ^ S.position *
        (3 ^ S.fareyLeftExponent * S.fareyLocalInverse) := by ring
    _ =
      2 ^ S.position *
        (1 + 2 ^ S.fareyTailDepth * S.fareyLocalQuotient) := by
          rw [hsmall]
    _ =
      2 ^ S.position +
        (2 ^ S.position * 2 ^ S.fareyTailDepth) *
          S.fareyLocalQuotient := by ring
    _ =
      2 ^ S.position +
        2 ^ S.length * S.fareyLocalQuotient := by
          rw [← pow_add, ← S.length_eq_position_add_fareyTailDepth]

/-- full modulus 上でも scaled small inverse は `3^a` を掛けると `2^i`。 -/
theorem threePow_mul_scaled_fareyLocalInverse_cast
    (S : AdjacentFerrersSwap) :
    (3 : ZMod S.modulus) ^ S.fareyLeftExponent *
        (((2 ^ S.position * S.fareyLocalInverse : ℕ)) : ZMod S.modulus) =
      (((2 ^ S.position : ℕ)) : ZMod S.modulus) := by
  have hNat := S.threePow_mul_scaled_fareyLocalInverse_eq
  have hCast := congrArg
    (fun n : ℕ => (n : ZMod S.modulus)) hNat
  push_cast at hCast
  have hModZero :
      (((2 ^ S.length : ℕ)) : ZMod S.modulus) = 0 := by
    unfold modulus
    exact ZMod.natCast_self (2 ^ S.length)
  push_cast at hModZero
  calc
    (3 : ZMod S.modulus) ^ S.fareyLeftExponent *
        (((2 ^ S.position * S.fareyLocalInverse : ℕ)) :
          ZMod S.modulus)
        =
      (3 : ZMod S.modulus) ^ S.fareyLeftExponent *
        ((2 : ZMod S.modulus) ^ S.position *
          (S.fareyLocalInverse : ZMod S.modulus)) := by
        push_cast
        rfl
    _ =
      (2 : ZMod S.modulus) ^ S.position +
        (2 : ZMod S.modulus) ^ S.length *
          (S.fareyLocalQuotient : ZMod S.modulus) :=
      hCast
    _ =
      (2 : ZMod S.modulus) ^ S.position := by
        rw [hModZero]
        simp
    _ =
      (((2 ^ S.position : ℕ)) : ZMod S.modulus) := by
        push_cast
        rfl

/-- full local class `deltaClass` も `3^a` を掛けると `2^i`。 -/
theorem threePow_mul_deltaClass_eq_twoPow
    (S : AdjacentFerrersSwap) :
    (3 : ZMod S.modulus) ^ S.fareyLeftExponent * S.deltaClass =
      (((2 ^ S.position : ℕ)) : ZMod S.modulus) := by
  unfold deltaClass
  change
    (3 : ZMod (2 ^ S.length)) ^ S.fareyLeftExponent *
        ((2 : ZMod (2 ^ S.length)) ^ S.position *
          invThreePow S.length S.fareyLeftExponent) =
      (((2 ^ S.position : ℕ)) : ZMod (2 ^ S.length))
  have hInv :=
    threePow_mul_invThreePow S.length S.fareyLeftExponent
  push_cast
  calc
    (3 : ZMod (2 ^ S.length)) ^ S.fareyLeftExponent *
        ((2 : ZMod (2 ^ S.length)) ^ S.position *
          invThreePow S.length S.fareyLeftExponent)
        =
      (2 : ZMod (2 ^ S.length)) ^ S.position *
        ((3 : ZMod (2 ^ S.length)) ^ S.fareyLeftExponent *
          invThreePow S.length S.fareyLeftExponent) := by ring
    _ = (2 : ZMod (2 ^ S.length)) ^ S.position := by
      rw [hInv]
      ring

/--
full modulus 上で `2^i*u` と `deltaClass` は同じ class。
`3^a` が unit なので cancellation する。
-/
theorem scaled_fareyLocalInverse_cast_eq_deltaClass
    (S : AdjacentFerrersSwap) :
    (((2 ^ S.position * S.fareyLocalInverse : ℕ)) : ZMod S.modulus) =
      S.deltaClass := by
  have hx := S.threePow_mul_scaled_fareyLocalInverse_cast
  have hd := S.threePow_mul_deltaClass_eq_twoPow
  have hmul :
      (3 : ZMod S.modulus) ^ S.fareyLeftExponent *
          (((2 ^ S.position * S.fareyLocalInverse : ℕ)) : ZMod S.modulus) =
        (3 : ZMod S.modulus) ^ S.fareyLeftExponent * S.deltaClass := by
    exact hx.trans hd.symm
  let q : ZMod S.modulus := by
    change ZMod (2 ^ S.length)
    exact invThreePow S.length S.fareyLeftExponent
  have hInv :=
    threePow_mul_invThreePow S.length S.fareyLeftExponent
  have hInv' :
      q * (3 : ZMod S.modulus) ^ S.fareyLeftExponent = 1 := by
    dsimp [q]
    change
      invThreePow S.length S.fareyLeftExponent *
          (3 : ZMod (2 ^ S.length)) ^ S.fareyLeftExponent = 1
    simpa [mul_comm] using hInv
  calc
    (((2 ^ S.position * S.fareyLocalInverse : ℕ)) : ZMod S.modulus)
        =
      (q * (3 : ZMod S.modulus) ^ S.fareyLeftExponent) *
        (((2 ^ S.position * S.fareyLocalInverse : ℕ)) : ZMod S.modulus) := by
          rw [hInv']
          ring
    _ =
      q *
        ((3 : ZMod S.modulus) ^ S.fareyLeftExponent *
          (((2 ^ S.position * S.fareyLocalInverse : ℕ)) : ZMod S.modulus)) := by
            ring
    _ =
      q *
        ((3 : ZMod S.modulus) ^ S.fareyLeftExponent * S.deltaClass) := by
          rw [hmul]
    _ =
      (q * (3 : ZMod S.modulus) ^ S.fareyLeftExponent) * S.deltaClass := by
        ring
    _ = S.deltaClass := by
      rw [hInv']
      ring

/--
full local ordinary representative は exact に `2^i*u`。
-/
theorem deltaR_eq_twoPow_mul_fareyLocalInverse
    (S : AdjacentFerrersSwap) :
    S.deltaR = 2 ^ S.position * S.fareyLocalInverse := by
  have hClass := S.scaled_fareyLocalInverse_cast_eq_deltaClass
  have hVal := congrArg ZMod.val hClass
  have hxlt := S.twoPow_mul_fareyLocalInverse_lt_modulus
  have hxval :
      ((((2 ^ S.position * S.fareyLocalInverse : ℕ)) : ZMod S.modulus).val) =
        2 ^ S.position * S.fareyLocalInverse :=
    ZMod.val_natCast_of_lt hxlt
  rw [hxval] at hVal
  simpa only [deltaR] using hVal.symm

/--
carry complement は exact に `2^i*h`。
-/
theorem carryComplement_eq_twoPow_mul_fareyH
    (S : AdjacentFerrersSwap) :
    S.carryComplement = 2 ^ S.position * S.fareyH := by
  unfold carryComplement fareyH modulus
  rw [S.deltaR_eq_twoPow_mul_fareyLocalInverse]
  rw [S.length_eq_position_add_fareyTailDepth, pow_add]
  rw [← Nat.mul_sub_left_distrib]

/-- 一つの adjacent swap から pure Farey packet を canonical に構成する。 -/
def toFareyCellPacket
    (S : AdjacentFerrersSwap) : FareyCellPacket := {
  i := S.position
  d := S.fareyTailDepth
  a := S.fareyLeftExponent
  r := S.fareyRightExponent
  k := S.length
  m := S.oddTotal
  h := (S.fareyH : ℤ)
  s := S.fareyS
  G := (2 : ℤ) ^ S.length - (3 : ℤ) ^ S.oddTotal
  k_eq := S.length_eq_position_add_fareyTailDepth
  m_eq := S.oddTotal_eq_fareyLeftExponent_add_fareyRightExponent
  gap_eq := rfl
  determinant_one := S.farey_determinant_one
}

end AdjacentFerrersSwap

namespace FirstFailureEdge

/-- actual first-failure edge から Farey bridge data を canonical に構成する。 -/
def toFirstFailureFareyData
    (F : FirstFailureEdge) : FirstFailureFareyData F := {
  farey := F.step.edge.toFareyCellPacket
  i_eq_position := rfl
  d_eq_tail := by
    rfl
  a_eq_left := by
    rfl
  r_eq_right := by
    rfl
  k_eq_length := rfl
  m_eq_oddTotal := rfl
  complement_eq := by
    change
      (F.step.edge.carryComplement : ℤ) =
        (2 : ℤ) ^ F.step.edge.position * (F.step.edge.fareyH : ℤ)
    exact_mod_cast F.step.edge.carryComplement_eq_twoPow_mul_fareyH
}

/--
前ファイルで残していた bridge の existence。
任意の first-failure edge は actual Farey packet を持つ。
-/
theorem exists_firstFailureFareyData
    (F : FirstFailureEdge) :
    Nonempty (FirstFailureFareyData F) := by
  exact ⟨F.toFirstFailureFareyData⟩

end FirstFailureEdge

namespace FirstFailureFareyData

/-- actual first-passage gap と Farey packet の `G` は同じ integer。 -/
theorem farey_G_eq_wordTerminalGap
    {F : FirstFailureEdge}
    (D : FirstFailureFareyData F) :
    D.farey.G =
      (wordTerminalGap F.step.edge.lowerWord : ℤ) := by
  have hContract :
      3 ^ F.step.edge.oddTotal < F.step.edge.modulus := by
    have h := F.lower_firstPassage.2.2
    unfold CoefficientContracting at h
    rw [F.step.lower_eq] at h
    simpa [AdjacentFerrersSwap.modulus] using h
  have hle :
      3 ^ F.step.edge.oddTotal ≤ F.step.edge.modulus :=
    Nat.le_of_lt hContract
  rw [D.farey.gap_eq, D.k_eq_length, D.m_eq_oddTotal]
  rw [F.step.edge.wordTerminalGap_lowerWord]
  rw [Nat.cast_sub hle]
  simp [AdjacentFerrersSwap.modulus]

/--
actual carry jump を Farey residue へ exact factorization する。

  J = 2^i * 2^d * D.
-/
theorem carryCellJumpInt_eq_twoPow_mul_twoPow_mul_residue
    {F : FirstFailureEdge}
    (D : FirstFailureFareyData F) :
    F.step.edge.carryCellJumpInt =
      (2 : ℤ) ^ D.farey.i *
        ((2 : ℤ) ^ D.farey.d * D.farey.residue) := by
  have hG := D.farey_G_eq_wordTerminalGap
  have hTwo := D.farey.twoPow_mul_residue
  unfold AdjacentFerrersSwap.carryCellJumpInt
  rw [D.complement_eq]
  rw [← hG]
  unfold AdjacentFerrersSwap.deltaB
  push_cast
  rw [← D.i_eq_position, ← D.r_eq_right]
  calc
    D.farey.G *
          ((2 : ℤ) ^ D.farey.i * D.farey.h) -
        (2 : ℤ) ^ D.farey.i * (3 : ℤ) ^ D.farey.r
        =
      (2 : ℤ) ^ D.farey.i *
        (D.farey.G * D.farey.h - (3 : ℤ) ^ D.farey.r) := by ring
    _ =
      (2 : ℤ) ^ D.farey.i *
        ((2 : ℤ) ^ D.farey.d * D.farey.residue) := by
          rw [← hTwo]

/--
actual first failure の Farey residue `D` は strict positive。
-/
theorem residue_pos
    {F : FirstFailureEdge}
    (D : FirstFailureFareyData F) :
    0 < D.farey.residue := by
  have hJump := F.carryCellJumpInt_pos
  have hFactor :=
    D.carryCellJumpInt_eq_twoPow_mul_twoPow_mul_residue
  have hi : 0 < (2 : ℤ) ^ D.farey.i := by
    positivity
  have hd : 0 < (2 : ℤ) ^ D.farey.d := by
    positivity
  rw [hFactor] at hJump
  have hInner :
      0 < (2 : ℤ) ^ D.farey.d * D.farey.residue :=
    pos_of_mul_pos_right hJump (le_of_lt hi)
  exact
    pos_of_mul_pos_right hInner (le_of_lt hd)

/-- actual first failure では `G*h > 3^r`。 -/
theorem threePow_lt_gap_mul_h
    {F : FirstFailureEdge}
    (D : FirstFailureFareyData F) :
    (3 : ℤ) ^ D.farey.r < D.farey.G * D.farey.h := by
  exact D.farey.threePow_lt_gap_mul_h_of_residue_pos D.residue_pos

/-- actual first failure では双対側でも `G*s > 2^i`。 -/
theorem twoPow_lt_gap_mul_s
    {F : FirstFailureEdge}
    (D : FirstFailureFareyData F) :
    (2 : ℤ) ^ D.farey.i < D.farey.G * D.farey.s := by
  exact D.farey.twoPow_lt_gap_mul_s_of_residue_pos D.residue_pos

end FirstFailureFareyData

namespace FirstFailureEdge

/--
first failure を一つの positive Farey + polynomial-small error packet にまとめる。

ここで得られる `D` は actual edge から canonical に抽出したものであり、
もはや外部 bridge 仮定を必要としない。
-/
theorem exists_positive_farey_packet_with_polynomial_error
    (F : FirstFailureEdge)
    {K A : ℕ}
    (hGap :
      ∀ p H : ℕ,
        0 < p →
        3 ^ p < 2 ^ H →
        3 ^ p ≤
          K * (p + 1) ^ A * (2 ^ H - 3 ^ p)) :
    ∃ D : FirstFailureFareyData F,
      0 < D.farey.residue ∧
      (F.step.edge.lowerR : ℤ) =
        (2 : ℤ) ^ D.farey.i * D.farey.h +
          (F.step.edge.upperR : ℤ) ∧
      F.step.edge.upperR ≤
        K * (D.farey.k + 1) ^ (A + 1) := by
  let D := F.toFirstFailureFareyData
  refine ⟨D, D.residue_pos, ?_, ?_⟩
  · exact D.lowerR_eq_twoPow_mul_h_add_upperR
  · exact D.upperR_le_lengthPolynomial hGap

end FirstFailureEdge

end CSTMicro
end Collatz2
