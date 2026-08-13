import CollatzLean.Collatz2.Synthesis.SwapResidue

/-!
# Collatz2 Synthesis: thin carry extracted from word-swap residue displacement

`SwapResidue` の ZMod equality から、canonical representatives の実際の差を取り出す。

新しい packet は作らない。
`swapResidueDisplacement` は ZMod 差の最小非負代表、
`swapCarry` はその representative を足したとき common modulus を跨ぐ回数である。

両 canonical start と displacement はすべて common modulus 未満なので、carry は必ず `0` または `1`。
-/

namespace Collatz2
namespace Synthesis

/--
word swap による canonical-start residue displacement の最小非負代表。

`canonicalStart(u++v) - canonicalStart(v++u)` を
common modulus `residueModulus (u++v)` 上で取り、その `ZMod.val` を読む。
-/
def swapResidueDisplacement (u v : Word) : ℕ :=
  ZMod.val
    (((Word.canonicalStart (u ++ v) : ℕ) :
        ZMod (Word.residueModulus (u ++ v))) -
      ((Word.canonicalStart (v ++ u) : ℕ) :
        ZMod (Word.residueModulus (u ++ v))))

/-- swap residue displacement は common modulus 未満。 -/
theorem swapResidueDisplacement_lt_modulus
    (u v : Word) :
    swapResidueDisplacement u v < Word.residueModulus (u ++ v) := by
  haveI : NeZero (Word.residueModulus (u ++ v)) :=
    ⟨Nat.ne_of_gt (Word.residueModulus_pos (u ++ v))⟩
  unfold swapResidueDisplacement
  exact ZMod.val_lt _

/-- displacement を ZMod に戻すと canonical-start の差そのもの。 -/
theorem swapResidueDisplacement_cast_eq_start_sub
    (u v : Word) :
    ((swapResidueDisplacement u v : ℕ) :
        ZMod (Word.residueModulus (u ++ v))) =
      (((Word.canonicalStart (u ++ v) : ℕ) :
          ZMod (Word.residueModulus (u ++ v))) -
        ((Word.canonicalStart (v ++ u) : ℕ) :
          ZMod (Word.residueModulus (u ++ v)))) := by
  haveI : NeZero (Word.residueModulus (u ++ v)) :=
    ⟨Nat.ne_of_gt (Word.residueModulus_pos (u ++ v))⟩
  unfold swapResidueDisplacement
  exact ZMod.natCast_zmod_val _

/--
同じ displacement は `omega` による residue displacement でもある。

center / commutator 側と representative / carry 側をここで接続する。
-/
theorem swapResidueDisplacement_cast_eq_omega
    (u v : Word) :
    ((swapResidueDisplacement u v : ℕ) :
        ZMod (Word.residueModulus (u ++ v))) =
      -((↑((Word.leadingUnit (u ++ v))⁻¹) :
          ZMod (Word.residueModulus (u ++ v))) *
        ((MatrixAnalysis.omega
          (AffineTransfer.ofWord u)
          (AffineTransfer.ofWord v) : ℤ) :
            ZMod (Word.residueModulus (u ++ v)))) := by
  rw [swapResidueDisplacement_cast_eq_start_sub]
  exact oddStartClass_swap_displacement u v

/--
`canonicalStart(v++u) + displacement` の common-modulus remainder は
`canonicalStart(u++v)` そのもの。
-/
theorem canonicalStart_swap_add_displacement_mod
    (u v : Word) :
    (Word.canonicalStart (v ++ u) + swapResidueDisplacement u v) %
        Word.residueModulus (u ++ v) =
      Word.canonicalStart (u ++ v) := by
  let m := Word.residueModulus (u ++ v)
  haveI : NeZero m :=
    ⟨Nat.ne_of_gt (by
      simp only [Word.residueModulus_pos, m])⟩
  have hshift :=
    swapResidueDisplacement_cast_eq_start_sub u v
  have hcast :
      (((Word.canonicalStart (v ++ u) +
          swapResidueDisplacement u v : ℕ) : ZMod m)) =
        ((Word.canonicalStart (u ++ v) : ℕ) : ZMod m) := by
    rw [Nat.cast_add]
    rw [hshift]
    ring
  have hval := congrArg ZMod.val hcast
  have hxlt : Word.canonicalStart (u ++ v) < m := by
    simpa [m] using
      Word.canonicalStart_lt_modulus (u ++ v)
  change
    (Word.canonicalStart (v ++ u) +
        swapResidueDisplacement u v) % m =
      Word.canonicalStart (u ++ v)
  calc
    (Word.canonicalStart (v ++ u) +
        swapResidueDisplacement u v) % m
        =
        ((((Word.canonicalStart (v ++ u) +
            swapResidueDisplacement u v : ℕ) : ZMod m)).val) := by
          symm
          exact ZMod.val_natCast m
            (Word.canonicalStart (v ++ u) +
              swapResidueDisplacement u v)
    _ =
        (((Word.canonicalStart (u ++ v) : ℕ) : ZMod m).val) := hval
    _ = Word.canonicalStart (u ++ v) := by
        exact ZMod.val_natCast_of_lt hxlt

/--
word swap representative の carry。

`v++u` の canonical start に displacement を足して common modulus を跨がなければ `0`、
跨げば `1`。二回以上跨ぐことはない。
-/
def swapCarry (u v : Word) : ℕ :=
  if Word.canonicalStart (v ++ u) + swapResidueDisplacement u v <
      Word.residueModulus (u ++ v) then 0 else 1

/-- swap carry は `0` または `1`。 -/
theorem swapCarry_eq_zero_or_one
    (u v : Word) :
    swapCarry u v = 0 ∨ swapCarry u v = 1 := by
  unfold swapCarry
  split_ifs <;> simp

/-- carry が `0` であることは modulus を跨がないことと同値。 -/
theorem swapCarry_eq_zero_iff
    (u v : Word) :
    swapCarry u v = 0 ↔
      Word.canonicalStart (v ++ u) + swapResidueDisplacement u v <
        Word.residueModulus (u ++ v) := by
  unfold swapCarry
  split_ifs with h
  · simp [h]
  · simp [h]

/-- carry が `1` であることは modulus を一度跨ぐことと同値。 -/
theorem swapCarry_eq_one_iff
    (u v : Word) :
    swapCarry u v = 1 ↔
      Word.residueModulus (u ++ v) ≤
        Word.canonicalStart (v ++ u) + swapResidueDisplacement u v := by
  unfold swapCarry
  split_ifs with h
  · simp [ Nat.not_le_of_gt h]
  · have hle := Nat.le_of_not_gt h
    simp [ hle]

/--
actual canonical representatives の exact carry equation。

`canonicalStart(v++u) + displacement
   = canonicalStart(u++v) + carry * modulus`。
-/
theorem swapCarry_spec
    (u v : Word) :
    Word.canonicalStart (v ++ u) + swapResidueDisplacement u v =
      Word.canonicalStart (u ++ v) +
        swapCarry u v * Word.residueModulus (u ++ v) := by
  let m := Word.residueModulus (u ++ v)
  let x := Word.canonicalStart (u ++ v)
  let y := Word.canonicalStart (v ++ u)
  let s := swapResidueDisplacement u v
  have hmpos : 0 < m := by
    simp only [Word.residueModulus_pos, m]
  have hxlt : x < m := by
    simpa [x, m] using Word.canonicalStart_lt_modulus (u ++ v)
  have hylt : y < m := by
    have hy := Word.canonicalStart_lt_modulus (v ++ u)
    have hmod := residueModulus_swap u v
    rw [hmod] at hy
    simpa [y, m] using hy
  have hslt : s < m := by
    simpa [s, m] using swapResidueDisplacement_lt_modulus u v
  have hmodEq : (y + s) % m = x := by
    simpa [x, y, s, m] using canonicalStart_swap_add_displacement_mod u v
  unfold swapCarry
  change
    y + s = x +
      (if y + s < m then 0 else 1) * m
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

/-- carry は高々1。 -/
theorem swapCarry_le_one
    (u v : Word) :
    swapCarry u v ≤ 1 := by
  rcases swapCarry_eq_zero_or_one u v with h | h <;> simp [h]

/-- carry `0` では representative equality に modulus 補正が不要。 -/
theorem canonicalStart_swap_eq_of_carry_zero
    (u v : Word)
    (hcarry : swapCarry u v = 0) :
    Word.canonicalStart (v ++ u) + swapResidueDisplacement u v =
      Word.canonicalStart (u ++ v) := by
  have h := swapCarry_spec u v
  rw [hcarry] at h
  simpa using h

/-- carry `1` では exactly 一つの common modulus を補正する。 -/
theorem canonicalStart_swap_add_modulus_eq_of_carry_one
    (u v : Word)
    (hcarry : swapCarry u v = 1) :
    Word.canonicalStart (v ++ u) + swapResidueDisplacement u v =
      Word.canonicalStart (u ++ v) + Word.residueModulus (u ++ v) := by
  have h := swapCarry_spec u v
  rw [hcarry] at h
  simpa using h

end Synthesis
end Collatz2
