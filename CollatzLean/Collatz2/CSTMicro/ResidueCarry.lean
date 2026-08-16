import CollatzLean.Collatz2.CSTMicro.AdjacentFerrersSwap

/-!
# General CST: residue carry dichotomy

Adjacent Ferrers swap の ordinary representative change

  R_upper = (R_lower + delta) mod 2^k

を no-carry / carry に完全分岐する。

no-carry 側では

  R_upper = R_lower + delta >= R_lower
  B_upper <= B_lower

なので pure separation は自動保存される。
したがって CST を壊し得る局所 edge は carry 側だけになる。
-/

namespace Collatz2
namespace CSTMicro
namespace AdjacentFerrersSwap

/-- ordinary addition が modulus を跨がない。 -/
def NoCarry (S : AdjacentFerrersSwap) : Prop :=
  S.lowerR + S.deltaR < S.modulus

/-- ordinary addition が modulus を跨ぐ。 -/
def HasCarry (S : AdjacentFerrersSwap) : Prop :=
  S.modulus ≤ S.lowerR + S.deltaR

/-- no-carry / carry の完全二分岐。 -/
theorem noCarry_or_hasCarry (S : AdjacentFerrersSwap) :
    S.NoCarry ∨ S.HasCarry := by
  unfold NoCarry HasCarry
  omega

/-- no-carry なら modulo は消える。 -/
theorem upperR_eq_add_of_noCarry
    (S : AdjacentFerrersSwap)
    (h : S.NoCarry) :
    S.upperR = S.lowerR + S.deltaR := by
  rw [S.upperR_eq_mod_add]
  exact Nat.mod_eq_of_lt h

/-- no-carry なら representative は減らない。 -/
theorem lowerR_le_upperR_of_noCarry
    (S : AdjacentFerrersSwap)
    (h : S.NoCarry) :
    S.lowerR ≤ S.upperR := by
  rw [S.upperR_eq_add_of_noCarry h]
  omega

/-- lowerR と deltaR は各々 modulus 未満なので和は `2*modulus` 未満。 -/
theorem lowerR_add_deltaR_lt_two_mul_modulus
    (S : AdjacentFerrersSwap) :
    S.lowerR + S.deltaR < 2 * S.modulus := by
  have hl := S.lowerR_lt_modulus
  have hd := S.deltaR_lt_modulus
  omega

/-- carry なら modulo reduction は一回だけ。 -/
theorem upperR_eq_add_sub_modulus_of_hasCarry
    (S : AdjacentFerrersSwap)
    (h : S.HasCarry) :
    S.upperR = S.lowerR + S.deltaR - S.modulus := by
  rw [S.upperR_eq_mod_add]
  rw [Nat.mod_eq_sub_mod h]
  have hlt :
      S.lowerR + S.deltaR - S.modulus < S.modulus := by
    have htwo := S.lowerR_add_deltaR_lt_two_mul_modulus
    omega
  rw [Nat.mod_eq_of_lt hlt]

/-- carry なら unreduced sum は `modulus + upperR` に exact 分解する。 -/
theorem lowerR_add_deltaR_eq_modulus_add_upperR_of_hasCarry
    (S : AdjacentFerrersSwap)
    (h : S.HasCarry) :
    S.lowerR + S.deltaR = S.modulus + S.upperR := by
  have hu := S.upperR_eq_add_sub_modulus_of_hasCarry h
  have hle : S.modulus ≤ S.lowerR + S.deltaR := h
  omega

/--
CST micro object の adjacent Ferrers edge。
両側が同じ `prefix ++ 01/10 ++ suffix` を underlying word に持つ。
-/
structure MicroSwap where
  edge : AdjacentFerrersSwap
  lower : MicroObject
  upper : MicroObject
  lower_word : lower.path.word = edge.lowerWord
  upper_word : upper.path.word = edge.upperWord

namespace MicroSwap

/-- lower/upper の endpoint gap は同じ。 -/
theorem G_eq (S : MicroSwap) :
    S.lower.G = S.upper.G := by
  unfold MicroObject.G FirstPassagePath.terminalGap
  unfold FirstPassagePath.length FirstPassagePath.endpointOddCount
  rw [S.lower_word, S.upper_word]
  simp

/-- lower/upper の B は adjacent swap の affine numerators。 -/
theorem lower_B_eq (S : MicroSwap) :
    S.lower.B = affineConst S.edge.lowerWord := by
  unfold MicroObject.B
  rw [S.lower_word]

/-- upper/edge affine numerator identification。 -/
theorem upper_B_eq (S : MicroSwap) :
    S.upper.B = affineConst S.edge.upperWord := by
  unfold MicroObject.B
  rw [S.upper_word]

/-- lower representative identification。 -/
theorem lower_R_eq (S : MicroSwap) :
    S.lower.R = S.edge.lowerR := by
  unfold MicroObject.R AdjacentFerrersSwap.lowerR
  rw [S.lower_word]

/-- upper representative identification。 -/
theorem upper_R_eq (S : MicroSwap) :
    S.upper.R = S.edge.upperR := by
  unfold MicroObject.R AdjacentFerrersSwap.upperR
  rw [S.upper_word]

/--
no-carry Ferrers move は pure separation を保存する。

B は下がり、R は上がるので、CST obstruction は生成できない。
-/
theorem pureSeparation_preserved_of_noCarry
    (S : MicroSwap)
    (hNoCarry : S.edge.NoCarry)
    (hSep : S.lower.PureSeparation) :
    S.upper.PureSeparation := by
  unfold MicroObject.PureSeparation at hSep ⊢
  have hB : S.upper.B ≤ S.lower.B := by
    rw [S.lower_B_eq, S.upper_B_eq]
    exact S.edge.upper_affineConst_le_lower
  have hR : S.lower.R ≤ S.upper.R := by
    rw [S.lower_R_eq, S.upper_R_eq]
    exact S.edge.lowerR_le_upperR_of_noCarry hNoCarry
  have hGR :
      S.lower.G * S.lower.R ≤ S.upper.G * S.upper.R := by
    rw [← S.G_eq]
    exact Nat.mul_le_mul_left S.lower.G hR
  exact lt_of_le_of_lt hB (lt_of_lt_of_le hSep hGR)

/-- no-carry Ferrers move は `CSTHolds` も保存する。 -/
theorem cstHolds_preserved_of_noCarry
    (S : MicroSwap)
    (hNoCarry : S.edge.NoCarry)
    (hCST : S.lower.CSTHolds) :
    S.upper.CSTHolds := by
  apply (S.upper.cstHolds_iff_pureSeparation).2
  apply S.pureSeparation_preserved_of_noCarry hNoCarry
  exact (S.lower.cstHolds_iff_pureSeparation).1 hCST

/--
したがって upper 側が CST failure で lower 側が safe なら、
その edge は必ず carry。
-/
theorem hasCarry_of_lower_cstHolds_of_upper_failure
    (S : MicroSwap)
    (hLower : S.lower.CSTHolds)
    (hUpper : ¬ S.upper.CSTHolds) :
    S.edge.HasCarry := by
  rcases S.edge.noCarry_or_hasCarry with hNo | hCarry
  · exact False.elim (hUpper (S.cstHolds_preserved_of_noCarry hNo hLower))
  · exact hCarry

end MicroSwap
end AdjacentFerrersSwap
end CSTMicro
end Collatz2
