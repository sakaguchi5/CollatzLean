import CollatzLean.Collatz3.CSTCarry.FerrersCarry
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Positivity

/-!
# Collatz3 CSTCarry: Ferrers defect から binary residue shift へ

Ferrers weighted defect `S` に対し、fixed binary modulus `2^H` 上で

  3^P * U = S  (mod 2^H)

を解く canonical shift class を定義する。
`3^P` は奇数なので `2^H` 上で常に unit であり、解は一意である。

ここでは wrap 判定そのものは `BinaryWrap` に分離し、このファイルは
「defect -> shift」の逆復号だけを担当する。
-/

namespace Collatz3
namespace CSTCarry

/-- binary modulus `2^H` 上の `3^P` unit。 -/
def threePowBinaryUnit (P H : ℕ) : (ZMod (2 ^ H))ˣ :=
  ZMod.unitOfCoprime
    (3 ^ P)
    (((by decide : Nat.Coprime 3 2).pow_left P).pow_right H)

/-- `3^P U = S (mod 2^H)` の canonical shift class。 -/
def binaryShiftClass (P H S : ℕ) : ZMod (2 ^ H) :=
  (↑((threePowBinaryUnit P H)⁻¹) : ZMod (2 ^ H)) *
    ((S : ℕ) : ZMod (2 ^ H))

/-- canonical shift class は defining congruence を満たす。 -/
theorem binaryShiftClass_spec (P H S : ℕ) :
    (((3 ^ P : ℕ) : ZMod (2 ^ H)) * binaryShiftClass P H S) =
      ((S : ℕ) : ZMod (2 ^ H)) := by
  unfold binaryShiftClass
  have hleading :
      (((3 ^ P : ℕ) : ZMod (2 ^ H))) =
        (↑(threePowBinaryUnit P H) : ZMod (2 ^ H)) := by
    simp [threePowBinaryUnit]
  rw [hleading]
  simp [← mul_assoc]

/-- canonical shift の最小非負代表。 -/
def binaryShift (P H S : ℕ) : ℕ :=
  (binaryShiftClass P H S).val

/-- canonical shift は `H` bit 範囲内。 -/
theorem binaryShift_lt_modulus (P H S : ℕ) :
    binaryShift P H S < 2 ^ H := by
  have : NeZero (2 ^ H) := ⟨by positivity⟩
  exact ZMod.val_lt (binaryShiftClass P H S)

/-- Ferrers row listから直接 canonical binary shift を作る。 -/
def ferrersBinaryShift (H : ℕ) (rows : List FerrersRow) : ℕ :=
  binaryShift rows.length H (ferrersWeightedDefect rows)

/-- Ferrers binary shift も常に `H` bit に収まる。 -/
theorem ferrersBinaryShift_lt_modulus
    (H : ℕ) (rows : List FerrersRow) :
    ferrersBinaryShift H rows < 2 ^ H := by
  exact binaryShift_lt_modulus rows.length H (ferrersWeightedDefect rows)

end CSTCarry
end Collatz3
