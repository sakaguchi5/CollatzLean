import CollatzLean.Collatz3.CSTCarry.BinaryWrap
import CollatzLean.Collatz3.CSTCarry.BinaryShift
import CollatzLean.Collatz3.CSTCarry.FirstPassageBridge

/-!
# Collatz3 CSTCarry: 証明済み部分と未解決 frontier の型

ここでは未証明の主張を theorem として置かない。
今後の研究で閉じたい条件だけを薄い predicate として名前付けする。

特に会話中に P<=17 の計算で観察した

  final carry < 2^H

は一般 theorem ではないため、`CarryBelowModulus` という目標 predicate に留める。
-/

namespace Collatz3
namespace CSTCarry

/-- carry recurrence の final carry が binary modulus より下に留まるという研究目標。 -/
def CarryBelowModulus (H finalCarry : ℕ) : Prop :=
  finalCarry < 2 ^ H

/-- boundary residue と Ferrers binary shift の組が wrap しないという条件。 -/
def NoFerrersWrap
    (H boundary : ℕ)
    (rows : List FerrersRow) : Prop :=
  boundary + ferrersBinaryShift H rows < 2 ^ H

/-- boundary residue が正しく H-bit representative であるという最小 side condition。 -/
def BoundaryInRange (H boundary : ℕ) : Prop :=
  boundary < 2 ^ H

/--
`BoundaryInRange` の下では `NoFerrersWrap` は `BinaryShiftData.Wraps` の否定そのもの。
-/
theorem noFerrersWrap_iff_not_wraps
    {H boundary : ℕ}
    {rows : List FerrersRow}
    (hBoundary : BoundaryInRange H boundary) :
    NoFerrersWrap H boundary rows ↔
      ¬ (BinaryShiftData.mk
        boundary
        (ferrersBinaryShift H rows)
        hBoundary
        (ferrersBinaryShift_lt_modulus H rows)).Wraps := by
  unfold NoFerrersWrap BinaryShiftData.Wraps BinaryShiftData.modulus
  simp only [not_le]

end CSTCarry
end Collatz3
