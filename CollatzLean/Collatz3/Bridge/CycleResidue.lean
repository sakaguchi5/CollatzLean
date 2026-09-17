import CollatzLean.Collatz3.Binary.ResidueWeight
import CollatzLean.Collatz3.Semantics.OddStep
import CollatzLean.Collatz3.Arithmetic.Pow23
import Mathlib.Data.Nat.ModEq

/-!
# Collatz3 Bridge: cycle residue の一歩 relation

cycle 上の局所 3進 recurrence

`2^e * z' ≡ 1 + 3*z`

だけを薄い relation として保存する。
新しい automaton structure は導入しない。

actual `OddStep` はこの relation を任意 residue depth で満たす。
また `2^e` は 3冪法で単元なので、同じ source residue からの target residue は一意である。
-/

namespace Collatz3
namespace Bridge

/-- depth `K` における cycle residue の一歩 relation。 -/
def CycleResidueStep
    (K e start finish : ℕ) : Prop :=
  2 ^ e * finish ≡ 3 * start + 1
    [MOD Binary.residueDepthModulus K]

namespace CycleResidueStep

/-- actual odd-only step は任意の 3進 depth で residue step を実現する。 -/
theorem of_oddStep
    (K : ℕ)
    {e x y : ℕ}
    (h : OddStep e x y) :
    CycleResidueStep K e x y := by
  unfold CycleResidueStep
  rw [h.equation]

/-- 同じ source と exponent からの target residue は一意。 -/
theorem target_unique
    {K e start y z : ℕ}
    (hy : CycleResidueStep K e start y)
    (hz : CycleResidueStep K e start z) :
    y ≡ z [MOD Binary.residueDepthModulus K] := by
  unfold CycleResidueStep at hy hz
  have hScaled :
      2 ^ e * y ≡ 2 ^ e * z
        [MOD Binary.residueDepthModulus K] :=
    hy.trans hz.symm
  have hCop :
      Nat.Coprime (Binary.residueDepthModulus K) (2 ^ e) := by
    simpa [Binary.residueDepthModulus] using
      Arithmetic.coprime_threePow_twoPow (K + 1) e
  exact Nat.ModEq.cancel_left_of_coprime hCop hScaled

/-- source residue が同じなら、同じ exponent の target residue も同じ。 -/
theorem respects_source_residue
    {K e x₁ x₂ y₁ y₂ : ℕ}
    (h₁ : CycleResidueStep K e x₁ y₁)
    (h₂ : CycleResidueStep K e x₂ y₂)
    (hx : x₁ ≡ x₂ [MOD Binary.residueDepthModulus K]) :
    y₁ ≡ y₂ [MOD Binary.residueDepthModulus K] := by
  unfold CycleResidueStep at h₁ h₂
  have hRhs :
      3 * x₁ + 1 ≡ 3 * x₂ + 1
        [MOD Binary.residueDepthModulus K] :=
    (hx.mul_left 3).add_right 1
  have hScaled :
      2 ^ e * y₁ ≡ 2 ^ e * y₂
        [MOD Binary.residueDepthModulus K] :=
    h₁.trans (hRhs.trans h₂.symm)
  have hCop :
      Nat.Coprime (Binary.residueDepthModulus K) (2 ^ e) := by
    simpa [Binary.residueDepthModulus] using
      Arithmetic.coprime_threePow_twoPow (K + 1) e
  exact Nat.ModEq.cancel_left_of_coprime hCop hScaled

end CycleResidueStep

end Bridge
end Collatz3
