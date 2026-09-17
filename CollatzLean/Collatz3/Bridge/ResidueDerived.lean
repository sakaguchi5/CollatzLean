import CollatzLean.Collatz3.Bridge.CountRunResidue
import CollatzLean.Collatz3.Binary.ResidueSupportDerived

/-!
# Collatz3 Bridge: residue lift の coarse consequences

R1 の `endpointEquation_residueLift` は odd-step 数だけ 3進精度を上げる。
ここではその深い結論を元の source depth へ射影した、固定 depth での決定性を導く。
-/

namespace Collatz3
namespace Bridge

/-- 同じ word は source residue class を固定 depth の endpoint residue classへ写す。 -/
theorem endpointEquation_preserves_residueDepth
    {K : ℕ} {w : Word}
    {x₁ x₂ y₁ y₂ : ℕ}
    (h₁ : w.EndpointEquation x₁ y₁)
    (h₂ : w.EndpointEquation x₂ y₂)
    (hx : x₁ ≡ x₂ [MOD Binary.residueDepthModulus K]) :
    y₁ ≡ y₂ [MOD Binary.residueDepthModulus K] := by
  have hDeep := endpointEquation_residueLift h₁ h₂ hx
  apply Nat.ModEq.of_dvd (h := hDeep)
  exact Binary.residueDepthModulus_dvd_add K (Word.oddSteps w)

/-- actual Runs 版の fixed-depth residue determinism。 -/
theorem runs_preserve_residueDepth
    {K : ℕ} {w : Word}
    {x₁ x₂ y₁ y₂ : ℕ}
    (h₁ : Runs w x₁ y₁)
    (h₂ : Runs w x₂ y₂)
    (hx : x₁ ≡ x₂ [MOD Binary.residueDepthModulus K]) :
    y₁ ≡ y₂ [MOD Binary.residueDepthModulus K] :=
  endpointEquation_preserves_residueDepth
    h₁.endpointEquation h₂.endpointEquation hx

end Bridge
end Collatz3
