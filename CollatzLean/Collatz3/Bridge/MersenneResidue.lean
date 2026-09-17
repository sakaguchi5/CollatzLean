import CollatzLean.Collatz3.Bridge.MersenneRuns
import CollatzLean.Collatz3.Bridge.CountRunResidue
import CollatzLean.Collatz3.Mersenne.MacroLine

/-!
# Collatz3 Bridge: Mersenne macro と 3進 residue lift

一つの Mersenne block は `d` odd steps をまとめた actual run なので、
source の residue depth `K` は endpoint で `K+d` まで上がる。

fixed `(d,r)` affine family にも同じ lift law がそのまま適用できる。
-/

namespace Collatz3
namespace Bridge

/-- 同じ `(d,r)` Mersenne block の source residue は endpoint で `d` 段深くなる。 -/
theorem mersenneBlockData_residueLift
    {K d r u₁ u₂ x₁ x₂ y₁ y₂ : ℕ}
    (h₁ : Mersenne.BlockData d r u₁ x₁ y₁)
    (h₂ : Mersenne.BlockData d r u₂ x₂ y₂)
    (hx : x₁ ≡ x₂ [MOD Binary.residueDepthModulus K]) :
    y₁ ≡ y₂ [MOD Binary.residueDepthModulus (K + d)] := by
  have hRun₁ := mersenneBlockData_runs h₁
  have hRun₂ := mersenneBlockData_runs h₂
  have hLift := runs_residueLift hRun₁ hRun₂ hx
  have hSteps :
      Word.oddSteps (Mersenne.blockWord d r) = d :=
    Mersenne.blockWord_oddSteps h₁.depth_pos
  simpa [hSteps] using hLift

/-- fixed `(d,r)` affine line 上でも source residue equality は `d` 段増幅される。 -/
theorem mersenneAffineLine_residueLift
    {K d r u x y s t : ℕ}
    (h : Mersenne.BlockData d r u x y)
    (hSource :
      Mersenne.blockSourceLift d r x s ≡
        Mersenne.blockSourceLift d r x t
          [MOD Binary.residueDepthModulus K]) :
    Mersenne.blockEndpointLift d y s ≡
      Mersenne.blockEndpointLift d y t
        [MOD Binary.residueDepthModulus (K + d)] := by
  exact mersenneBlockData_residueLift (h.lift s) (h.lift t) hSource

end Bridge
end Collatz3
