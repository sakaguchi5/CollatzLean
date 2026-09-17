import CollatzLean.Collatz3.Binary.ResidueSupport
import CollatzLean.Collatz3.Arithmetic.ModThreePow
import CollatzLean.Collatz3.Bridge.RunsToCanonical
import Mathlib.Data.Nat.ModEq


/-!
# Collatz3 Bridge: source residue + exponent word -> endpoint residue lift

既存 `Word.EndpointEquation`

`2^E * y = 3^m * x + affineConst(w)`

を使い、source が mod `3^(K+1)` で一致する二つの realization は、
`m` odd steps 後には mod `3^(K+m+1)` で endpoint も一致することを導く。

新しい affine constant は定義しない。
actual `Runs` 版は既存 `Runs.endpointEquation` から直ちに得る。
-/

namespace Collatz3
namespace Bridge

/--
同じ exponent word の endpoint equations は、source residue の 3進精度を
odd-step 数だけ増やして endpoint residue へ運ぶ。
-/
theorem endpointEquation_residueLift
    {K : ℕ} {w : Word}
    {x₁ x₂ y₁ y₂ : ℕ}
    (h₁ : w.EndpointEquation x₁ y₁)
    (h₂ : w.EndpointEquation x₂ y₂)
    (hx : x₁ ≡ x₂ [MOD Binary.residueDepthModulus K]) :
    y₁ ≡ y₂
      [MOD Binary.residueDepthModulus (K + Word.oddSteps w)] := by
  let m : ℕ := Word.oddSteps w
  let E : ℕ := Word.twoSteps w
  let M : ℕ := Binary.residueDepthModulus (K + m)
  have hScaled := hx.mul_left' (3 ^ m)
  have hModEq :
      3 ^ m * Binary.residueDepthModulus K = M := by
    dsimp [M, Binary.residueDepthModulus]
    calc
      3 ^ m * 3 ^ (K + 1) = 3 ^ (m + (K + 1)) := by
        rw [pow_add]
      _ = 3 ^ (K + m + 1) := by
        congr 1
        omega
  rw [hModEq] at hScaled
  have hRhs :
      3 ^ m * x₁ + Word.affineConst w ≡
        3 ^ m * x₂ + Word.affineConst w [MOD M] :=
    hScaled.add_right (Word.affineConst w)
  have hMain₁ := (Word.endpointEquation_iff w x₁ y₁).1 h₁
  have hMain₂ := (Word.endpointEquation_iff w x₂ y₂).1 h₂
  have hTwo :
      2 ^ E * y₁ ≡ 2 ^ E * y₂ [MOD M] := by
    dsimp [E, m] at hMain₁ hMain₂
    calc
      2 ^ E * y₁ = 3 ^ m * x₁ + Word.affineConst w := by
        simpa [E, m] using hMain₁
      _ ≡ 3 ^ m * x₂ + Word.affineConst w [MOD M] := hRhs
      _ = 2 ^ E * y₂ := by
        simpa [E, m] using hMain₂.symm
  have hCop : Nat.Coprime M (2 ^ E) := by
    dsimp [M, E, m, Binary.residueDepthModulus]
    exact Arithmetic.coprime_threePow_twoPow (K + m + 1) (Word.twoSteps w)
  have hCancel : y₁ ≡ y₂ [MOD M] :=
    Nat.ModEq.cancel_left_of_coprime hCop hTwo
  simpa [M, m] using hCancel

/-- actual finite runs 版の residue lift。 -/
theorem runs_residueLift
    {K : ℕ} {w : Word}
    {x₁ x₂ y₁ y₂ : ℕ}
    (h₁ : Runs w x₁ y₁)
    (h₂ : Runs w x₂ y₂)
    (hx : x₁ ≡ x₂ [MOD Binary.residueDepthModulus K]) :
    y₁ ≡ y₂
      [MOD Binary.residueDepthModulus (K + Word.oddSteps w)] :=
  endpointEquation_residueLift h₁.endpointEquation h₂.endpointEquation hx

/-- 1 odd step では 3進 residue depth がちょうど一段上がる。 -/
theorem oddStep_residueLift
    {K e x₁ x₂ y₁ y₂ : ℕ}
    (h₁ : OddStep e x₁ y₁)
    (h₂ : OddStep e x₂ y₂)
    (hx : x₁ ≡ x₂ [MOD Binary.residueDepthModulus K]) :
    y₁ ≡ y₂ [MOD Binary.residueDepthModulus (K + 1)] := by
  have hRun₁ : Runs [e] x₁ y₁ :=
    Runs.cons h₁ (Runs.nil y₁)
  have hRun₂ : Runs [e] x₂ y₂ :=
    Runs.cons h₂ (Runs.nil y₂)
  simpa [Word.oddSteps] using runs_residueLift hRun₁ hRun₂ hx

end Bridge
end Collatz3
