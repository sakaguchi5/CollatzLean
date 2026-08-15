import CollatzLean.Collatz2.Canonical.EndpointFloorFerrersInverse
import CollatzLean.Collatz2.Geometry.RankUnitGeometricInverse
import CollatzLean.Collatz2.Geometry.ResidueIndexedFerrersCellSum

/-!
# Collatz2 Canonical: primitive current A の Ferrers closed form

既存の Ferrers inverse equation

  (1-v) * (C + 12*n) = 1

を rank unit `u` と primitive geometric baseline に戻す。
`u*v=1`, `u^p=2` なので exact に

  (u-1) * (C + 12*n - 1) = 1,
  C + 12*n = 2*baselineResidueSum,
  C + 12*n - 1 = 1 + u + ... + u^(p-1)

を同じ rank unit packet で保持する。

さらに `C` 自身を residue-indexed quotient profile

  q_r = rankQuotient(residueCut(r))

の cell generating sumへ置換し、cut/path index を closed form から消す。
-/

namespace Collatz2
namespace OddOrbit
namespace CanonicalEndpointFloorContractingReturn

/-- closed-form 側で使う current A の FirstCrossing。 -/
theorem ferrersClosedFirstCrossing
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O) :
    Word.FirstCrossing D.word := by
  simpa [word] using D.firstCrossing

/-- primitive exponent pair を closed-form 側の word coprime slope へ読む。 -/
theorem ferrersClosedWordCoprime
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (hPrimitive : D.exponentPair.IsPrimitive) :
    Nat.Coprime (Word.twoSteps D.word) (Word.oddSteps D.word) := by
  simpa [Word.ContractingExponentPair.IsPrimitive,
    exponentPair_oddCount, exponentPair_twoDepth] using hPrimitive

/--
同じ rank unit `R` 上で inverse / direct inverse / fixed baseline closed form を束ねる。
-/
structure FerrersClosedFormData
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O) where
  R : Word.RankUnitData D.word
  inverseEquation :
    (1 - Word.inverseUnitValue R) *
        (Word.ferrersCellSum R +
          ((12 * D.toCenterShadowData.n : ℕ) :
            ZMod (Word.terminalGap D.word))) = 1
  directInverseEquation :
    (Word.directUnitValue R - 1) *
        (Word.ferrersCellSum R +
          ((12 * D.toCenterShadowData.n : ℕ) :
            ZMod (Word.terminalGap D.word)) - 1) = 1
  doubleBaselineEquation :
    Word.ferrersCellSum R +
        ((12 * D.toCenterShadowData.n : ℕ) :
          ZMod (Word.terminalGap D.word)) =
      2 * Word.baselineResidueSum R
  directGeometricEquation :
    Word.ferrersCellSum R +
        ((12 * D.toCenterShadowData.n : ℕ) :
          ZMod (Word.terminalGap D.word)) - 1 =
      Word.directGeometricResidueSum R

/--
primitive current A は Ferrers closed-form packet を持つ。
-/
theorem exists_ferrersClosedFormData
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O)
    (hPrimitive : D.exponentPair.IsPrimitive) :
    Nonempty (FerrersClosedFormData D) := by
  obtain ⟨R, hInvRaw⟩ :=
    D.exists_rankUnit_ferrersInverseEquation hPrimitive
  let v : ZMod (Word.terminalGap D.word) := Word.inverseUnitValue R
  let u : ZMod (Word.terminalGap D.word) := Word.directUnitValue R
  let C : ZMod (Word.terminalGap D.word) := Word.ferrersCellSum R
  let B : ZMod (Word.terminalGap D.word) := Word.baselineResidueSum R
  let z12 : ZMod (Word.terminalGap D.word) :=
    ((12 * D.toCenterShadowData.n : ℕ) :
      ZMod (Word.terminalGap D.word))
  let X : ZMod (Word.terminalGap D.word) := C + z12
  have hInv : (1 - v) * X = 1 := by
    simpa [v, X, C, z12] using hInvRaw
  have hF := D.ferrersClosedFirstCrossing
  have hCop := D.ferrersClosedWordCoprime hPrimitive
  have hBaselineInvRaw :=
    R.one_sub_inverseUnitValue_mul_two_mul_baselineResidueSum_eq_one
      hF hCop
  have hBaselineInv : (1 - v) * (2 * B) = 1 := by
    simpa [v, B] using hBaselineInvRaw
  have huvRaw := R.directUnitValue_mul_inverseUnitValue_eq_one
  have huv : u * v = 1 := by
    simpa [u, v] using huvRaw
  have hUX : u * X - X = u := by
    calc
      u * X - X = (u - 1) * X := by ring
      _ = (u - u * v) * X := by rw [huv]
      _ = u * ((1 - v) * X) := by ring
      _ = u * 1 := by rw [hInv]
      _ = u := by ring
  have hDirectInv : (u - 1) * (X - 1) = 1 := by
    calc
      (u - 1) * (X - 1)
          = (u * X - X) - u + 1 := by ring
      _ = u - u + 1 := by rw [hUX]
      _ = 1 := by ring
  have hDouble : X = 2 * B := by
    calc
      X = X * 1 := by ring
      _ = X * ((1 - v) * (2 * B)) := by rw [hBaselineInv]
      _ = ((1 - v) * X) * (2 * B) := by ring
      _ = 1 * (2 * B) := by rw [hInv]
      _ = 2 * B := by ring
  have hGeoInvRaw :=
    R.directUnitValue_sub_one_mul_directGeometricResidueSum_eq_one
  have hGeoInv :
      (u - 1) * Word.directGeometricResidueSum R = 1 := by
    simpa [u] using hGeoInvRaw
  have hDirectGeo :
      X - 1 = Word.directGeometricResidueSum R := by
    calc
      X - 1 = (X - 1) * 1 := by ring
      _ = (X - 1) *
            ((u - 1) * Word.directGeometricResidueSum R) := by
              rw [hGeoInv]
      _ = ((u - 1) * (X - 1)) *
            Word.directGeometricResidueSum R := by ring
      _ = 1 * Word.directGeometricResidueSum R := by rw [hDirectInv]
      _ = Word.directGeometricResidueSum R := by ring
  exact Nonempty.intro {
    R := R
    inverseEquation := by
      simpa [v, X, C, z12] using hInv
    directInverseEquation := by
      simpa [u, X, C, z12] using hDirectInv
    doubleBaselineEquation := by
      simpa [X, C, z12, B] using hDouble
    directGeometricEquation := by
      simpa [X, C, z12] using hDirectGeo
  }

namespace FerrersClosedFormData

/-- packet の baseline を固定 geometric residue sum へ置換する。 -/
theorem doubleGeometricBaselineEquation
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (F : FerrersClosedFormData D)
    (hPrimitive : D.exponentPair.IsPrimitive) :
    Word.ferrersCellSum F.R +
        ((12 * D.toCenterShadowData.n : ℕ) :
          ZMod (Word.terminalGap D.word)) =
      2 * Word.geometricResidueSum F.R := by
  have hF := D.ferrersClosedFirstCrossing
  have hCop := D.ferrersClosedWordCoprime hPrimitive
  calc
    Word.ferrersCellSum F.R +
        ((12 * D.toCenterShadowData.n : ℕ) :
          ZMod (Word.terminalGap D.word))
        = 2 * Word.baselineResidueSum F.R := F.doubleBaselineEquation
    _ = 2 * Word.geometricResidueSum F.R := by
      rw [F.R.baselineResidueSum_eq_geometricResidueSum hF hCop]

/-- `C` を residue-indexed quotient profile の column sumへ完全に置換する。 -/
theorem residueIndexedDoubleBaselineEquation
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (F : FerrersClosedFormData D)
    (hPrimitive : D.exponentPair.IsPrimitive) :
    Word.residueIndexedFerrersCellSum
          F.R D.ferrersClosedFirstCrossing
          (D.ferrersClosedWordCoprime hPrimitive) +
        ((12 * D.toCenterShadowData.n : ℕ) :
          ZMod (Word.terminalGap D.word)) =
      2 * Word.geometricResidueSum F.R := by
  have hF := D.ferrersClosedFirstCrossing
  have hCop := D.ferrersClosedWordCoprime hPrimitive
  have hCells :=
    F.R.ferrersCellSum_eq_residueIndexedFerrersCellSum hF hCop
  calc
    Word.residueIndexedFerrersCellSum F.R hF hCop +
        ((12 * D.toCenterShadowData.n : ℕ) :
          ZMod (Word.terminalGap D.word))
        = Word.ferrersCellSum F.R +
            ((12 * D.toCenterShadowData.n : ℕ) :
              ZMod (Word.terminalGap D.word)) := by rw [← hCells]
    _ = 2 * Word.geometricResidueSum F.R :=
      F.doubleGeometricBaselineEquation hPrimitive

/--
各 cell を `v^(r+p*j)` とした generating sum による path/cut-free closed form。
-/
theorem residueIndexedPowerCellDoubleBaselineEquation
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (F : FerrersClosedFormData D)
    (hPrimitive : D.exponentPair.IsPrimitive) :
    Word.residueIndexedFerrersPowerCellSum
          F.R D.ferrersClosedFirstCrossing
          (D.ferrersClosedWordCoprime hPrimitive) +
        ((12 * D.toCenterShadowData.n : ℕ) :
          ZMod (Word.terminalGap D.word)) =
      2 * Word.geometricResidueSum F.R := by
  have hF := D.ferrersClosedFirstCrossing
  have hCop := D.ferrersClosedWordCoprime hPrimitive
  have hCells :=
    F.R.ferrersCellSum_eq_residueIndexedFerrersPowerCellSum hF hCop
  calc
    Word.residueIndexedFerrersPowerCellSum F.R hF hCop +
        ((12 * D.toCenterShadowData.n : ℕ) :
          ZMod (Word.terminalGap D.word))
        = Word.ferrersCellSum F.R +
            ((12 * D.toCenterShadowData.n : ℕ) :
              ZMod (Word.terminalGap D.word)) := by rw [← hCells]
    _ = 2 * Word.geometricResidueSum F.R :=
      F.doubleGeometricBaselineEquation hPrimitive

/--
path/cut-free cell generating sum と direct `u` geometric sum の closed form。
-/
theorem residueIndexedPowerCellDirectGeometricEquation
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (F : FerrersClosedFormData D)
    (hPrimitive : D.exponentPair.IsPrimitive) :
    Word.residueIndexedFerrersPowerCellSum
          F.R D.ferrersClosedFirstCrossing
          (D.ferrersClosedWordCoprime hPrimitive) +
        ((12 * D.toCenterShadowData.n : ℕ) :
          ZMod (Word.terminalGap D.word)) - 1 =
      Word.directGeometricResidueSum F.R := by
  have hF := D.ferrersClosedFirstCrossing
  have hCop := D.ferrersClosedWordCoprime hPrimitive
  have hCells :=
    F.R.ferrersCellSum_eq_residueIndexedFerrersPowerCellSum hF hCop
  calc
    Word.residueIndexedFerrersPowerCellSum F.R hF hCop +
          ((12 * D.toCenterShadowData.n : ℕ) :
            ZMod (Word.terminalGap D.word)) - 1
        = Word.ferrersCellSum F.R +
            ((12 * D.toCenterShadowData.n : ℕ) :
              ZMod (Word.terminalGap D.word)) - 1 := by rw [← hCells]
    _ = Word.directGeometricResidueSum F.R := F.directGeometricEquation

end FerrersClosedFormData

end CanonicalEndpointFloorContractingReturn
end OddOrbit
end Collatz2
