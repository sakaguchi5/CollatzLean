import CollatzLean.Collatz2.Canonical.EndpointFloorRankFerrers
import CollatzLean.Collatz2.Geometry.ResidueIndexedFerrers

/-!
# Collatz2 Canonical: primitive current A の Ferrers inverse equation

primitive current A では既に

  W = baseline + (half-1)*C = 6*n

がある。さらに primitive residue permutation から

  (v-1)*baseline = half-1

であり、rank unit から

  2*half = 1.

これらを消去すると exact に

  (1-v) * (C + 12*n) = 1      (mod G)

を得る。
-/

namespace Collatz2
namespace OddOrbit
namespace CanonicalEndpointFloorContractingReturn

/-- primitive current A 用 FirstCrossing bridge。 -/
private theorem inverseWordFirstCrossing
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O) :
    Word.FirstCrossing D.word := by
  simpa [word] using D.firstCrossing

/-- primitive exponent pair を word coprime slope へ読む。 -/
private theorem inverseExponentPrimitive_word_coprime
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (hPrimitive : D.exponentPair.IsPrimitive) :
    Nat.Coprime (Word.twoSteps D.word) (Word.oddSteps D.word) := by
  simpa [Word.ContractingExponentPair.IsPrimitive,
    exponentPair_oddCount, exponentPair_twoDepth] using hPrimitive

/--
4. primitive current A の weighted Small-Residue equation を一個の inverse equation へ圧縮する。
-/
theorem exists_rankUnit_ferrersInverseEquation
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O)
    (hPrimitive : D.exponentPair.IsPrimitive) :
    ∃ R : Word.RankUnitData D.word,
      (1 - Word.inverseUnitValue R) *
          (Word.ferrersCellSum R +
            ((12 * D.toCenterShadowData.n : ℕ) :
              ZMod (Word.terminalGap D.word))) = 1 := by
  obtain ⟨R, hW⟩ :=
    D.exists_rankUnit_weightedRankSum_eq_six_mul_n hPrimitive
  have hF := D.inverseWordFirstCrossing
  have hCop := D.inverseExponentPrimitive_word_coprime hPrimitive
  have hCells :=
    R.weightedRankSum_eq_baseline_add_halfSubOne_mul_ferrersCellSum
  have hBase :=
    R.inverseUnitValue_sub_one_mul_baselineResidueSum_eq_half_sub_one
      hF hCop
  have hHalfRaw := R.halfUnitValue_mul_two_eq_one
  let v : ZMod (Word.terminalGap D.word) := Word.inverseUnitValue R
  let h : ZMod (Word.terminalGap D.word) := Word.halfUnitValue R
  let B : ZMod (Word.terminalGap D.word) := Word.baselineResidueSum R
  let C : ZMod (Word.terminalGap D.word) := Word.ferrersCellSum R
  let z : ZMod (Word.terminalGap D.word) :=
    ((D.toCenterShadowData.n : ℕ) : ZMod (Word.terminalGap D.word))
  have hWeighted : B + (h - 1) * C = 6 * z := by
    calc
      B + (h - 1) * C = Word.weightedRankSum R := by
        simpa [B, h, C] using hCells.symm
      _ = ((6 * D.toCenterShadowData.n : ℕ) :
            ZMod (Word.terminalGap D.word)) := hW
      _ = 6 * z := by
        dsimp [z]
        push_cast
        rfl
  have hBase' : (v - 1) * B = h - 1 := by
    simpa [v, B, h] using hBase
  have hHalf : h * 2 = 1 := by
    simpa [h] using hHalfRaw
  have hHalfSub : 2 * (h - 1) = -1 := by
    calc
      2 * (h - 1) = h * 2 - 2 := by ring
      _ = 1 - 2 := by rw [hHalf]
      _ = -1 := by ring
  have hCore :
      -1 - (v - 1) * C = 12 * z * (v - 1) := by
    calc
      -1 - (v - 1) * C
          = 2 * (h - 1) +
              2 * (h - 1) * (v - 1) * C := by
                rw [hHalfSub]
                ring
      _ = 2 * (v - 1) * B +
            2 * (v - 1) * (h - 1) * C := by
              rw [mul_assoc 2 (v - 1) B]
              rw [hBase']
              ring
      _ = 2 * (v - 1) * (B + (h - 1) * C) := by ring
      _ = 2 * (v - 1) * (6 * z) := by rw [hWeighted]
      _ = 12 * z * (v - 1) := by ring
  refine ⟨R, ?_⟩
  change
    (1 - v) *
        (C + ((12 * D.toCenterShadowData.n : ℕ) :
          ZMod (Word.terminalGap D.word))) = 1
  have hTwelve :
      (((12 * D.toCenterShadowData.n : ℕ) :
        ZMod (Word.terminalGap D.word))) = 12 * z := by
    dsimp [z]
    push_cast
    rfl
  rw [hTwelve]
  calc
    (1 - v) * (C + 12 * z)
        = -(v - 1) * C - 12 * z * (v - 1) := by ring
    _ = 1 := by
      rw [← hCore]
      ring

end CanonicalEndpointFloorContractingReturn
end OddOrbit
end Collatz2
