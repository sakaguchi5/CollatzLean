import CollatzLean.Collatz2.Canonical.EndpointFloorCyclicGeometry
import CollatzLean.Collatz2.Canonical.EndpointFloorBestUpperReduction
import CollatzLean.Collatz2.Geometry.WeightedRankSum
import CollatzLean.Collatz2.Geometry.PrimitiveBestUpper

/-!
# Collatz2 Canonical: current A の Small-Residue weighted-rank congruence

`CenterShadowData` には current A から exact に

  B = G*S + 2^(H+1)*n

があり、mod `G=2^H-3^p` では

  B = 2*3^p*n.

一方 `WeightedRankSum` では primitive exponent pair に対し

  3*B = 3^p * W,
  W = sum_{k=0}^{p-1} u^(-d_k).

`3^p` は rank unit の unit value なので cancel でき、exact に

  W = 6*n        (mod G)

を得る。

これで Small-Residue Principle の前段だった
「B 全体を weighted-rank sum にまとめる」部分を閉じる。
-/

namespace Collatz2
namespace OddOrbit
namespace CanonicalEndpointFloorContractingReturn

/-- current A の FirstCrossing を rank-unit 側へ渡す。 -/
private theorem rankWordFirstCrossing
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O) :
    Word.FirstCrossing D.word := by
  simpa [word] using D.firstCrossing

/-- exponent primitive 性を word の `gcd(H,p)=1` に読む。 -/
private theorem exponentPrimitive_word_coprime
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (hPrimitive : D.exponentPair.IsPrimitive) :
    Nat.Coprime (Word.twoSteps D.word) (Word.oddSteps D.word) := by
  simpa [Word.ContractingExponentPair.IsPrimitive,
    exponentPair_oddCount, exponentPair_twoDepth] using hPrimitive

namespace CenterShadowData

/--
current A の small-residue congruence を rank-unit modulus `terminalGap` で読む。
-/
theorem translate_cast_eq_smallResidue_terminalGap
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (L : CenterShadowData D) :
    ((Word.affineConst D.word : ℕ) : ZMod (Word.terminalGap D.word)) =
      ((2 * 3 ^ Word.oddSteps D.word * L.n : ℕ) :
        ZMod (Word.terminalGap D.word)) := by
  have hGap :
      Word.terminalGap D.word =
        (AffineTransfer.ofWord D.word).centerGap := by
    unfold Word.terminalGap AffineTransfer.centerGap
    simp only [
      AffineTransfer.ofWord_twoCoeff,
      AffineTransfer.ofWord_oddCoeff
    ]
  rw [hGap]
  exact L.translate_cast_eq_smallResidue

/--
rank unit を一つ固定した current A の weighted-rank identity。

  weightedRankSum = 6*n   (mod G).
-/
theorem weightedRankSum_eq_six_mul_n
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (L : CenterShadowData D)
    (R : Word.RankUnitData D.word) :
    Word.weightedRankSum R =
      ((6 * L.n : ℕ) : ZMod (Word.terminalGap D.word)) := by
  have hF := D.rankWordFirstCrossing
  have hWeighted :=
    R.three_mul_affineConst_cast_eq_threePow_mul_weightedRankSum hF
  have hSmall := L.translate_cast_eq_smallResidue_terminalGap
  have hSmall3 :=
    congrArg
      (fun z : ZMod (Word.terminalGap D.word) =>
        ((3 : ℕ) : ZMod (Word.terminalGap D.word)) * z)
      hSmall
  have hRight :
      (((3 * Word.affineConst D.word : ℕ) :
          ZMod (Word.terminalGap D.word))) =
        ((3 ^ Word.oddSteps D.word : ℕ) :
            ZMod (Word.terminalGap D.word)) *
          (((6 * L.n : ℕ) : ZMod (Word.terminalGap D.word))) := by
    calc
      (((3 * Word.affineConst D.word : ℕ) :
          ZMod (Word.terminalGap D.word)))
          = ((3 : ℕ) : ZMod (Word.terminalGap D.word)) *
              ((Word.affineConst D.word : ℕ) :
                ZMod (Word.terminalGap D.word)) := by
                  push_cast
                  rfl
      _ = ((3 : ℕ) : ZMod (Word.terminalGap D.word)) *
            ((2 * 3 ^ Word.oddSteps D.word * L.n : ℕ) :
              ZMod (Word.terminalGap D.word)) := hSmall3
      _ = ((3 ^ Word.oddSteps D.word : ℕ) :
              ZMod (Word.terminalGap D.word)) *
            (((6 * L.n : ℕ) : ZMod (Word.terminalGap D.word))) := by
              push_cast
              ring
  have hCancel :
      ((3 ^ Word.oddSteps D.word : ℕ) :
          ZMod (Word.terminalGap D.word)) * Word.weightedRankSum R =
        ((3 ^ Word.oddSteps D.word : ℕ) :
          ZMod (Word.terminalGap D.word)) *
            (((6 * L.n : ℕ) : ZMod (Word.terminalGap D.word))) := by
    calc
      ((3 ^ Word.oddSteps D.word : ℕ) :
          ZMod (Word.terminalGap D.word)) * Word.weightedRankSum R
          = (((3 * Word.affineConst D.word : ℕ) :
              ZMod (Word.terminalGap D.word))) := hWeighted.symm
      _ = ((3 ^ Word.oddSteps D.word : ℕ) :
              ZMod (Word.terminalGap D.word)) *
            (((6 * L.n : ℕ) : ZMod (Word.terminalGap D.word))) := hRight
  exact R.cancel_threePow hCancel

end CenterShadowData

/--
primitive current A では rank unit は追加仮定ではないので、
small-residue weighted-rank congruence を満たす unit packet が実在する。
-/
theorem exists_rankUnit_weightedRankSum_eq_six_mul_n
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O)
    (hPrimitive : D.exponentPair.IsPrimitive) :
    ∃ R : Word.RankUnitData D.word,
      Word.weightedRankSum R =
        ((6 * D.toCenterShadowData.n : ℕ) :
          ZMod (Word.terminalGap D.word)) := by
  have hCop := D.exponentPrimitive_word_coprime hPrimitive
  obtain ⟨R⟩ :=
    D.rankWordFirstCrossing.exists_rankUnitData_of_coprime hCop
  refine ⟨R, ?_⟩
  exact D.toCenterShadowData.weightedRankSum_eq_six_mul_n R

end CanonicalEndpointFloorContractingReturn
end OddOrbit
end Collatz2
