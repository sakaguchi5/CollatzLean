import CollatzLean.Collatz2.Canonical.EndpointFloorWeightedRank
import CollatzLean.Collatz2.Geometry.WeightedRankFerrers

/-!
# Collatz2 Canonical: current A の original-word Ferrers bridge

nonreduced exponent pair を descendant `Q` の modulus へ移さず、original current A の
rank quotient に戻す。

wide strip

  p < stripRank(k)

は original word 上で

  0 < rankQuotient(k)

を強制する。一方 primitive current A では proper rank residues は `1,...,p-1` を
一度ずつ取り、weighted-rank identity

  W = 6*n

はそのまま

  W = 1 + proper permutation-weighted half-depth sum

および

  W = baseline + (half-1)*FerrersCellSum

へ exact に書き換えられる。
-/

namespace Collatz2
namespace OddOrbit
namespace CanonicalEndpointFloorContractingReturn

/-- current A の FirstCrossing を再び word 側へ読む。 -/
private theorem ferrersWordFirstCrossing
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O) :
    Word.FirstCrossing D.word := by
  simpa [word] using D.firstCrossing

/-- exponent primitive 性を word の coprime slope に読む。 -/
private theorem ferrersExponentPrimitive_word_coprime
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (hPrimitive : D.exponentPair.IsPrimitive) :
    Nat.Coprime (Word.twoSteps D.word) (Word.oddSteps D.word) := by
  simpa [Word.ContractingExponentPair.IsPrimitive,
    exponentPair_oddCount, exponentPair_twoDepth] using hPrimitive

/--
nonreduced / wide-strip branch は original word の rank quotient に正の witness を残す。
-/
theorem exists_positive_rankQuotient_of_wide
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O)
    (hWide : D.exponentPair.HasWideStrip) :
    ∃ k : ℕ,
      0 < k ∧
      k < Word.oddSteps D.word ∧
      0 < Word.rankQuotient D.word k := by
  rcases hWide with ⟨k, hkPos, hkLt, hkWide⟩
  refine ⟨k, hkPos, by simpa using hkLt, ?_⟩
  have hF := D.ferrersWordFirstCrossing
  apply hF.rankQuotient_pos_of_stripRank_gt_oddSteps hkPos (by simpa using hkLt)
  simpa [exponentPair_stripRank_eq] using hkWide

/-- primitive current A では proper rank residues は `1,...,p-1` の permutation。 -/
theorem exists_unique_cut_of_rankResidue_of_primitive
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O)
    (hPrimitive : D.exponentPair.IsPrimitive)
    {q : ℕ}
    (hqPos : 0 < q)
    (hqLt : q < Word.oddSteps D.word) :
    ∃! k : ℕ,
      0 < k ∧
      k < Word.oddSteps D.word ∧
      Word.rankResidue D.word k = q := by
  have hF := D.ferrersWordFirstCrossing
  have hCop := D.ferrersExponentPrimitive_word_coprime hPrimitive
  exact hF.exists_unique_proper_cut_of_rankResidue hCop hqPos hqLt

/--
primitive current A の `W=6*n` を Ferrers residue/quotient form へ移す rank unit が存在する。
-/
theorem exists_rankUnit_ferrersWeightedSum_eq_six_mul_n
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O)
    (hPrimitive : D.exponentPair.IsPrimitive) :
    ∃ R : Word.RankUnitData D.word,
      Word.ferrersWeightedSum R =
        ((6 * D.toCenterShadowData.n : ℕ) :
          ZMod (Word.terminalGap D.word)) := by
  obtain ⟨R, hW⟩ :=
    D.exists_rankUnit_weightedRankSum_eq_six_mul_n hPrimitive
  refine ⟨R, ?_⟩
  calc
    Word.ferrersWeightedSum R = Word.weightedRankSum R :=
      R.weightedRankSum_eq_ferrersWeightedSum.symm
    _ = ((6 * D.toCenterShadowData.n : ℕ) :
          ZMod (Word.terminalGap D.word)) := hW

/--
primitive current A では exact に

  1 + proper permutation-weighted half-depth sum = 6*n.
-/
theorem exists_rankUnit_one_add_properPermutationWeightedHalfDepthSum_eq_six_mul_n
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O)
    (hPrimitive : D.exponentPair.IsPrimitive) :
    ∃ R : Word.RankUnitData D.word,
      1 + Word.properPermutationWeightedHalfDepthSum R =
        ((6 * D.toCenterShadowData.n : ℕ) :
          ZMod (Word.terminalGap D.word)) := by
  obtain ⟨R, hW⟩ :=
    D.exists_rankUnit_weightedRankSum_eq_six_mul_n hPrimitive
  have hF := D.ferrersWordFirstCrossing
  have hSplit :=
    R.weightedRankSum_eq_one_add_properPermutationWeightedHalfDepthSum hF
  refine ⟨R, ?_⟩
  calc
    1 + Word.properPermutationWeightedHalfDepthSum R
        = Word.weightedRankSum R := hSplit.symm
    _ = ((6 * D.toCenterShadowData.n : ℕ) :
          ZMod (Word.terminalGap D.word)) := hW

/--
primitive current A の weighted residue を baseline + Ferrers cells へ exact に書き換える。
-/
theorem exists_rankUnit_baseline_add_cells_eq_six_mul_n
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O)
    (hPrimitive : D.exponentPair.IsPrimitive) :
    ∃ R : Word.RankUnitData D.word,
      Word.baselineResidueSum R +
          (Word.halfUnitValue R - 1) * Word.ferrersCellSum R =
        ((6 * D.toCenterShadowData.n : ℕ) :
          ZMod (Word.terminalGap D.word)) := by
  obtain ⟨R, hW⟩ :=
    D.exists_rankUnit_weightedRankSum_eq_six_mul_n hPrimitive
  have hCells :=
    R.weightedRankSum_eq_baseline_add_halfSubOne_mul_ferrersCellSum
  refine ⟨R, ?_⟩
  calc
    Word.baselineResidueSum R +
          (Word.halfUnitValue R - 1) * Word.ferrersCellSum R
        = Word.weightedRankSum R := hCells.symm
    _ = ((6 * D.toCenterShadowData.n : ℕ) :
          ZMod (Word.terminalGap D.word)) := hW

end CanonicalEndpointFloorContractingReturn
end OddOrbit
end Collatz2
