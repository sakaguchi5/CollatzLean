import CollatzLean.Collatz2.Canonical.EndpointFloorTailRankTrap
import CollatzLean.Collatz2.Geometry.ContractingPairDescent

/-!
# Collatz2 Canonical: current A -> best-upper exponent-pair reduction

Stage 9 bridge。

7b の unconditional tail-rank trap から出る wide-strip branch

  p < stripRank(w,r)

を pure exponent pair

  P = (p,H)

の `HasWideStrip` に移す。
すると Stage 9a により denominator `r<p` の strict contracting pair へ降下し、
Stage 9b により有限回の denominator descent の終点として `StripReduced` pair を得る。

ここでも endpoint FutureMinimum は使わない。
-/

namespace Collatz2
namespace OddOrbit
namespace CanonicalEndpointFloorContractingReturn

/-- current A の terminal exponent pair。 -/
def exponentPair
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O) :
    Word.ContractingExponentPair := {
  oddCount := Word.oddSteps D.word
  twoDepth := Word.twoSteps D.word
  oddCount_pos := by
    unfold Word.oddSteps
    exact List.length_pos_iff.mpr D.word_nonempty
  contracting :=
    (Word.contracting_iff_threePow_lt_twoPow).1 D.contracting
}

@[simp] theorem exponentPair_oddCount
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O) :
    D.exponentPair.oddCount = Word.oddSteps D.word := rfl

@[simp] theorem exponentPair_twoDepth
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O) :
    D.exponentPair.twoDepth = Word.twoSteps D.word := rfl

/-- pair stripRank は word stripRank と definitionally 同じ。 -/
theorem exponentPair_stripRank_eq
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O)
    (r : ℕ) :
    D.exponentPair.stripRank r = Word.stripRank D.word r := by
  rfl

namespace TailRankTrapData

/-- wide-strip branch を pure exponent pair の witness に変換する。 -/
theorem hasWideStrip_of_strip_branch
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (R : TailRankTrapData D)
    (hStrip :
      Word.oddSteps D.word <
        Word.stripRank D.word R.crossingLength) :
    D.exponentPair.HasWideStrip := by
  refine ⟨R.crossingLength, R.crossingLength_pos, ?_, ?_⟩
  · simpa using R.crossing_lt_whole
  · simpa [exponentPair_stripRank_eq] using hStrip

/--
9a bridge: wide strip なら current pair より denominator の小さい strict contracting pair がある。
-/
theorem exists_smaller_pair_of_strip_branch
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (R : TailRankTrapData D)
    (hStrip :
      Word.oddSteps D.word <
        Word.stripRank D.word R.crossingLength) :
    ∃ Q : Word.ContractingExponentPair,
      Q.oddCount < D.exponentPair.oddCount ∧
      Word.ContractingExponentPair.SlopeStrictBelow Q D.exponentPair := by
  have hWide : D.exponentPair.HasWideStrip :=
    R.hasWideStrip_of_strip_branch hStrip
  rcases hWide with ⟨r, hrPos, hrLt, hrWide⟩
  exact
    Word.ContractingExponentPair.exists_smaller_contractingPair_of_wide
      hrPos hrLt hrWide

/--
7b + 9a の current-A dichotomy。

* base rank が first rank 以下へ落ちる
* denominator の小さい strict contracting exponent pair が存在する
-/
theorem rankDrop_or_smallerContractingPair
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (R : TailRankTrapData D) :
    Word.chordRankInt D.word (R.crossingLength + 1) ≤
        Word.chordRankInt D.word 1 ∨
      ∃ Q : Word.ContractingExponentPair,
        Q.oddCount < D.exponentPair.oddCount ∧
        Word.ContractingExponentPair.SlopeStrictBelow Q D.exponentPair := by
  rcases R.crossing_rank_or_strip with hRank | hStrip
  · exact Or.inl hRank
  · exact Or.inr (R.exists_smaller_pair_of_strip_branch hStrip)

end TailRankTrapData

/--
9b: current A の terminal exponent pair には必ず finite-descent の終点 certificate がある。
-/
theorem exists_bestUpperCertificate
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O) :
    Nonempty (Word.ContractingExponentPair.BestUpperCertificate D.exponentPair) :=
  Word.ContractingExponentPair.exists_bestUpperCertificate D.exponentPair

/--
current A が実際に wide strip を持つなら、reduced descendant の denominator は strict に小さい。
-/
theorem exists_strict_bestUpperCertificate_of_wide
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O)
    (hWide : D.exponentPair.HasWideStrip) :
    ∃ C : Word.ContractingExponentPair.BestUpperCertificate D.exponentPair,
      C.pair.oddCount < D.exponentPair.oddCount :=
  Word.ContractingExponentPair.exists_bestUpperCertificate_strict_of_wide hWide

/-- 7b packet の strip branch から strict best-upper certificate まで一気に落とす。 -/
theorem exists_strict_bestUpperCertificate_of_tailStrip
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (R : TailRankTrapData D)
    (hStrip :
      Word.oddSteps D.word <
        Word.stripRank D.word R.crossingLength) :
    ∃ C : Word.ContractingExponentPair.BestUpperCertificate D.exponentPair,
      C.pair.oddCount < D.exponentPair.oddCount := by
  exact D.exists_strict_bestUpperCertificate_of_wide
    (R.hasWideStrip_of_strip_branch hStrip)

end CanonicalEndpointFloorContractingReturn
end OddOrbit
end Collatz2
