import CollatzLean.Collatz2.Canonical.EndpointFloorRecordDescent
import CollatzLean.Collatz2.Geometry.RankQuotient

/-!
# Collatz2: primitive + StripReduced -> exact Christoffel roof

`primitive + StripReduced` contracting exponent pair では、任意の proper denominator `r` に対し

  criticalHeight r = floor (H * r / p)

が exact に成立する。

current A へ specialize すると、proper cut の deterministic strip は `p` 未満になり、
既存

  rankQuotient = stripRank / p + extraDepth

の strip quotient が消えるため

  rankQuotient = extraDepth

まで exact に縮約する。
-/

namespace Collatz2
namespace Word
namespace ContractingExponentPair

/--
primitive + StripReduced pair では、irrational critical roof は
whole rational chord の floor と proper denominator 上で exact に一致する。

  criticalHeight r = (H * r) / p
-/
theorem criticalHeight_eq_chordFloor_of_primitive_reduced
    {P : ContractingExponentPair}
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    {r : ℕ}
    (hrPos : 0 < r)
    (hrLt : r < P.oddCount) :
    criticalHeight r =
      P.twoDepth * r / P.oddCount := by
  have hRange :=
    P.stripRank_pos_lt_of_primitive_reduced
      hPrimitive hReduced hrPos hrLt
  have hCrit :
      P.oddCount * criticalHeight r <
        P.twoDepth * r :=
    P.criticalHeight_below_chord hrPos
  have hDiffLt :
      P.twoDepth * r -
          P.oddCount * criticalHeight r <
        P.oddCount := by
    simpa [stripRank] using hRange.2
  have hUpperAdd :
      P.twoDepth * r <
        P.oddCount * criticalHeight r + P.oddCount := by
    omega
  have hUpper :
      P.twoDepth * r <
        (criticalHeight r + 1) * P.oddCount := by
    calc
      P.twoDepth * r
          < P.oddCount * criticalHeight r + P.oddCount :=
            hUpperAdd
      _ = (criticalHeight r + 1) * P.oddCount := by
            ring
  have hFloor :
      P.twoDepth * r / P.oddCount = criticalHeight r := by
    apply Nat.div_eq_of_lt_le
    · simpa [Nat.mul_comm] using Nat.le_of_lt hCrit
    · exact hUpper
  exact hFloor.symm

/--
primitive + StripReduced pair では proper strip が一周未満なので、
strip quotient は zero。
-/
theorem stripRank_div_oddCount_eq_zero_of_primitive_reduced
    {P : ContractingExponentPair}
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    {r : ℕ}
    (hrPos : 0 < r)
    (hrLt : r < P.oddCount) :
    P.stripRank r / P.oddCount = 0 := by
  have hRange :=
    P.stripRank_pos_lt_of_primitive_reduced
      hPrimitive hReduced hrPos hrLt
  exact Nat.div_eq_of_lt hRange.2

end ContractingExponentPair
end Word

namespace OddOrbit
namespace CanonicalEndpointFloorContractingReturn

/--
current A specialization:

primitive + StripReduced current A では、全 proper cut `k` で

  criticalHeight k
    = (twoSteps word * k) / oddSteps word

が exact に成り立つ。
-/
theorem criticalHeight_eq_chordFloor_of_primitiveReduced
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O)
    (hPrimitive : D.exponentPair.IsPrimitive)
    (hReduced : D.exponentPair.StripReduced)
    {k : ℕ}
    (hkPos : 0 < k)
    (hkLt : k < Word.oddSteps D.word) :
    Word.criticalHeight k =
      Word.twoSteps D.word * k / Word.oddSteps D.word := by
  have h :=
    D.exponentPair.criticalHeight_eq_chordFloor_of_primitive_reduced
      hPrimitive hReduced hkPos (by simpa using hkLt)
  simpa using h

/--
current A specialization:

primitive + StripReduced では proper deterministic strip は whole denominator 未満。
-/
theorem stripRank_lt_oddSteps_of_primitiveReduced
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O)
    (hPrimitive : D.exponentPair.IsPrimitive)
    (hReduced : D.exponentPair.StripReduced)
    {k : ℕ}
    (hkPos : 0 < k)
    (hkLt : k < Word.oddSteps D.word) :
    Word.stripRank D.word k < Word.oddSteps D.word := by
  have hRange :=
    D.exponentPair.stripRank_pos_lt_of_primitive_reduced
      hPrimitive hReduced hkPos (by simpa using hkLt)
  have hPair : D.exponentPair.stripRank k < D.exponentPair.oddCount :=
    hRange.2
  rw [exponentPair_stripRank_eq D k] at hPair
  simpa using hPair

/--
current A specialization:

primitive + StripReduced では proper cut の strip wrap が消え、

  rankQuotient k = extraDepth k

となる。したがって residue-indexed Ferrers column height は
critical roof から actual prefix path が沈んだ depth そのものになる。
-/
theorem rankQuotient_eq_extraDepth_of_primitiveReduced
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O)
    (hPrimitive : D.exponentPair.IsPrimitive)
    (hReduced : D.exponentPair.StripReduced)
    {k : ℕ}
    (hkPos : 0 < k)
    (hkLt : k < Word.oddSteps D.word) :
    Word.rankQuotient D.word k =
      Word.extraDepth D.word k := by
  have hF : Word.FirstCrossing D.word :=
    D.wordFirstCrossing
  have hStripLt :
      Word.stripRank D.word k < Word.oddSteps D.word :=
    D.stripRank_lt_oddSteps_of_primitiveReduced
      hPrimitive hReduced hkPos hkLt
  have hEq :=
    hF.rankQuotient_eq_stripDiv_add_extraDepth hkPos hkLt
  rw [Nat.div_eq_of_lt hStripLt, zero_add] at hEq
  exact hEq

end CanonicalEndpointFloorContractingReturn
end OddOrbit
end Collatz2
