import CollatzLean.Collatz.AdjacentReturn.PositiveReturn.ReplayProfile

/-!
# bi-canonical cut corridor

positive first crossing の cut を左右から見る。
start が prefix modulus 未満、endpoint が suffix replay 一段分未満なら、
同じ cut boundary が prefix canonical end かつ suffix canonical start になる。
-/

namespace Collatz
namespace AdjacentReturn
namespace PositiveReturn
namespace FirstCrossingData

/-- cut `k` までの actual prefix word。 -/
def prefixWord
    {O : OddOrbit} {R : State O}
    (_F : FirstCrossingData R) (k : ℕ) : Collatz.Word :=
  O.segment R.startIndex k

/-- prefix の actual endpoint は cut boundary。 -/
theorem prefixEnd_eq_boundary
    {O : OddOrbit} {R : State O}
    (F : FirstCrossingData R) (k : ℕ) :
    O.value (R.startIndex + k) = boundaryValue F k := by
  rfl

end FirstCrossingData

/-- 一つの cut が左右同時に canonical であること。 -/
structure BiCanonicalCutData
    {O : OddOrbit} {R : State O}
    (F : FirstCrossingData R) (k : ℕ) : Prop where
  cut_pos : 0 < k
  cut_lt : k < F.length
  prefixStart_eq :
    R.startValue = Word.canonicalStart (FirstCrossingData.prefixWord F k)
  prefixEnd_eq :
    FirstCrossingData.boundaryValue F k = Word.canonicalEnd (FirstCrossingData.prefixWord F k)
  suffixStart_eq :
    FirstCrossingData.boundaryValue F k = Word.canonicalStart (FirstCrossingData.suffixWord F k)
  suffixEnd_eq :
    F.endpointValue = Word.canonicalEnd (FirstCrossingData.suffixWord F k)

namespace CanonicalChain

/-- start が prefix modulus 未満なら prefix は同じ start から canonical。 -/
theorem prefix_canonical_of_start_lt_modulus
    {O : OddOrbit} (C : CanonicalChain O) (n k : ℕ)
    (hsmall :
      (C.state n).startValue <
        Word.residueModulus
          (FirstCrossingData.prefixWord
            (C.firstCrossing n) k)) :
    (C.state n).startValue =
        Word.canonicalStart
          (FirstCrossingData.prefixWord
            (C.firstCrossing n) k) ∧
      FirstCrossingData.boundaryValue
          (C.firstCrossing n) k =
        Word.canonicalEnd
          (FirstCrossingData.prefixWord
            (C.firstCrossing n) k) := by
  let F := C.firstCrossing n
  let U := FirstCrossingData.prefixWord F k
  have hreal :
      Word.Realizes U
        (C.state n).startValue
        (FirstCrossingData.boundaryValue F k) := by
    simpa [U, FirstCrossingData.prefixWord,
      FirstCrossingData.boundaryValue, State.startValue, F] using
      O.realizesSegment (C.state n).startIndex k
  have hendOdd : Odd (FirstCrossingData.boundaryValue F k) := by
    simpa [FirstCrossingData.boundaryValue, F] using
      O.value_odd ((C.state n).startIndex + k)
  have hstart :
      (C.state n).startValue = Word.canonicalStart U :=
    hreal.eq_canonicalStart_of_lt_modulus hendOdd (by simpa [U, F] using hsmall)
  let Q :
      Word.ReplayCoordinate
        U (C.state n).startValue (FirstCrossingData.boundaryValue F k) :=
    Word.ReplayCoordinate.ofRealization hreal hendOdd
  have hq : Q.quotient = 0 :=
    Q.quotient_eq_zero_of_start_eq_canonical hstart
  have hfinish := Q.finish_eq
  rw [hq] at hfinish
  constructor
  · simpa [U] using hstart
  · simpa [Q, U] using hfinish

/--
左右の size 条件が同時に成立する cut は bi-canonical。
これが positive-return saturation を受ける有限 cut の基本 package。
-/
theorem biCanonicalCut_of_bounds
    {O : OddOrbit} (C : CanonicalChain O) (n k : ℕ)
    (hkPos : 0 < k)
    (hkLt : k < (C.firstCrossing n).length)
    (hprefix :
      (C.state n).startValue <
        Word.residueModulus
          (FirstCrossingData.prefixWord
            (C.firstCrossing n) k))
    (hsuffix :
      (C.firstCrossing n).endpointValue <
        2 * 3 ^
          (FirstCrossingData.suffixWord
            (C.firstCrossing n) k).oddSteps) :
    BiCanonicalCutData (C.firstCrossing n) k := by
  have hpre :=
    C.prefix_canonical_of_start_lt_modulus
      n k hprefix
  have hsuf :=
    C.suffix_canonical_of_endpoint_lt
      n k (Nat.le_of_lt hkLt) hsuffix
  exact {
    cut_pos := hkPos
    cut_lt := hkLt
    prefixStart_eq := hpre.1
    prefixEnd_eq := hpre.2
    suffixStart_eq := hsuf.1
    suffixEnd_eq := hsuf.2
  }

/-- bi-canonical cut では左右の canonical representatives が同じ actual boundary で接続する。 -/
theorem biCanonical_boundary_identity
    {O : OddOrbit} {C : CanonicalChain O}
    {n k : ℕ}
    (D : BiCanonicalCutData (C.firstCrossing n) k) :
    Word.canonicalEnd
        (FirstCrossingData.prefixWord
          (C.firstCrossing n) k) =
      Word.canonicalStart
        (FirstCrossingData.suffixWord
          (C.firstCrossing n) k) := by
  rw [← D.prefixEnd_eq, D.suffixStart_eq]

/-- bi-canonical cut の suffix は元 first crossing と同じ canonical endpoint を持つ。 -/
theorem biCanonical_suffix_same_endpoint
    {O : OddOrbit} {C : CanonicalChain O}
    {n k : ℕ}
    (D : BiCanonicalCutData (C.firstCrossing n) k) :
    Word.canonicalEnd
        (FirstCrossingData.suffixWord
          (C.firstCrossing n) k) =
      Word.canonicalEnd (C.word n) := by
  rw [← D.suffixEnd_eq, ← C.endpoint_eq_canonicalEnd n]

end CanonicalChain
end PositiveReturn
end AdjacentReturn
end Collatz
