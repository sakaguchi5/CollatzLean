import CollatzLean.Collatz2.Global.RightBranchEndpointFloorClosure
import CollatzLean.Collatz2.Canonical.ZeroCoreNestedCorridor
import CollatzLean.Collatz2.Orbit.FutureMinimumArithmetic

/-!
# Collatz2 Global: minimal adjacent canonical return

current A reduction で実際に使った「最短 positive / all-suffix-contracting candidate」
の provenance を捨てずに保持し、B1 の true zero-core と endpoint future-minimum を
同じ packet に載せる。

重要:

* `base` は既存 `CanonicalEndpointFloorContractingReturn`
* `source` は A で使った `PositiveFirstCrossingSource`
* `base` の start/length は `source.minimalPositiveCandidate` と一致
* `zeroCore` は B1 の `j=0` handoff
* `endFutureMinimum` は追加の orbit-order 情報

これにより current A theorem 自体は一切変更せず、必要な場合だけ強化 packet へ進める。

`endFutureMinimum + endpointFloor + positive` から start も future minimum となるため、
この packet の start/end 間には interior future minimum が存在しない。
-/

namespace Collatz2
namespace OddOrbit
namespace EndpointFloorReduction

/--
A の minimal candidate provenance と B1 zero-core、endpoint future-minimum を
同時に保持する thin strengthened packet。
-/
structure MinimalAdjacentCanonicalReturn (O : OddOrbit) where
  base : CanonicalEndpointFloorContractingReturn O
  source : PositiveFirstCrossingSource O

  base_startIndex_eq :
    base.startIndex =
      O.globalMinimumIndex + source.minimalPositiveCandidate.startCut

  base_length_eq :
    base.length = source.minimalPositiveCandidate.length

  zeroCore :
    CanonicalEndpointFloorContractingReturn.CanonicalZeroCoreData base

  endFutureMinimum :
    O.FutureMinimumAt base.endIndex

namespace PositiveFirstCrossingSource

/--
A の最短 candidate は、その内部に自分より短い
positive / all-suffix-contracting subsegment を持てない。

endpoint floor を得るときに使った minimality を、後段で再利用できる形にする。
-/
theorem minimalPositiveCandidate_no_shorter_positive_subsegment
    {O : OddOrbit}
    (S : PositiveFirstCrossingSource O)
    {cut length : ℕ}
    (hlengthPos : 0 < length)
    (hinside : cut + length ≤ S.minimalPositiveCandidate.length)
    (hlengthLt : length < S.minimalPositiveCandidate.length)
    (hAll :
      Word.AllSuffixesContracting
        (O.segment
          (O.globalMinimumIndex +
            (S.minimalPositiveCandidate.startCut + cut))
          length))
    (hPositive :
      O.value
          (O.globalMinimumIndex +
            (S.minimalPositiveCandidate.startCut + cut)) <
        O.value
          (O.globalMinimumIndex +
            (S.minimalPositiveCandidate.startCut + cut + length))) :
    False := by
  let C := S.minimalPositiveCandidate
  let P : PositiveSubsegmentCandidate S := {
    startCut := C.startCut + cut
    length := length
    length_pos := hlengthPos
    end_le_source := by
      have hC := C.end_le_source
      have hinside' : cut + length ≤ C.length := by
        simpa [C] using hinside
      omega
    allSuffixesContracting := by
      simpa [C, Nat.add_assoc] using hAll
    positive := by
      simpa [C, Nat.add_assoc] using hPositive
  }
  have hmin : S.minimalPositiveLength ≤ P.length :=
    S.minimalPositiveLength_le P
  have hCmin :
      C.length = S.minimalPositiveLength := by
    simpa [C] using S.minimalPositiveCandidate_length
  have hLower : C.length ≤ P.length := by
    rw [hCmin]
    exact hmin
  have hPLen : P.length = length := rfl
  rw [hPLen] at hLower
  have hlengthLt' : length < C.length := by
    simpa [C] using hlengthLt
  omega

end PositiveFirstCrossingSource

namespace MinimalAdjacentCanonicalReturn

/-- base endpoint-floor object。 -/
def word
    {O : OddOrbit}
    (M : MinimalAdjacentCanonicalReturn O) : Word :=
  M.base.word

/-- B1 true zero-core natural coordinates。 -/
def natural
    {O : OddOrbit}
    (M : MinimalAdjacentCanonicalReturn O) :
    M.base.NaturalCoordinates :=
  M.zeroCore.natural

/-- true zero-core tail。 -/
def tail
    {O : OddOrbit}
    (M : MinimalAdjacentCanonicalReturn O) : Word :=
  M.zeroCore.natural.tail

/-- terminal index。 -/
def endIndex
    {O : OddOrbit}
    (M : MinimalAdjacentCanonicalReturn O) : ℕ :=
  M.base.endIndex

/-- first interior boundary value。 -/
def boundary
    {O : OddOrbit}
    (M : MinimalAdjacentCanonicalReturn O) : ℕ :=
  M.zeroCore.natural.boundary

/-- base start から endpoint への positive return。 -/
theorem startValue_lt_endValue
    {O : OddOrbit}
    (M : MinimalAdjacentCanonicalReturn O) :
    O.value M.base.startIndex < O.value M.endIndex := by
  simpa [endIndex, CanonicalEndpointFloorContractingReturn.endIndex] using
    M.base.positive

/-- endpoint future-minimum と endpoint floor から start も future minimum。 -/
theorem startFutureMinimum
    {O : OddOrbit}
    (M : MinimalAdjacentCanonicalReturn O) :
    O.FutureMinimumAt M.base.startIndex := by
  intro m hm
  by_cases hEq : m = M.base.startIndex
  · subst m
    exact le_rfl
  have hstartLt : M.base.startIndex < m := by
    omega
  by_cases hBefore : m < M.endIndex
  · let k := m - M.base.startIndex
    have hmEq : m = M.base.startIndex + k := by
      dsimp [k]
      omega
    have hkPos : 0 < k := by
      dsimp [k]
      omega
    have hkLt : k < M.base.length := by
      dsimp [endIndex, CanonicalEndpointFloorContractingReturn.endIndex] at hBefore
      dsimp [k]
      omega
    have hFloor := M.base.endpointFloor k hkPos hkLt
    have hPos := M.base.positive
    rw [hmEq]
    omega
  · have hEndLeM : M.base.endIndex ≤ m := by
      have h :
          M.endIndex ≤ m :=
        Nat.le_of_not_gt hBefore
      simpa [endIndex] using h
    have hTail :=
      M.endFutureMinimum m hEndLeM
    have hPos :
        O.value M.base.startIndex <
          O.value M.base.endIndex := by
      simpa [endIndex] using M.startValue_lt_endValue
    omega

/-- start/end の間に別の future minimum は存在しない。 -/
theorem not_futureMinimumAt_interior
    {O : OddOrbit}
    (M : MinimalAdjacentCanonicalReturn O)
    {k : ℕ}
    (hkPos : 0 < k)
    (hkLt : k < M.base.length) :
    ¬ O.FutureMinimumAt (M.base.startIndex + k) := by
  intro hMin
  have hLe :
      O.value (M.base.startIndex + k) ≤
        O.value M.endIndex := by
    apply hMin M.endIndex
    dsimp [endIndex, CanonicalEndpointFloorContractingReturn.endIndex]
    omega
  have hFloor :
      O.value M.endIndex <
        O.value (M.base.startIndex + k) := by
    simpa [endIndex, CanonicalEndpointFloorContractingReturn.endIndex] using
      M.base.endpointFloor k hkPos hkLt
  omega

/-- unbounded normalized orbit 上では future-minimum start は1ではない。 -/
theorem one_lt_startValue
    {O : OddOrbit}
    (M : MinimalAdjacentCanonicalReturn O) :
    1 < O.value M.base.startIndex := by
  have hpos := O.value_pos M.base.startIndex
  by_contra hnot
  have hx : O.value M.base.startIndex = 1 := by
    omega
  have hActual := O.step M.base.startIndex
  have hModel :
      2 ^ (2 : ℕ) * 1 = 3 * O.value M.base.startIndex + 1 := by
    rw [hx]
    norm_num
  have hUnique :=
    normalizedStep_unique
      hActual hModel
      (O.value_odd (M.base.startIndex + 1))
      (by decide : Odd (1 : ℕ))
  have hNext : O.value (M.base.startIndex + 1) = 1 := by
    simpa using hUnique.2
  have hRepeat :
      O.value M.base.startIndex =
        O.value (M.base.startIndex + 1) := by
    rw [hx, hNext]
  have hIndex := O.value_injective_of_unbounded M.base.unbounded hRepeat
  omega

/-- endpoint は start より大きいので `>1`。 -/
theorem one_lt_endValue
    {O : OddOrbit}
    (M : MinimalAdjacentCanonicalReturn O) :
    1 < O.value M.endIndex := by
  have hStart := M.one_lt_startValue
  have hPos := M.startValue_lt_endValue
  omega

/-- strengthened endpoint は future minimum なので、その直後 exponent は1。 -/
theorem endpointExponent_eq_one
    {O : OddOrbit}
    (M : MinimalAdjacentCanonicalReturn O) :
    O.exponent M.endIndex = 1 :=
  M.endFutureMinimum.exponent_eq_one_of_one_lt_value
    M.one_lt_endValue

/-- start も future minimum なので exponent は1。 -/
theorem startExponent_eq_one
    {O : OddOrbit}
    (M : MinimalAdjacentCanonicalReturn O) :
    O.exponent M.base.startIndex = 1 :=
  M.startFutureMinimum.exponent_eq_one_of_one_lt_value
    M.one_lt_startValue

/-- natural coordinate `n` は adjacent future-minimum gap の half-gap。 -/
theorem endValue_eq_startValue_add_two_mul_n
    {O : OddOrbit}
    (M : MinimalAdjacentCanonicalReturn O) :
    O.value M.endIndex =
      O.value M.base.startIndex + 2 * M.natural.n := by
  have h := M.natural.fullEnd_eq
  calc
    O.value M.endIndex
        = Word.canonicalEnd M.base.word := by
            simpa [endIndex,
              CanonicalEndpointFloorContractingReturn.endIndex,
              CanonicalEndpointFloorContractingReturn.word] using
              M.base.endCanonical
    _ = Word.canonicalStart M.base.word + 2 * M.natural.n := h
    _ = O.value M.base.startIndex + 2 * M.natural.n := by
          simpa [CanonicalEndpointFloorContractingReturn.word] using
            congrArg (fun x => x + 2 * M.natural.n)
              M.base.startCanonical.symm

/-- start/end がともに `3 mod 4` なので natural half-gap `n` は偶数。 -/
theorem exists_halfGap_half
    {O : OddOrbit}
    (M : MinimalAdjacentCanonicalReturn O) :
    ∃ q : ℕ, M.natural.n = 2 * q := by
  obtain ⟨a, ha⟩ :=
    M.startFutureMinimum.value_eq_four_mul_add_three
      M.one_lt_startValue
  obtain ⟨b, hb⟩ :=
    M.endFutureMinimum.value_eq_four_mul_add_three
      M.one_lt_endValue
  have hret :
      O.value M.base.endIndex =
        O.value M.base.startIndex + 2 * M.natural.n := by
    simpa [endIndex] using
      M.endValue_eq_startValue_add_two_mul_n
  have hlt :
      O.value M.base.startIndex <
        O.value M.base.endIndex := by
    simpa [endIndex] using
      M.startValue_lt_endValue
  have hab : a < b := by
    rw [ha, hb] at hlt
    omega
  refine ⟨b - a, ?_⟩
  rw [ha, hb] at hret
  omega

/-- tail は actual segment そのもの。 -/
theorem tail_eq_actual_segment
    {O : OddOrbit}
    (M : MinimalAdjacentCanonicalReturn O) :
    M.tail =
      O.segment
        (M.base.startIndex + 1)
        M.tail.length := by
  simpa [tail] using M.zeroCore.tail_eq_actual_segment

/-- tail は nonempty。 -/
theorem tail_nonempty
    {O : OddOrbit}
    (M : MinimalAdjacentCanonicalReturn O) :
    M.tail ≠ [] := by
  simpa [tail] using M.zeroCore.natural.tail_nonempty

/-- tail は valid。 -/
theorem tail_valid
    {O : OddOrbit}
    (M : MinimalAdjacentCanonicalReturn O) :
    Word.Valid M.tail := by
  simpa [tail] using M.zeroCore.tail_valid

/-- tail は contracting。 -/
theorem tail_contracting
    {O : OddOrbit}
    (M : MinimalAdjacentCanonicalReturn O) :
    Word.Contracting M.tail := by
  simpa [tail] using M.zeroCore.tail_contracting

/-- first interior boundary は actual orbit value。 -/
theorem boundary_eq_value
    {O : OddOrbit}
    (M : MinimalAdjacentCanonicalReturn O) :
    M.boundary = O.value (M.base.startIndex + 1) := by
  simpa [boundary, natural] using M.zeroCore.natural.boundary_eq

/-- endpoint value は tail canonical endpoint。 -/
theorem endValue_eq_tailCanonicalEnd
    {O : OddOrbit}
    (M : MinimalAdjacentCanonicalReturn O) :
    O.value M.endIndex = Word.canonicalEnd M.tail := by
  calc
    O.value M.endIndex
        = Word.canonicalEnd M.base.word := by
            simpa [endIndex,
              CanonicalEndpointFloorContractingReturn.endIndex,
              CanonicalEndpointFloorContractingReturn.word] using
              M.base.endCanonical
    _ = Word.canonicalEnd M.tail := by
          simpa [tail] using M.zeroCore.fullEnd_eq_tailEnd

/-- first boundary は tail canonical start。 -/
theorem boundary_eq_tailCanonicalStart
    {O : OddOrbit}
    (M : MinimalAdjacentCanonicalReturn O) :
    M.boundary = Word.canonicalStart M.tail := by
  simpa [boundary, tail] using M.zeroCore.boundary_eq_tailStart

/--
A provenance により、base 内部に base より短い positive
all-suffix-contracting subsegment は存在しない。
-/
theorem no_shorter_positive_subsegment
    {O : OddOrbit}
    (M : MinimalAdjacentCanonicalReturn O)
    {cut length : ℕ}
    (hlengthPos : 0 < length)
    (hinside : cut + length ≤ M.base.length)
    (hlengthLt : length < M.base.length)
    (hAll :
      Word.AllSuffixesContracting
        (O.segment (M.base.startIndex + cut) length))
    (hPositive :
      O.value (M.base.startIndex + cut) <
        O.value (M.base.startIndex + cut + length)) :
    False := by
  have hCutInside :
      cut + length ≤ M.source.minimalPositiveCandidate.length := by
    rw [← M.base_length_eq]
    exact hinside
  have hLenLt :
      length < M.source.minimalPositiveCandidate.length := by
    rw [← M.base_length_eq]
    exact hlengthLt
  have hAll' :
      Word.AllSuffixesContracting
        (O.segment
          (O.globalMinimumIndex +
            (M.source.minimalPositiveCandidate.startCut + cut))
          length) := by
    simpa [M.base_startIndex_eq, Nat.add_assoc] using hAll
  have hPositive' :
      O.value
          (O.globalMinimumIndex +
            (M.source.minimalPositiveCandidate.startCut + cut)) <
        O.value
          (O.globalMinimumIndex +
            (M.source.minimalPositiveCandidate.startCut + cut + length)) := by
    simpa [M.base_startIndex_eq, Nat.add_assoc] using hPositive
  exact
    M.source.minimalPositiveCandidate_no_shorter_positive_subsegment
      hlengthPos hCutInside hLenLt hAll' hPositive'

/--
既存 A constructor から strengthened packet を作る薄い constructor。
追加で必要なのは B1 zero-core と、その同じ endpoint が future minimum である証明だけ。
-/
noncomputable def ofCurrentReduction
    {O : OddOrbit}
    (S : PositiveFirstCrossingSource O)
    (hGap : TwoThreeSmallGapExclusion)
    (Z :
      CanonicalEndpointFloorContractingReturn.CanonicalZeroCoreData
        (S.toCanonicalEndpointFloorContractingReturn hGap))
    (hEndFuture :
      O.FutureMinimumAt
        (S.toCanonicalEndpointFloorContractingReturn hGap).endIndex) :
    MinimalAdjacentCanonicalReturn O := by
  classical
  let D := S.toCanonicalEndpointFloorContractingReturn hGap
  exact {
    base := D
    source := S
    base_startIndex_eq := by
      rfl
    base_length_eq := by
      rfl
    zeroCore := by
      simpa [D] using Z
    endFutureMinimum := by
      simpa [D] using hEndFuture
  }

end MinimalAdjacentCanonicalReturn
end EndpointFloorReduction
end OddOrbit
end Collatz2
