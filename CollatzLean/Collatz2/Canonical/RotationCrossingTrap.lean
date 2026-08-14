import CollatzLean.Collatz2.Global.MinimalAdjacentCanonicalReturn
import CollatzLean.Collatz2.External.TwoThreeEffectiveGap

/-!
# Collatz2 Canonical: minimal-adjacent zero-core rotation trap

`MinimalAdjacentCanonicalReturn` の whole word を

  w = 1 :: v

とする。
endpoint `T` が future minimum なので、その直後 exponent は1。
従って cyclic rotation

  rho = v ++ [1]

は actual orbit run になる。

natural coordinates から rotation endpoint `U` は exact に

  U = boundary + 3*n

なので rotation は strict positive。
また cyclic rotation は odd/two coefficient を保存するため contracting。

一方 `v` 自身も contracting なので、その最初の FirstCrossing prefix を取れる。
A の minimality により、その crossing endpoint `Y` は rotation start `s` より下。
元の endpoint floor により

  T <= Y < s

まで lossless に得る。

注意:
`Y=T`（tail 自身が FirstCrossing）の terminal case は一般には排除されていない。
proper interior crossing なら strict に

  T < Y < s

となる。

この terminal/interior 両方をまとめて排除する最終局所 principle を
`NoRotationCrossingTrap` として Prop 化する。
-/

namespace Collatz2
namespace OddOrbit
namespace EndpointFloorReduction
namespace MinimalAdjacentCanonicalReturn

/-- `p <= w.length` なら singleton append は先頭 `p` 文字を変えない。 -/
private theorem take_append_singleton_of_le_length
    {α : Type*}
    (w : List α)
    (a : α)
    {p : ℕ}
    (hp : p ≤ w.length) :
    (w ++ [a]).take p = w.take p := by
  induction w generalizing p with
  | nil =>
      have hp0 : p = 0 := by
        simp at hp
        omega
      subst p
      simp
  | cons x w ih =>
      cases p with
      | zero =>
          simp
      | succ p =>
          have hp' : p ≤ w.length := by
            simp at hp
            omega
          simp [ih hp']

/-- cyclic rotation `v ++ [1]`。 -/
def rotationWord
    {O : OddOrbit}
    (M : MinimalAdjacentCanonicalReturn O) : Word :=
  M.tail ++ [1]

/-- rotation の actual terminal index。 -/
def rotationEndIndex
    {O : OddOrbit}
    (M : MinimalAdjacentCanonicalReturn O) : ℕ :=
  M.endIndex + 1

/-- endpoint 直後の一文字 run は exponent 1。 -/
theorem endpointOneRun
    {O : OddOrbit}
    (M : MinimalAdjacentCanonicalReturn O) :
    Runs ([1] : Word)
      (O.value M.endIndex)
      (O.value M.rotationEndIndex) := by
  have h := O.runsSegment M.endIndex 1
  simpa [rotationEndIndex, M.endpointExponent_eq_one] using h

/-- tail actual run。 -/
theorem tailRuns
    {O : OddOrbit}
    (M : MinimalAdjacentCanonicalReturn O) :
    Runs M.tail
      M.boundary
      (O.value M.endIndex) := by
  have h :=
    O.runsSegment
      (M.base.startIndex + 1)
      M.tail.length
  rw [← M.tail_eq_actual_segment] at h
  have hLen :
      M.base.length = M.tail.length + 1 := by
    have hTail := M.zeroCore.natural.tail_length_add_one
    simpa [tail, word] using hTail.symm
  have hIndex :
      M.base.startIndex + 1 + M.tail.length = M.endIndex := by
    dsimp [endIndex, CanonicalEndpointFloorContractingReturn.endIndex]
    omega
  rw [hIndex] at h
  rw [M.boundary_eq_value]
  exact h

/-- rotation は actual normalized run。 -/
theorem rotationRuns
    {O : OddOrbit}
    (M : MinimalAdjacentCanonicalReturn O) :
    Runs M.rotationWord
      M.boundary
      (O.value M.rotationEndIndex) := by
  have h := M.tailRuns.append M.endpointOneRun
  simpa [rotationWord] using h

/-- rotation word は valid。 -/
theorem rotationValid
    {O : OddOrbit}
    (M : MinimalAdjacentCanonicalReturn O) :
    Word.Valid M.rotationWord :=
  M.rotationRuns.valid

/-- rotation word は nonempty。 -/
theorem rotationNonempty
    {O : OddOrbit}
    (M : MinimalAdjacentCanonicalReturn O) :
    M.rotationWord ≠ [] := by
  simp [rotationWord]

/-- rotation は whole word と同じ odd/two coefficient を持つ。 -/
theorem rotation_oddSteps_eq
    {O : OddOrbit}
    (M : MinimalAdjacentCanonicalReturn O) :
    Word.oddSteps M.rotationWord =
      Word.oddSteps M.base.word := by
  rw [M.zeroCore.natural.word_eq]
  simp [rotationWord, tail, Word.oddSteps]

/-- rotation は whole word と同じ total two exponent を持つ。 -/
theorem rotation_twoSteps_eq
    {O : OddOrbit}
    (M : MinimalAdjacentCanonicalReturn O) :
    Word.twoSteps M.rotationWord =
      Word.twoSteps M.base.word := by
  rw [M.zeroCore.natural.word_eq]
  simp [rotationWord, tail, Word.twoSteps]
  omega

/-- cyclic rotation も contracting。 -/
theorem rotationContracting
    {O : OddOrbit}
    (M : MinimalAdjacentCanonicalReturn O) :
    Word.Contracting M.rotationWord := by
  apply (Word.contracting_iff_threePow_lt_twoPow).2
  have h :=
    (Word.contracting_iff_threePow_lt_twoPow).1
      M.base.contracting
  rw [M.rotation_oddSteps_eq, M.rotation_twoSteps_eq]
  exact h

/-- rotation endpoint は exact に `boundary + 3*n`。 -/
theorem rotationEndValue_eq_boundary_add_three_mul_n
    {O : OddOrbit}
    (M : MinimalAdjacentCanonicalReturn O) :
    O.value M.rotationEndIndex =
      M.boundary + 3 * M.natural.n := by
  have hStep := O.step M.endIndex
  rw [M.endpointExponent_eq_one] at hStep
  norm_num at hStep
  have hEnd :
      O.value M.endIndex =
        Word.canonicalEnd M.base.word := by
    simpa [
      endIndex,
      CanonicalEndpointFloorContractingReturn.endIndex,
      CanonicalEndpointFloorContractingReturn.word
    ] using M.base.endCanonical
  rw [hEnd] at hStep
  have hStep' :
      2 * O.value M.rotationEndIndex =
        3 * Word.canonicalEnd M.base.word + 1 := by
    simpa [rotationEndIndex] using hStep
  have hT :
      Word.canonicalEnd M.base.word + 1 =
        6 * M.natural.n + 4 * M.natural.d := by
    simpa [natural] using
      M.natural.fullEnd_add_one
  have hS :
      M.boundary + 1 =
        6 * (M.natural.n + M.natural.d) := by
    simpa [boundary, natural] using
      M.natural.boundary_add_one
  omega

/-- rotation は strict positive return。 -/
theorem rotationPositive
    {O : OddOrbit}
    (M : MinimalAdjacentCanonicalReturn O) :
    M.boundary < O.value M.rotationEndIndex := by
  rw [M.rotationEndValue_eq_boundary_add_three_mul_n]
  have hn := M.natural.n_pos
  omega

/--
effective gap 下では rotation start は common modulus 未満。
zero-core の `canonicalStart(tail) < 2^K` を使う。
-/
theorem rotationStart_lt_modulus
    {O : OddOrbit}
    (M : MinimalAdjacentCanonicalReturn O)
    (hEffective : External.TwoThreeEffectiveGapInput) :
    M.boundary < Word.residueModulus M.rotationWord := by
  have hStart :
      Word.canonicalStart M.tail <
        2 ^ Word.twoSteps M.tail := by
    simpa [tail] using
      M.zeroCore.canonicalStart_tail_lt_twoPow hEffective
  have hBoundary :
      M.boundary = Word.canonicalStart M.tail :=
    M.boundary_eq_tailCanonicalStart
  have hPowPos :
      0 < 2 ^ Word.twoSteps M.tail :=
    Nat.pow_pos (by omega)
  have hMod :
      Word.residueModulus M.rotationWord =
        4 * 2 ^ Word.twoSteps M.tail := by
    unfold Word.residueModulus
    simp [rotationWord, Word.twoSteps, pow_add]
    ring
  rw [hBoundary, hMod]
  nlinarith

/-- effective gap 下では rotation actual start も canonical representative。 -/
theorem rotationStartCanonical
    {O : OddOrbit}
    (M : MinimalAdjacentCanonicalReturn O)
    (hEffective : External.TwoThreeEffectiveGapInput) :
    M.boundary = Word.canonicalStart M.rotationWord := by
  exact
    M.rotationRuns.realizes.eq_canonicalStart_of_lt_modulus
      (M.rotationRuns.end_odd_of_ne_nil M.rotationNonempty)
      (M.rotationStart_lt_modulus hEffective)

/-- effective gap 下では rotation は q=0 canonical run。 -/
theorem rotationEndCanonical
    {O : OddOrbit}
    (M : MinimalAdjacentCanonicalReturn O)
    (hEffective : External.TwoThreeEffectiveGapInput) :
    O.value M.rotationEndIndex =
      Word.canonicalEnd M.rotationWord := by
  let R :
      Word.ReplayCoordinate
        M.rotationWord
        M.boundary
        (O.value M.rotationEndIndex) :=
    Word.ReplayCoordinate.ofRuns
      M.rotationRuns M.rotationNonempty
  have hq : R.quotient = 0 :=
    R.quotient_eq_zero_of_start_eq_canonical
      (M.rotationStartCanonical hEffective)
  exact R.finish_eq_canonical_of_quotient_eq_zero hq

/--
rotation tail `v` の最初の coefficient crossing が作る trap。

無条件には `T <= Y < s`。
`crossingLength < tail.length` なら `T < Y < s`。
-/
structure RotationCrossingTrap
    {O : OddOrbit}
    (M : MinimalAdjacentCanonicalReturn O) : Type where
  crossingLength : ℕ
  crossingLength_pos : 0 < crossingLength
  crossingLength_le_tail : crossingLength ≤ M.tail.length

  firstCrossing :
    Word.FirstCrossing (M.tail.take crossingLength)

  crossingRuns :
    Runs (M.tail.take crossingLength)
      M.boundary
      (O.value (M.base.startIndex + 1 + crossingLength))

  endpoint_le_crossing :
    O.value M.endIndex ≤
      O.value (M.base.startIndex + 1 + crossingLength)

  crossing_lt_boundary :
    O.value (M.base.startIndex + 1 + crossingLength) <
      M.boundary

namespace RotationCrossingTrap

/-- trap の FirstCrossing は rotation 自身の同じ長さの prefix crossing。 -/
theorem rotationFirstCrossing
    {O : OddOrbit}
    {M : MinimalAdjacentCanonicalReturn O}
    (R : RotationCrossingTrap M) :
    Word.FirstCrossing (M.rotationWord.take R.crossingLength) := by
  have htake :
      M.rotationWord.take R.crossingLength =
        M.tail.take R.crossingLength := by
    simpa [rotationWord] using
      take_append_singleton_of_le_length
        M.tail (1 : ℕ) R.crossingLength_le_tail
  rw [htake]
  exact R.firstCrossing

/-- terminal crossing なら crossing value は original endpoint そのもの。 -/
theorem crossingValue_eq_endpoint_of_terminal
    {O : OddOrbit}
    {M : MinimalAdjacentCanonicalReturn O}
    (R : RotationCrossingTrap M)
    (hterminal : R.crossingLength = M.tail.length) :
    O.value (M.base.startIndex + 1 + R.crossingLength) =
      O.value M.endIndex := by
  have hLen :
      M.base.length = M.tail.length + 1 := by
    have h := M.zeroCore.natural.tail_length_add_one
    simpa [tail] using h.symm
  apply congrArg O.value
  dsimp [endIndex, CanonicalEndpointFloorContractingReturn.endIndex]
  rw [hterminal]
  omega

/-- proper interior crossing なら endpoint より strict に上。 -/
theorem endpoint_lt_crossing_of_interior
    {O : OddOrbit}
    {M : MinimalAdjacentCanonicalReturn O}
    (R : RotationCrossingTrap M)
    (hinterior : R.crossingLength < M.tail.length) :
    O.value M.endIndex <
      O.value (M.base.startIndex + 1 + R.crossingLength) := by
  have hkLt :
      1 + R.crossingLength < M.base.length := by
    have hLen :
        M.base.length = M.tail.length + 1 := by
      have h := M.zeroCore.natural.tail_length_add_one
      simpa [tail] using h.symm
    omega
  simpa [endIndex, CanonicalEndpointFloorContractingReturn.endIndex,
    Nat.add_assoc] using
    M.base.endpointFloor
      (1 + R.crossingLength)
      (by omega)
      hkLt

/-- lossless trap interval `T <= Y < s`。 -/
theorem endpoint_le_crossing_lt_boundary
    {O : OddOrbit}
    {M : MinimalAdjacentCanonicalReturn O}
    (R : RotationCrossingTrap M) :
    O.value M.endIndex ≤
        O.value (M.base.startIndex + 1 + R.crossingLength) ∧
      O.value (M.base.startIndex + 1 + R.crossingLength) <
        M.boundary :=
  ⟨R.endpoint_le_crossing, R.crossing_lt_boundary⟩

/-- proper interior crossing の strict trap `T < Y < s`。 -/
theorem strict_interval_of_interior
    {O : OddOrbit}
    {M : MinimalAdjacentCanonicalReturn O}
    (R : RotationCrossingTrap M)
    (hinterior : R.crossingLength < M.tail.length) :
    O.value M.endIndex <
        O.value (M.base.startIndex + 1 + R.crossingLength) ∧
      O.value (M.base.startIndex + 1 + R.crossingLength) <
        M.boundary :=
  ⟨R.endpoint_lt_crossing_of_interior hinterior,
    R.crossing_lt_boundary⟩

/-- terminal crossing branch は `Y = T < s`。 -/
theorem terminal_value_eq_and_lt_boundary
    {O : OddOrbit}
    {M : MinimalAdjacentCanonicalReturn O}
    (R : RotationCrossingTrap M)
    (hterminal : R.crossingLength = M.tail.length) :
    O.value (M.base.startIndex + 1 + R.crossingLength) =
        O.value M.endIndex ∧
      O.value M.endIndex < M.boundary := by
  refine ⟨R.crossingValue_eq_endpoint_of_terminal hterminal, ?_⟩
  have h := M.zeroCore.natural.fullEnd_lt_boundary
  calc
    O.value M.endIndex
        = Word.canonicalEnd M.base.word := by
            simpa [endIndex,
              CanonicalEndpointFloorContractingReturn.endIndex,
              CanonicalEndpointFloorContractingReturn.word] using
              M.base.endCanonical
    _ < M.boundary := by
      simpa [boundary, natural] using h

/-- crossing は terminal または strict interior の二つだけ。 -/
theorem terminal_or_interior
    {O : OddOrbit}
    {M : MinimalAdjacentCanonicalReturn O}
    (R : RotationCrossingTrap M) :
    R.crossingLength = M.tail.length ∨
      R.crossingLength < M.tail.length := by
  have hle := R.crossingLength_le_tail
  omega

end RotationCrossingTrap

/--
minimality と endpoint floor から rotation crossing trap を実際に構成する。
-/
theorem exists_rotationCrossingTrap
    {O : OddOrbit}
    (M : MinimalAdjacentCanonicalReturn O) :
    Nonempty (RotationCrossingTrap M) := by
  obtain ⟨p, hpLe, hFirst⟩ :=
    Word.exists_firstCrossing_of_contracting
      M.tail_valid M.tail_nonempty M.tail_contracting
  have hpPos : 0 < p := by
    have hne := hFirst.nonempty
    have htakeLen : (M.tail.take p).length = p :=
      List.length_take_of_le hpLe
    have hlenPos : 0 < (M.tail.take p).length :=
      List.length_pos_iff.mpr hne
    rw [htakeLen] at hlenPos
    exact hlenPos
  have htake :
      M.tail.take p =
        O.segment (M.base.startIndex + 1) p := by
    rw [M.tail_eq_actual_segment]
    exact O.segment_take_of_le hpLe
  have hRun :
      Runs (M.tail.take p)
        M.boundary
        (O.value (M.base.startIndex + 1 + p)) := by
    have h := O.runsSegment (M.base.startIndex + 1) p
    rw [← htake] at h
    rw [M.boundary_eq_value]
    simpa [Nat.add_assoc] using h
  have hCrossNeBoundary :
      O.value (M.base.startIndex + 1 + p) ≠ M.boundary := by
    rw [M.boundary_eq_value]
    intro hEq
    have hIndex := O.value_injective_of_unbounded M.base.unbounded hEq
    omega
  have hCrossLtBoundary :
      O.value (M.base.startIndex + 1 + p) < M.boundary := by
    by_contra hnot
    have hBoundaryLe :
        M.boundary ≤ O.value (M.base.startIndex + 1 + p) :=
      Nat.le_of_not_gt hnot
    have hBoundaryLt :
        M.boundary < O.value (M.base.startIndex + 1 + p) := by
      omega
    have hLen :
        M.base.length = M.tail.length + 1 := by
      have h := M.zeroCore.natural.tail_length_add_one
      simpa [tail] using h.symm
    have hInside : 1 + p ≤ M.base.length := by
      omega
    have hShort : p < M.base.length := by
      omega
    have hAll :
        Word.AllSuffixesContracting
          (O.segment (M.base.startIndex + 1) p) := by
      rw [← htake]
      exact hFirst.allSuffixesContracting
    exact
      False.elim
        (M.no_shorter_positive_subsegment
          hpPos hInside hShort hAll
          (by
            rw [← M.boundary_eq_value]
            simpa [Nat.add_assoc] using hBoundaryLt))
  have hEndpointLe :
      O.value M.endIndex ≤
        O.value (M.base.startIndex + 1 + p) := by
    by_cases hterminal : p = M.tail.length
    · have hLen :
          M.base.length = M.tail.length + 1 := by
        have h := M.zeroCore.natural.tail_length_add_one
        simpa [tail] using h.symm
      have hIdx :
          M.base.startIndex + 1 + p = M.endIndex := by
        dsimp [endIndex, CanonicalEndpointFloorContractingReturn.endIndex]
        rw [hterminal]
        omega
      calc
        O.value M.endIndex ≤ O.value M.endIndex := le_rfl
        _ = O.value (M.base.startIndex + 1 + p) :=
          (congrArg O.value hIdx).symm
    · have hpLt : p < M.tail.length := by
        omega
      have hkLt : 1 + p < M.base.length := by
        have hLen :
            M.base.length = M.tail.length + 1 := by
          have h := M.zeroCore.natural.tail_length_add_one
          simpa [tail] using h.symm
        omega
      have hFloor :=
        M.base.endpointFloor (1 + p) (by omega) hkLt
      simpa [endIndex,
        CanonicalEndpointFloorContractingReturn.endIndex,
        Nat.add_assoc] using Nat.le_of_lt hFloor
  let R : RotationCrossingTrap M := {
    crossingLength := p
    crossingLength_pos := hpPos
    crossingLength_le_tail := hpLe
    firstCrossing := hFirst
    crossingRuns := hRun
    endpoint_le_crossing := hEndpointLe
    crossing_lt_boundary := hCrossLtBoundary
  }
  exact ⟨R⟩

/--
最終局所 obstruction。
terminal crossing と strict interior crossing を分けず、
`MinimalAdjacentCanonicalReturn` から生じる rotation trap を一括排除する。
-/
def NoRotationCrossingTrap : Prop :=
  ∀ (O : OddOrbit)
    (M : MinimalAdjacentCanonicalReturn O)
    (_R : RotationCrossingTrap M),
      False

/-- `NoRotationCrossingTrap` があれば strengthened packet は存在しない。 -/
theorem not_minimalAdjacentCanonicalReturn_of_noRotationCrossingTrap
    (hNo : NoRotationCrossingTrap)
    (O : OddOrbit) :
    ¬ Nonempty (MinimalAdjacentCanonicalReturn O) := by
  rintro ⟨M⟩
  obtain ⟨R⟩ := M.exists_rotationCrossingTrap
  exact hNo O M R

end MinimalAdjacentCanonicalReturn
end EndpointFloorReduction
end OddOrbit
end Collatz2
