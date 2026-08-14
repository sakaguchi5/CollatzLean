import CollatzLean.Collatz2.Canonical.PositiveSuffixBudget
import CollatzLean.Collatz2.Global.OddOrbitSurvivalBridge
import CollatzLean.Collatz2.Local.ContractingClosure
import CollatzLean.Collatz2.Orbit.FutureMinimumSelection

/-!
# Collatz2 Global: canonical adjacent contracting return

q=0 right branch の最終局面で使う orbit-level finite object。

start は orbit の global minimum、endpoint はその直後の tail における
次の future minimum とし、block 内部の全 boundary は endpoint より strict に上にある。
さらに block 自身は contracting で、actual start/end は canonical start/end と一致する。

この object からは FirstCrossing を使わずに

* canonical-positive
* AllSuffixesContracting
* 6*n < p
* sigma * 2^H = 3*G*S + K

を回収できる。
-/

namespace Collatz2
namespace OddOrbit

/-- global minimum index 自身は future minimum。 -/
theorem globalMinimumIndex_futureMinimum
    (O : OddOrbit) :
    O.FutureMinimumAt O.globalMinimumIndex := by
  intro m hm
  rw [O.value_globalMinimumIndex]
  exact O.globalMinimumValue_le_value m

/-- orbit segment の drop は開始 index を同じ長さだけ右へ移した segment。 -/
theorem segment_drop_of_le
    (O : OddOrbit)
    {i n k : ℕ}
    (hk : k ≤ n) :
    (O.segment i n).drop k =
      O.segment (i + k) (n - k) := by
  have hsum : k + (n - k) = n := by
    omega
  have h := O.segment_add i k (n - k)
  rw [hsum] at h
  rw [h]
  simp

/--
canonical adjacent contracting return。

`length` は global minimum から次の selected endpoint までの odd-step 数。
`interiorAboveEnd` により endpoint より前の内部 boundary はすべて endpoint より上。
従って interior に別の future minimum は存在できない。
-/
structure CanonicalAdjacentContractingReturn (O : OddOrbit) where
  unbounded : O.Unbounded
  length : ℕ
  length_pos : 0 < length

  endFutureMinimum :
    O.FutureMinimumAt (O.globalMinimumIndex + length)

  interiorAboveEnd :
    ∀ k : ℕ,
      0 < k →
      k < length →
      O.value (O.globalMinimumIndex + length) <
        O.value (O.globalMinimumIndex + k)

  contracting :
    Word.Contracting
      (O.segment O.globalMinimumIndex length)

  startCanonical :
    O.globalMinimumValue =
      Word.canonicalStart
        (O.segment O.globalMinimumIndex length)

  endCanonical :
    O.value (O.globalMinimumIndex + length) =
      Word.canonicalEnd
        (O.segment O.globalMinimumIndex length)

namespace CanonicalAdjacentContractingReturn

/-- block word。 -/
noncomputable def word
    {O : OddOrbit}
    (D : CanonicalAdjacentContractingReturn O) : Word :=
  O.segment O.globalMinimumIndex D.length

/-- block endpoint index。 -/
noncomputable def endIndex
    {O : OddOrbit}
    (D : CanonicalAdjacentContractingReturn O) : ℕ :=
  O.globalMinimumIndex + D.length

@[simp] theorem word_length
    {O : OddOrbit}
    (D : CanonicalAdjacentContractingReturn O) :
    D.word.length = D.length := by
  simp [word]

/-- block word は nonempty。 -/
theorem word_nonempty
    {O : OddOrbit}
    (D : CanonicalAdjacentContractingReturn O) :
    D.word ≠ [] := by
  apply List.ne_nil_of_length_pos
  rw [D.word_length]
  exact D.length_pos

/-- block は actual normalized run。 -/
theorem runs
    {O : OddOrbit}
    (D : CanonicalAdjacentContractingReturn O) :
    Runs D.word
      O.globalMinimumValue
      (O.value D.endIndex) := by
  unfold word endIndex
  simpa [O.value_globalMinimumIndex] using
    O.runsSegment O.globalMinimumIndex D.length

/-- block word は valid。 -/
theorem word_valid
    {O : OddOrbit}
    (D : CanonicalAdjacentContractingReturn O) :
    Word.Valid D.word :=
  D.runs.valid

/-- global minimum から endpoint への return は strict positive。 -/
theorem startValue_lt_endValue
    {O : OddOrbit}
    (D : CanonicalAdjacentContractingReturn O) :
    O.globalMinimumValue < O.value D.endIndex := by
  have hle :
      O.globalMinimumValue ≤ O.value D.endIndex :=
    O.globalMinimumValue_le_value D.endIndex
  have hidx :
      O.globalMinimumIndex < D.endIndex := by
    have hlen : 0 < D.length := D.length_pos
    unfold endIndex
    omega
  have hne :
      O.globalMinimumValue ≠ O.value D.endIndex := by
    rw [← O.value_globalMinimumIndex]
    exact O.value_ne_of_lt_of_unbounded D.unbounded hidx
  omega

/-- actual block は canonical-positive。 -/
theorem canonicalPositive
    {O : OddOrbit}
    (D : CanonicalAdjacentContractingReturn O) :
    Word.canonicalStart D.word < Word.canonicalEnd D.word := by
  calc
    Word.canonicalStart D.word
        = O.globalMinimumValue := by
            simpa [word] using D.startCanonical.symm
    _ < O.value D.endIndex := D.startValue_lt_endValue
    _ = Word.canonicalEnd D.word := by
          simpa [word, endIndex] using D.endCanonical

/-- global minimum は future minimum。 -/
theorem startFutureMinimum
    {O : OddOrbit} :
    O.FutureMinimumAt O.globalMinimumIndex :=
  O.globalMinimumIndex_futureMinimum

/--
endpoint は start より後の任意の orbit value 以下。
interior では `interiorAboveEnd`、endpoint 以後では `endFutureMinimum` を使う。
-/
theorem endValue_le_of_startIndex_lt
    {O : OddOrbit}
    (D : CanonicalAdjacentContractingReturn O)
    {m : ℕ}
    (hm : O.globalMinimumIndex < m) :
    O.value D.endIndex ≤ O.value m := by
  by_cases hBefore : m < D.endIndex
  · let k := m - O.globalMinimumIndex
    have hmEq : m = O.globalMinimumIndex + k := by
      dsimp [k]
      omega
    have hkPos : 0 < k := by
      dsimp [k]
      omega
    have hkLt : k < D.length := by
      unfold endIndex at hBefore
      dsimp [k]
      omega
    have hlt := D.interiorAboveEnd k hkPos hkLt
    have hlt' : O.value D.endIndex < O.value m := by
      simpa [endIndex, hmEq] using hlt
    exact Nat.le_of_lt hlt'
  · have hEndLe : D.endIndex ≤ m := Nat.le_of_not_gt hBefore
    exact D.endFutureMinimum m hEndLe

/--
endpoint index は global minimum の一つ後から選ぶ tail-minimum index と一致する。

従ってこの block は index/value の両方で canonical な adjacent future-minimum block。
-/
theorem endIndex_eq_tailMinIndex_after_start
    {O : OddOrbit}
    (D : CanonicalAdjacentContractingReturn O) :
    D.endIndex =
      FutureMinimumSelection.tailMinIndex
        O (O.globalMinimumIndex + 1) := by
  classical
  let j :=
    FutureMinimumSelection.tailMinIndex
      O (O.globalMinimumIndex + 1)
  have hjge :
      O.globalMinimumIndex + 1 ≤ j := by
    dsimp [j]
    exact
      FutureMinimumSelection.tailMinIndex_ge
        O (O.globalMinimumIndex + 1)
  have hEndLeJ :
      O.value D.endIndex ≤ O.value j := by
    apply D.endValue_le_of_startIndex_lt
    omega
  have hStartLeEnd :
      O.globalMinimumIndex + 1 ≤ D.endIndex := by
    have hlen : 0 < D.length := D.length_pos
    unfold endIndex
    omega
  have hJLeEnd :
      O.value j ≤ O.value D.endIndex := by
    have hval :
        O.value j =
          FutureMinimumSelection.tailMinValue
            O (O.globalMinimumIndex + 1) := by
      dsimp [j]
      exact
        FutureMinimumSelection.value_tailMinIndex
          O (O.globalMinimumIndex + 1)
    rw [hval]
    exact
      FutureMinimumSelection.tailMinValue_le
        O
        (O.globalMinimumIndex + 1)
        D.endIndex
        hStartLeEnd
  have hvalues :
      O.value D.endIndex = O.value j :=
    Nat.le_antisymm hEndLeJ hJLeEnd
  have hindices : D.endIndex = j :=
    O.value_injective_of_unbounded D.unbounded hvalues
  simpa [j] using hindices

/-- interior boundary は future minimum にはなれない。 -/
theorem not_futureMinimumAt_interior
    {O : OddOrbit}
    (D : CanonicalAdjacentContractingReturn O)
    {k : ℕ}
    (hkPos : 0 < k)
    (hkLt : k < D.length) :
    ¬ O.FutureMinimumAt (O.globalMinimumIndex + k) := by
  intro hmin
  have hle :
      O.value (O.globalMinimumIndex + k) ≤
        O.value (O.globalMinimumIndex + D.length) :=
    hmin
      (O.globalMinimumIndex + D.length)
      (by omega)
  have hgt := D.interiorAboveEnd k hkPos hkLt
  omega

/--
whole は contracting、proper suffix は endpoint への strict descent なので、
全 nonempty suffix が contracting。
-/
theorem allSuffixesContracting
    {O : OddOrbit}
    (D : CanonicalAdjacentContractingReturn O) :
    Word.AllSuffixesContracting D.word := by
  intro k hk
  apply (Word.suffixDeterminant_neg_iff_contracting).2
  by_cases hk0 : k = 0
  · subst k
    simpa [word] using D.contracting
  · have hkPos : 0 < k := Nat.pos_of_ne_zero hk0
    have hkLt : k < D.length := by
      simpa [D.word_length] using hk
    have hkLe : k ≤ D.length := Nat.le_of_lt hkLt
    have hdrop :=
      O.segment_drop_of_le
        (i := O.globalMinimumIndex)
        (n := D.length)
        hkLe
    rw [word, hdrop]
    have hrun :=
      O.runsSegment
        (O.globalMinimumIndex + k)
        (D.length - k)
    have hne :
        O.segment (O.globalMinimumIndex + k) (D.length - k) ≠ [] := by
      apply List.ne_nil_of_length_pos
      simp
      omega
    apply Word.Runs.contracting_of_end_lt_start hrun hne
    have hidx :
        O.globalMinimumIndex + k + (D.length - k) =
          O.globalMinimumIndex + D.length := by
      omega
    rw [hidx]
    exact D.interiorAboveEnd k hkPos hkLt

/--
最終 obstruction の half-gap / sigma exact budget。
FirstCrossing はここでは不要。
-/
theorem exists_halfGap_sigma_budgetIdentity
    {O : OddOrbit}
    (D : CanonicalAdjacentContractingReturn O) :
    ∃ n sigma : ℕ,
      0 < n ∧
      0 < sigma ∧
      Word.canonicalEnd D.word =
        Word.canonicalStart D.word + 2 * n ∧
      Word.oddSteps D.word = 6 * n + sigma ∧
      sigma * 2 ^ Word.twoSteps D.word =
        3 * (AffineTransfer.ofWord D.word).centerGap *
              Word.canonicalStart D.word +
          Word.suffixBudgetExcess D.word := by
  exact
    D.allSuffixesContracting.exists_canonicalHalfGap_sigma_budgetIdentity
      D.word_valid
      D.word_nonempty
      D.canonicalPositive

end CanonicalAdjacentContractingReturn
end OddOrbit
end Collatz2
