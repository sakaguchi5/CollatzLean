import CollatzLean.Collatz3.Experimental2.YoungFerrersRestricted.MechanicalCollisionSpecialization

/-!
# Collatz3 Experimental2: basis 面積余剰の exact slack 分解

F6 では

`actual weight - basis weight = 2 * (actual arm sum - basis arm sum)`

まで得ていた。
本ファイルでは arm sum の差を、basis recurrence の各段で生じる非負 slack に分解する。

* terminal slack は `arm` と `leg` の小さい方。
* internal slack は arm strictness / leg strictness のうち active な方の余剰。

各 slack は右端から左へ arm excess を伝播させるため、総 arm excess では
右側の slack ほど大きな重みを持つ。
その weighted sum と actual-basis arm sum の差が exact に一致することを証明する。

これにより Young 面積余剰は単なる偶数ではなく、
非負な局所 slack の weighted sum のちょうど `2` 倍として読める。
-/

namespace Collatz3
namespace Experimental2
namespace YoungFerrersRestricted

/-- singleton Frobenius symbol の terminal basis slack。 -/
def terminalBasisSlack
    (s a : ℤ) : ℤ :=
  if s ≤ 0 then a else a - s

/--
隣接二段の basis recurrence に対する internal slack。
`rank` が増えない側では arm strictness、増える側では leg strictness が active。
-/
def stepBasisSlack
    (s t a b : ℤ) : ℤ :=
  if s ≤ t then
    a - (b + 1)
  else
    a - (b + 1 + s - t)

/-- realization から右向きに並べた basis slack vector。 -/
def basisSlackVector : List ℤ → List ℤ → List ℤ
  | [], [] => []
  | [s], [a] => [terminalBasisSlack s a]
  | s :: t :: ss, a :: b :: as =>
      stepBasisSlack s t a b ::
        basisSlackVector (t :: ss) (b :: as)
  | _, _ => []

/--
slack の weighted sum。
再帰式

`W(x::xs) = x + W(xs) + sum(xs)`

により、左から `i` 番目の slack は最終的に係数 `i+1` を持つ。
-/
def weightedBasisSlack : List ℤ → ℤ
  | [] => 0
  | x :: xs => x + weightedBasisSlack xs + xs.sum

/-- realization の各 basis slack は非負。 -/
theorem basisSlackVector_nonneg
    {ranks arms : List ℤ}
    (h : IsArmRealization ranks arms) :
    ∀ z ∈ basisSlackVector ranks arms, 0 ≤ z := by
  induction h with
  | nil =>
      intro z hz
      simp [basisSlackVector] at hz
  | single s a ha0 hleg =>
      intro z hz
      simp only [basisSlackVector, List.mem_singleton] at hz
      subst z
      by_cases hs : s ≤ 0
      · simp only [terminalBasisSlack, hs, ↓reduceIte]
        exact ha0
      · simp [terminalBasisSlack, hs]
        omega
  | @cons s t ss a b as hTail ha0 hleg hArm hLeg ih =>
      intro z hz
      simp only [basisSlackVector, List.mem_cons] at hz
      rcases hz with hHead | hTailMem
      · subst z
        by_cases hst : s ≤ t
        · simp [stepBasisSlack, hst]
          omega
        · simp [stepBasisSlack, hst]
          omega
      · exact ih z hTailMem

/-- 非負要素からなる整数 list の和は非負。 -/
theorem sum_nonneg_of_mem_nonneg :
    ∀ xs : List ℤ,
      (∀ x ∈ xs, 0 ≤ x) →
      0 ≤ xs.sum
  | [], _h => by simp
  | x :: xs, h => by
      have hx : 0 ≤ x := h x (by simp)
      have hTail : ∀ y ∈ xs, 0 ≤ y := by
        intro y hy
        exact h y (by simp [hy])
      have ih := sum_nonneg_of_mem_nonneg xs hTail
      simp only [List.sum_cons]
      omega

/-- 非負 slack vector の weighted sum も非負。 -/
theorem weightedBasisSlack_nonneg
    (xs : List ℤ)
    (h : ∀ x ∈ xs, 0 ≤ x) :
    0 ≤ weightedBasisSlack xs := by
  induction xs with
  | nil =>
      simp [weightedBasisSlack]
  | cons x xs ih =>
      have hx : 0 ≤ x := h x (by simp)
      have hTail : ∀ y ∈ xs, 0 ≤ y := by
        intro y hy
        exact h y (by simp [hy])
      have hW := ih hTail
      have hSum := sum_nonneg_of_mem_nonneg xs hTail
      simp only [weightedBasisSlack]
      omega

/--
slack 総和は先頭 arm の basis からの excess に等しい。
右側で生じた slack がすべて左端まで一度ずつ伝播することを表す。
-/
theorem basisSlackVector_sum_eq_headExcess
    {ranks arms : List ℤ}
    (h : IsArmRealization ranks arms) :
    (basisSlackVector ranks arms).sum =
      arms.getD 0 0 - (basisArms ranks).getD 0 0 := by
  induction h with
  | nil =>
      simp [basisSlackVector, basisArms]
  | single s a ha0 hleg =>
      by_cases hs : s ≤ 0
      · simp [basisSlackVector, terminalBasisSlack, basisArms, hs]
      · simp [basisSlackVector, terminalBasisSlack, basisArms, hs]
  | @cons s t ss a b as hTail ha0 hleg hArm hLeg ih =>
      simp only [basisSlackVector, List.sum_cons]
      rw [ih]
      rw [basisArms_cons_cons]
      by_cases hst : s ≤ t
      · simp [stepBasisSlack, hst]
        ring
      · simp [stepBasisSlack, hst]
        ring

/--
weighted slack は actual arm sum と canonical basis arm sum の差に exact に一致する。
これが面積余剰の局所分解の中心補題。
-/
theorem weightedBasisSlack_eq_armSum_sub_basisArmSum
    {ranks arms : List ℤ}
    (h : IsArmRealization ranks arms) :
    weightedBasisSlack (basisSlackVector ranks arms) =
      arms.sum - (basisArms ranks).sum := by
  induction h with
  | nil =>
      simp [basisSlackVector, weightedBasisSlack, basisArms]
  | single s a ha0 hleg =>
      by_cases hs : s ≤ 0
      · simp [basisSlackVector, weightedBasisSlack,
          terminalBasisSlack, basisArms, hs]
      · simp [basisSlackVector, weightedBasisSlack,
          terminalBasisSlack, basisArms, hs]
  | @cons s t ss a b as hTail ha0 hleg hArm hLeg ih =>
      have hHead := basisSlackVector_sum_eq_headExcess hTail
      simp only [basisSlackVector, weightedBasisSlack, List.sum_cons]
      rw [ih, hHead]
      rw [basisArms_cons_cons]
      by_cases hst : s ≤ t
      · simp [stepBasisSlack, hst]
        ring
      · simp [stepBasisSlack, hst]
        ring

/--
任意 realization の symbol weight 余剰は weighted slack のちょうど2倍。
F6 の parity theorem を exact local decomposition に強化した形。
-/
theorem symbolWeightZ_sub_basisWeightZ_eq_two_mul_weightedSlack
    {ranks arms : List ℤ}
    (h : IsArmRealization ranks arms) :
    symbolWeightZ ranks arms - basisWeightZ ranks =
      2 * weightedBasisSlack (basisSlackVector ranks arms) := by
  rw [symbolWeightZ_sub_basisWeightZ]
  rw [weightedBasisSlack_eq_armSum_sub_basisArmSum h]

/-- actual Frobenius symbol の slack vector。 -/
def frobeniusBasisSlacks
    (c : WidthDropCode) : List ℤ :=
  basisSlackVector (successiveRankVector c) (frobeniusArmsZ c)

/-- actual Young shape の weighted basis excess。 -/
def frobeniusWeightedBasisExcess
    (c : WidthDropCode) : ℤ :=
  weightedBasisSlack (frobeniusBasisSlacks c)

/-- actual Frobenius slack はすべて非負。 -/
theorem frobeniusBasisSlacks_nonneg
    (c : WidthDropCode) :
    ∀ z ∈ frobeniusBasisSlacks c, 0 ≤ z := by
  unfold frobeniusBasisSlacks
  exact basisSlackVector_nonneg (frobeniusVectors_realize c)

/-- actual weighted basis excess は非負。 -/
theorem frobeniusWeightedBasisExcess_nonneg
    (c : WidthDropCode) :
    0 ≤ frobeniusWeightedBasisExcess c := by
  unfold frobeniusWeightedBasisExcess
  exact weightedBasisSlack_nonneg _ (frobeniusBasisSlacks_nonneg c)

/--
Young/Ferrers code の actual area と basis area の差の exact slack 分解。
-/
theorem codeArea_sub_basisWeightZ_eq_two_mul_weightedExcess
    (c : WidthDropCode) :
    (codeArea c : ℤ) - basisWeightZ (successiveRankVector c) =
      2 * frobeniusWeightedBasisExcess c := by
  rw [← frobeniusSymbolWeight_eq_codeArea c]
  unfold frobeniusWeightedBasisExcess frobeniusBasisSlacks
  exact
    symbolWeightZ_sub_basisWeightZ_eq_two_mul_weightedSlack
      (frobeniusVectors_realize c)

/--
weighted excess が0であることと、F7 の no-simultaneous-corner 条件は同値。
したがって weighted excess は basis equality からの genuine な距離量になる。
-/
theorem frobeniusWeightedBasisExcess_eq_zero_iff_noSimultaneousDiagonalCorner
    (c : WidthDropCode) :
    frobeniusWeightedBasisExcess c = 0 ↔
      NoSimultaneousDiagonalCorner
        (successiveRankVector c) (frobeniusArmsZ c) := by
  constructor
  · intro hZero
    have hGap := codeArea_sub_basisWeightZ_eq_two_mul_weightedExcess c
    rw [hZero] at hGap
    have hEq :
        (codeArea c : ℤ) = basisWeightZ (successiveRankVector c) := by
      omega
    exact
      (codeArea_eq_basisWeightZ_iff_noSimultaneousDiagonalCorner c).1 hEq
  · intro hCorner
    have hEq :
        (codeArea c : ℤ) = basisWeightZ (successiveRankVector c) :=
      (codeArea_eq_basisWeightZ_iff_noSimultaneousDiagonalCorner c).2 hCorner
    have hGap := codeArea_sub_basisWeightZ_eq_two_mul_weightedExcess c
    rw [hEq] at hGap
    omega

end YoungFerrersRestricted

namespace GenericRecordFerrers
namespace RecordFerrers

open YoungFerrersRestricted

/-- RecordFerrers rank-envelope shape の weighted basis excess。 -/
def basisWeightedExcess
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m) : ℤ :=
  frobeniusWeightedBasisExcess R.plateauWidthDropCode

/-- RecordFerrers の weighted basis excess は非負。 -/
theorem basisWeightedExcess_nonneg
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m) :
    0 ≤ R.basisWeightedExcess := by
  unfold basisWeightedExcess
  exact frobeniusWeightedBasisExcess_nonneg R.plateauWidthDropCode

/--
RecordFerrers Young 面積の actual-basis 差は weighted excess のちょうど2倍。
-/
theorem youngCellCount_sub_basisWeightZ_eq_two_mul_weightedExcess
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m) :
    (R.youngCellCount : ℤ) - basisWeightZ R.successiveRanks =
      2 * R.basisWeightedExcess := by
  unfold basisWeightedExcess youngCellCount successiveRanks
  exact codeArea_sub_basisWeightZ_eq_two_mul_weightedExcess R.plateauWidthDropCode

/--
weighted excess が0であることと F8 の canonical plateau basis condition は同値。
内部 collision 禁止と terminal tightness を一つの非負整数で測れる。
-/
theorem basisWeightedExcess_eq_zero_iff_canonicalPlateauBasisCondition
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m) :
    R.basisWeightedExcess = 0 ↔
      R.CanonicalPlateauBasisCondition := by
  unfold basisWeightedExcess
  rw [frobeniusWeightedBasisExcess_eq_zero_iff_noSimultaneousDiagonalCorner]
  exact R.noSimultaneousDiagonalCorner_iff_canonicalPlateauBasisCondition

/-- internal collision が一つでもあれば weighted excess は正。 -/
theorem basisWeightedExcess_pos_of_internalCollision
    {β : ℕ → ℕ}
    {m t : ℕ}
    (R : RecordFerrers β m)
    (ht : 0 < t)
    (htD : t < frobeniusDepth R.plateauWidthDropCode)
    (hC : R.HasCanonicalBoundaryCollision t) :
    0 < R.basisWeightedExcess := by
  have hNonneg := R.basisWeightedExcess_nonneg
  have hNotBasis :=
    R.canonicalPlateauBasisCondition_false_of_internalCollision ht htD hC
  have hNe : R.basisWeightedExcess ≠ 0 := by
    intro hZero
    exact hNotBasis
      ((R.basisWeightedExcess_eq_zero_iff_canonicalPlateauBasisCondition).1 hZero)
  omega

end RecordFerrers
end GenericRecordFerrers
end Experimental2
end Collatz3
