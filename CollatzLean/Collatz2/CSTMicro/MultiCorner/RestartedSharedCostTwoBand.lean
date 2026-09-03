import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedSharedCostArithmetic

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

namespace AttachedSharedCostPair

/--
二つの cost が `gap - defect` であるとき、master identity の左辺を
二重 predecessor の normalized defect 候補へ exact に書き換える。
-/
theorem modulus_mul_doubleNormalizedQCandidate_eq_masterRight
    (P : AttachedSharedCostPair)
    (D0 D1 : ℤ)
    (hCost0 : P.cost0 = P.gap - D0)
    (hCost1 : P.cost1 = P.gap - D1) :
    P.modulus *
        (P.normalizedQ + P.gap - D0 - D1) =
      P.gap * (P.deltaSum - P.representativeThreshold) +
        (P.affineB + P.weight0 + P.weight1) := by
  have hMaster := P.sharedCost_master_identity
  unfold costSum sharedBudget at hMaster
  rw [hCost0, hCost1] at hMaster
  nlinarith

/--
representative threshold に equality を許しても、
master identity の extra term が strict positive なので、
shared cost は shared budget を strict に超える。
-/
theorem sharedBudget_lt_costSum_of_representativeThreshold_le
    (P : AttachedSharedCostPair)
    (hThreshold :
      P.representativeThreshold ≤ P.deltaSum) :
    P.sharedBudget < P.costSum := by
  have hDelta :
      0 ≤ P.deltaSum - P.representativeThreshold :=
    sub_nonneg.mpr hThreshold
  have hGapTerm :
      0 ≤ P.gap *
        (P.deltaSum - P.representativeThreshold) :=
    mul_nonneg (le_of_lt P.gap_pos) hDelta
  have hRight :
      0 <
        P.gap * (P.deltaSum - P.representativeThreshold) +
          (P.affineB + P.weight0 + P.weight1) :=
    add_pos_of_nonneg_of_pos hGapTerm P.extra_pos
  have hLeft :
      0 < P.modulus * (P.costSum - P.sharedBudget) := by
    rw [P.sharedCost_master_identity]
    exact hRight
  nlinarith [P.modulus_pos]

/--
二つの cost が `gap - defect` であるとき、
non-strict representative threshold から strict two-band bound が出る。

これは
`D0 + D1 ≤ gap + normalizedQ`
より一段強い。
-/
theorem defectSum_lt_gap_add_normalizedQ_of_threshold_le
    (P : AttachedSharedCostPair)
    (D0 D1 : ℤ)
    (hCost0 : P.cost0 = P.gap - D0)
    (hCost1 : P.cost1 = P.gap - D1)
    (hThreshold :
      P.representativeThreshold ≤ P.deltaSum) :
    D0 + D1 < P.gap + P.normalizedQ := by
  have h :=
    P.sharedBudget_lt_costSum_of_representativeThreshold_le
      hThreshold
  unfold sharedBudget costSum at h
  rw [hCost0, hCost1] at h
  linarith

/--
二重 predecessor の normalized defect に対応する候補量。

`D0 + D1 < gap + normalizedQ` と同値な形を直接保持する。
-/
def doubleNormalizedQCandidate
    (P : AttachedSharedCostPair)
    (D0 D1 : ℤ) : ℤ :=
  P.normalizedQ + P.gap - D0 - D1

/-- master identity を `doubleNormalizedQCandidate` そのもので書く。 -/
theorem modulus_mul_doubleNormalizedQCandidate_eq_masterRight'
    (P : AttachedSharedCostPair)
    (D0 D1 : ℤ)
    (hCost0 : P.cost0 = P.gap - D0)
    (hCost1 : P.cost1 = P.gap - D1) :
    P.modulus * P.doubleNormalizedQCandidate D0 D1 =
      P.gap * (P.deltaSum - P.representativeThreshold) +
        (P.affineB + P.weight0 + P.weight1) := by
  simpa [doubleNormalizedQCandidate] using
    P.modulus_mul_doubleNormalizedQCandidate_eq_masterRight
      D0 D1 hCost0 hCost1

/--
representative threshold が成立すれば、
二重 predecessor の normalized defect 候補は strict positive。
-/
theorem doubleNormalizedQCandidate_pos_of_threshold_le
    (P : AttachedSharedCostPair)
    (D0 D1 : ℤ)
    (hCost0 : P.cost0 = P.gap - D0)
    (hCost1 : P.cost1 = P.gap - D1)
    (hThreshold :
      P.representativeThreshold ≤ P.deltaSum) :
    0 < P.doubleNormalizedQCandidate D0 D1 := by
  have h :=
    P.defectSum_lt_gap_add_normalizedQ_of_threshold_le
      D0 D1 hCost0 hCost1 hThreshold
  unfold doubleNormalizedQCandidate
  linarith

/--
strict two-band bound から、元の non-strict 目標を取り出す wrapper。
-/
theorem defectSum_le_gap_add_normalizedQ_of_threshold_le
    (P : AttachedSharedCostPair)
    (D0 D1 : ℤ)
    (hCost0 : P.cost0 = P.gap - D0)
    (hCost1 : P.cost1 = P.gap - D1)
    (hThreshold :
      P.representativeThreshold ≤ P.deltaSum) :
    D0 + D1 ≤ P.gap + P.normalizedQ := by
  exact le_of_lt
    (P.defectSum_lt_gap_add_normalizedQ_of_threshold_le
      D0 D1 hCost0 hCost1 hThreshold)

end AttachedSharedCostPair

end MultiCorner
end CSTMicro
end Collatz2
