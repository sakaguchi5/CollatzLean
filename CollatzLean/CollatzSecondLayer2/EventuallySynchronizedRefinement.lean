import CollatzLean.CollatzSecondLayer2.NormalizationRefinementObjects

/-!
# eventual synchronizationからone-sided meanderへ

標準normalization towerのeventual-sync項では、十分後の各q-windowがsynchronizedとなる。
したがって指数tailはq周期になる。

同期開始後に値が`q * 3^q`を超えるfuture-minimumを一つ選ぶ。そこでmeanderでなければ
first crossingが存在するが、q周期性によりその長さはq以下でなければならない。
一方、future-minimumから始まる長さq以下のfirst crossingは開始値を`q * 3^q`以下に
抑えるため矛盾する。

このファイルで`EventuallySynchronizedTowerToMeanderPrinciple`を実定理として閉じる。
-/

namespace CollatzSecondLayer2

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

namespace ExpWord

/-- 二つの膨張語を連結しても膨張する。 -/
theorem expanding_append
    {u v : ExpWord}
    (hu : Expanding u)
    (hv : Expanding v) :
    Expanding (u ++ v) := by
  unfold Expanding at hu hv ⊢
  rw [twoSteps_append, oddSteps_append, pow_add, pow_add]
  exact Nat.mul_lt_mul_of_lt_of_lt hu hv

end ExpWord

namespace OddOrbit

/--
指数列がanchor以後q周期なら、任意の有限segmentもqだけ平行移動して一致する。
-/
theorem segmentWord_add_period_eq
    (O : OddOrbit)
    {anchor q : ℕ}
    (hperiod : ∀ t : ℕ,
      O.exponent (anchor + t + q) =
        O.exponent (anchor + t)) :
    ∀ t m : ℕ,
      O.segmentWord (anchor + t + q) m =
        O.segmentWord (anchor + t) m := by
  intro t m
  induction m generalizing t with
  | zero =>
      simp
  | succ m ih =>
      simp only [segmentWord_succ]
      rw [hperiod t]
      have htail := ih (t + 1)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail

end OddOrbit

/--
q周期指数tail上のfirst crossingは、一周期q以内に起きなければならない。

仮にp>qなら、長さqのprefixと長さp-qのprefixはどちらもproper prefixなので膨張する。
周期性により後半segmentは長さp-qのprefixと同じ語であり、全語も膨張してしまう。
-/
theorem firstCrossing_length_le_of_exponent_period
    {O : OddOrbit} {anchor q p : ℕ}
    (hq : 0 < q)
    (hperiod : ∀ t : ℕ,
      O.exponent (anchor + t + q) =
        O.exponent (anchor + t))
    (hC : FirstCrossingAt O anchor p) :
    p ≤ q := by
  by_contra hnot
  have hqp : q < p := Nat.lt_of_not_ge hnot
  have hqExpanding :
      Expanding (O.segmentWord anchor q) := by
    have hprefix :=
      hC.properExpanding q hq (by simpa using hqp)
    rw [O.segmentWord_take_of_le hqp.le] at hprefix
    exact hprefix
  have hrestPos : 0 < p - q :=
    Nat.sub_pos_of_lt hqp
  have hrestLt : p - q < p := by
    exact Nat.sub_lt (Nat.zero_lt_of_lt hqp) hq
  have hrestExpanding :
      Expanding (O.segmentWord anchor (p - q)) := by
    have hprefix :=
      hC.properExpanding
        (p - q) hrestPos (by simpa using hrestLt)
    rw [O.segmentWord_take_of_le hrestLt.le] at hprefix
    exact hprefix
  have hshift :
      O.segmentWord (anchor + q) (p - q) =
        O.segmentWord anchor (p - q) := by
    simpa using O.segmentWord_add_period_eq hperiod 0 (p - q)
  have hsuffixExpanding :
      Expanding (O.segmentWord (anchor + q) (p - q)) := by
    rw [hshift]
    exact hrestExpanding
  have hsum : q + (p - q) = p := by
    omega
  have hdecomp :
      O.segmentWord anchor p =
        O.segmentWord anchor q ++
          O.segmentWord (anchor + q) (p - q) := by
    simpa [hsum] using O.segmentWord_add anchor q (p - q)
  have hfullExpanding :
      Expanding (O.segmentWord anchor p) := by
    rw [hdecomp]
    exact ExpWord.expanding_append
      hqExpanding hsuffixExpanding
  exact
    (Nat.not_lt_of_ge hC.terminalContracting.le)
      hfullExpanding

/--
十分大きいfuture-minimumから始まるq周期指数tailはone-sided meanderである。
-/
theorem meanderAt_of_exponent_period_of_large_futureMinimum
    {O : OddOrbit} {anchor q : ℕ}
    (hq : 0 < q)
    (hmin : O.FutureMinimumAt anchor)
    (hlarge : q * 3 ^ q < O.value anchor)
    (hperiod : ∀ t : ℕ,
      O.exponent (anchor + t + q) =
        O.exponent (anchor + t)) :
    MeanderAt O anchor := by
  rcases meander_or_firstCrossing_at O anchor with hM | hC
  · exact hM
  · rcases hC with ⟨p, hp⟩
    have hpq : p ≤ q :=
      firstCrossing_length_le_of_exponent_period
        hq hperiod hp
    have hbound : O.value anchor ≤ q * 3 ^ q :=
      futureMinimum_start_le_of_crossingLength_le
        hmin hp hpq
    exact False.elim (Nat.not_lt_of_ge hbound hlarge)

namespace OddOrbit.InfiniteCaptureNormalizationData

/--
eventual synchronization開始後では、指数列はwindow長qを周期に持つ。
-/
theorem exponent_period_at_synchronizedTail
    {O : OddOrbit} {start q : ℕ}
    {D₀ : O.WindowDifferenceData start q}
    (I : O.InfiniteCaptureNormalizationData D₀) :
    ∀ t : ℕ,
      O.exponent
          (start + I.synchronizationStart + t + q) =
        O.exponent
          (start + I.synchronizationStart + t) := by
  intro t
  have S :=
    I.eventuallySynchronized
      (I.synchronizationStart + t)
      (by omega)
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    S.upperExponent_eq_lower

end OddOrbit.InfiniteCaptureNormalizationData

namespace EventuallySynchronizedNormalizationTowerData

/--
eventual-sync towerの一項だけからactual anchored one-sided meanderを構成する。
-/
noncomputable def toAnchoredOneSidedMeanderData
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    (T : EventuallySynchronizedNormalizationTowerData D) :
    AnchoredOneSidedMeanderData O := by
  classical
  let n : ℕ := D.source.select (T.select 0)
  let P : PolynomialPreparedFullWindowFamily D.crossing :=
    polynomialPreparedFullWindowFamily hGap D.crossing
  let start : ℕ :=
    D.crossing.minima.index n + P.offset n
  let q : ℕ := D.crossing.crossingLength n
  let I := T.data 0
  let synchronizedStart : ℕ :=
    start + I.synchronizationStart
  have hq : 0 < q := by
    simpa [q, n] using
      (D.crossing.crossing n).length_pos
  have hperiodStart :
      ∀ t : ℕ,
        O.exponent (synchronizedStart + t + q) =
          O.exponent (synchronizedStart + t) := by
    intro t
    have h := I.exponent_period_at_synchronizedTail t
    simpa [
      synchronizedStart,
      start,
      q,
      P,
      n,
      Nat.add_assoc,
      Nat.add_comm,
      Nat.add_left_comm
    ] using h
  let M : ℕ := q * 3 ^ q
  let hEscape :=
    O.escapesToInfinity_of_unbounded
      D.crossing.unbounded M
  let N : ℕ := Classical.choose hEscape
  have hN :
      ∀ m : ℕ, N ≤ m → M < O.value m :=
    Classical.choose_spec hEscape
  let threshold : ℕ := max synchronizedStart N
  let anchor : ℕ := O.tailMinIndex threshold
  have hthresholdAnchor : threshold ≤ anchor := by
    simp only [OddOrbit.tailMinIndex_ge, anchor]
  have hsynchronizedStartAnchor : synchronizedStart ≤ anchor := by
    exact le_trans (Nat.le_max_left _ _) hthresholdAnchor
  have hNAnchor : N ≤ anchor := by
    exact le_trans (Nat.le_max_right _ _) hthresholdAnchor
  have hlarge : q * 3 ^ q < O.value anchor := by
    simpa [M] using hN anchor hNAnchor
  have hfutureMinimum : O.FutureMinimumAt anchor := by
    simpa [anchor] using
      O.futureMinimumAt_tailMinIndex threshold
  have hperiodAnchor :
      ∀ t : ℕ,
        O.exponent (anchor + t + q) =
          O.exponent (anchor + t) := by
    intro t
    have h :=
      hperiodStart (anchor - synchronizedStart + t)
    have hbase :
        synchronizedStart + (anchor - synchronizedStart) =
          anchor := by
      rw [Nat.add_comm]
      exact Nat.sub_add_cancel hsynchronizedStartAnchor
    have hshift :
        synchronizedStart +
            (anchor - synchronizedStart + t) =
          anchor + t := by
      rw [← Nat.add_assoc, hbase]
    rw [hshift] at h
    exact h
  exact
    { unbounded := D.crossing.unbounded
      anchor := anchor
      futureMinimum := hfutureMinimum
      meander :=
        meanderAt_of_exponent_period_of_large_futureMinimum
          hq hfutureMinimum hlarge hperiodAnchor }

end EventuallySynchronizedNormalizationTowerData

/-- eventual-sync towerからactual anchored meanderを得る実定理。 -/
theorem eventuallySynchronizedTower_to_meander
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    (T : EventuallySynchronizedNormalizationTowerData D) :
    Nonempty (AnchoredOneSidedMeanderData O) :=
  ⟨T.toAnchoredOneSidedMeanderData⟩

/-- eventual-sync towerをmeanderへ送る命題のまとめ。 -/
def EventuallySynchronizedTowerToMeanderPrinciple : Prop :=
  ∀ (hGap : TwoThreeGapPolynomialBound) (O : OddOrbit),
    ∀ D : StandardNormalizationGeneratedObstructionTowerData hGap O,
      EventuallySynchronizedNormalizationTowerData D →
        Nonempty (AnchoredOneSidedMeanderData O)

/-- `EventuallySynchronizedTowerToMeanderPrinciple`は実際に成立する。 -/
theorem eventuallySynchronizedTowerToMeanderPrinciple :
    EventuallySynchronizedTowerToMeanderPrinciple := by
  intro hGap O D T
  exact eventuallySynchronizedTower_to_meander T

end CollatzSecondLayer2
