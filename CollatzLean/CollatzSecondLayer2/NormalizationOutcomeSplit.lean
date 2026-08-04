import CollatzLean.CollatzSecondLayer2.NormalizationRefinementFacts

/-!
# normalization towerの無条件outcome分解

標準構成由来normalization towerの各項は、既に

* first deferredを持つ有限normalization
* deferredなしのeventual synchronization

のどちらかである。この有限二分岐を無限部分列へ持ち上げ、由来を失わない
二種類のtowerへ無条件に分解する。
-/

namespace CollatzSecondLayer2

/-- 狭義単調な自然数列は各添字以上に進む。 -/
private theorem strictMono_index_le
    (f : ℕ → ℕ)
    (hf : StrictMono f) :
    ∀ n : ℕ, n ≤ f n := by
  intro n
  induction n with
  | zero => omega
  | succ n ih =>
      have hstep : f n < f (n + 1) :=
        hf (Nat.lt_succ_self n)
      omega

namespace StandardNormalizationGeneratedObstructionTowerData

/-- 第`j`項のnormalization outcomeがfirst deferredであること。 -/
def IsFirstDeferred
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (D : StandardNormalizationGeneratedObstructionTowerData hGap O)
    (j : ℕ) : Prop :=
  match D.source.normalization j with
  | .firstDeferred _ => True
  | .eventuallySynchronized _ => False

/-- 第`j`項のnormalization outcomeがeventual synchronizationであること。 -/
def IsEventuallySynchronized
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (D : StandardNormalizationGeneratedObstructionTowerData hGap O)
    (j : ℕ) : Prop :=
  match D.source.normalization j with
  | .firstDeferred _ => False
  | .eventuallySynchronized _ => True

/-- 各項はfirst deferredまたはeventual synchronization。 -/
theorem normalizationKind_complete
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (D : StandardNormalizationGeneratedObstructionTowerData hGap O)
    (j : ℕ) :
    D.IsFirstDeferred j ∨ D.IsEventuallySynchronized j := by
  cases h : D.source.normalization j with
  | firstDeferred F =>
      exact Or.inl (by simp [IsFirstDeferred, h])
  | eventuallySynchronized I =>
      exact Or.inr (by simp [IsEventuallySynchronized, h])

/-- 二つのoutcomeは同時には成立しない。 -/
theorem normalizationKind_disjoint
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (D : StandardNormalizationGeneratedObstructionTowerData hGap O)
    (j : ℕ) :
    ¬ (D.IsFirstDeferred j ∧ D.IsEventuallySynchronized j) := by
  intro hboth
  cases h : D.source.normalization j with
  | firstDeferred F =>
      simpa [IsEventuallySynchronized, h] using hboth.2
  | eventuallySynchronized I =>
      simpa [IsFirstDeferred, h] using hboth.1

/-- first-deferred証明から実際の有限normalizationを取り出す。 -/
noncomputable def firstDeferredData
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (D : StandardNormalizationGeneratedObstructionTowerData hGap O)
    (j : ℕ)
    (h : D.IsFirstDeferred j) :
    O.FiniteCaptureNormalizationData
      ((polynomialPreparedFullWindowFamily hGap D.crossing).packet
        (D.source.select j)).toWindowDifferenceData := by
  cases hn : D.source.normalization j with
  | firstDeferred F => exact F
  | eventuallySynchronized I =>
      simp [IsFirstDeferred, hn] at h

/-- eventual-sync証明から実際の無限normalizationを取り出す。 -/
noncomputable def eventuallySynchronizedData
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (D : StandardNormalizationGeneratedObstructionTowerData hGap O)
    (j : ℕ)
    (h : D.IsEventuallySynchronized j) :
    O.InfiniteCaptureNormalizationData
      ((polynomialPreparedFullWindowFamily hGap D.crossing).packet
        (D.source.select j)).toWindowDifferenceData := by
  cases hn : D.source.normalization j with
  | firstDeferred F =>
      simp [IsEventuallySynchronized, hn] at h
  | eventuallySynchronized I => exact I

/-- first deferred項が任意に遠く現れること。 -/
def HasPersistentFirstDeferred
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (D : StandardNormalizationGeneratedObstructionTowerData hGap O) : Prop :=
  ∀ N : ℕ, ∃ j : ℕ, N ≤ j ∧ D.IsFirstDeferred j

/-- persistent first-deferred位置を狭義単調に選ぶ。 -/
noncomputable def persistentFirstDeferredSelect
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (D : StandardNormalizationGeneratedObstructionTowerData hGap O)
    (h : D.HasPersistentFirstDeferred) : ℕ → ℕ
  | 0 => Classical.choose (h 0)
  | n + 1 =>
      Classical.choose (h (D.persistentFirstDeferredSelect h n + 1))

/-- 選択位置は要求下限以上。 -/
theorem persistentFirstDeferredSelect_ge
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (D : StandardNormalizationGeneratedObstructionTowerData hGap O)
    (h : D.HasPersistentFirstDeferred) :
    ∀ n : ℕ, n ≤ D.persistentFirstDeferredSelect h n := by
  intro n
  induction n with
  | zero => omega
  | succ n ih =>
      have hs := Classical.choose_spec
        (h (D.persistentFirstDeferredSelect h n + 1))
      have hstep :
          D.persistentFirstDeferredSelect h n + 1 ≤
            D.persistentFirstDeferredSelect h (n + 1) := by
        simpa [persistentFirstDeferredSelect] using hs.1
      omega

/-- first-deferred選択列は狭義単調。 -/
theorem persistentFirstDeferredSelect_strict
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (D : StandardNormalizationGeneratedObstructionTowerData hGap O)
    (h : D.HasPersistentFirstDeferred) :
    StrictMono (D.persistentFirstDeferredSelect h) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hs := Classical.choose_spec
    (h (D.persistentFirstDeferredSelect h n + 1))
  have hstep :
      D.persistentFirstDeferredSelect h n + 1 ≤
        D.persistentFirstDeferredSelect h (n + 1) := by
    simpa [persistentFirstDeferredSelect] using hs.1
  omega

/-- 選択した各項はfirst deferred。 -/
theorem persistentFirstDeferredSelect_spec
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (D : StandardNormalizationGeneratedObstructionTowerData hGap O)
    (h : D.HasPersistentFirstDeferred)
    (n : ℕ) :
    D.IsFirstDeferred (D.persistentFirstDeferredSelect h n) := by
  cases n with
  | zero =>
      simpa [persistentFirstDeferredSelect] using
        (Classical.choose_spec (h 0)).2
  | succ n =>
      simpa [persistentFirstDeferredSelect] using
        (Classical.choose_spec
          (h (D.persistentFirstDeferredSelect h n + 1))).2

end StandardNormalizationGeneratedObstructionTowerData

/-- first-deferred outcomeだけを保持する無限部分tower。 -/
structure FirstDeferredNormalizationTowerData
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (D : StandardNormalizationGeneratedObstructionTowerData hGap O) where
  select : ℕ → ℕ
  select_strict : StrictMono select
  firstDeferred : ∀ j : ℕ, D.IsFirstDeferred (select j)

namespace FirstDeferredNormalizationTowerData

/-- 第`j`項の実際の有限normalization。 -/
noncomputable def data
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    (T : FirstDeferredNormalizationTowerData D)
    (j : ℕ) :=
  D.firstDeferredData (T.select j) (T.firstDeferred j)

/-- 選択後もwindow長は無限大へ進む。 -/
theorem lengths_tend_to_infinity
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    (T : FirstDeferredNormalizationTowerData D) :
    ∀ M : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      M < D.windowLength (T.select j) := by
  intro M
  obtain ⟨J, hJ⟩ := D.lengths_tend_to_infinity M
  refine ⟨J, ?_⟩
  intro j hj
  apply hJ (T.select j)
  have hsel : j ≤ T.select j := strictMono_index_le T.select T.select_strict j
  exact le_trans hj hsel

end FirstDeferredNormalizationTowerData

/-- eventual-sync outcomeだけを保持する無限部分tower。 -/
structure EventuallySynchronizedNormalizationTowerData
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (D : StandardNormalizationGeneratedObstructionTowerData hGap O) where
  select : ℕ → ℕ
  select_strict : StrictMono select
  eventuallySynchronized :
    ∀ j : ℕ, D.IsEventuallySynchronized (select j)

namespace EventuallySynchronizedNormalizationTowerData

/-- 第`j`項の実際の無限eventual-sync normalization。 -/
noncomputable def data
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    (T : EventuallySynchronizedNormalizationTowerData D)
    (j : ℕ) :=
  D.eventuallySynchronizedData
    (T.select j) (T.eventuallySynchronized j)

/-- 選択後もwindow長は無限大へ進む。 -/
theorem lengths_tend_to_infinity
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    (T : EventuallySynchronizedNormalizationTowerData D) :
    ∀ M : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      M < D.windowLength (T.select j) := by
  intro M
  obtain ⟨J, hJ⟩ := D.lengths_tend_to_infinity M
  refine ⟨J, ?_⟩
  intro j hj
  apply hJ (T.select j)
  have hsel : j ≤ T.select j := strictMono_index_le T.select T.select_strict j
  exact le_trans hj hsel

end EventuallySynchronizedNormalizationTowerData

/--
標準normalization towerは、first-deferred towerまたはeventual-sync towerへ
無条件に分解できる。
-/
theorem standardNormalization_outcomeTower_dichotomy
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (D : StandardNormalizationGeneratedObstructionTowerData hGap O) :
    Nonempty (FirstDeferredNormalizationTowerData D) ∨
      Nonempty (EventuallySynchronizedNormalizationTowerData D) := by
  classical
  by_cases hPersistent : D.HasPersistentFirstDeferred
  · exact Or.inl
      ⟨{
        select := D.persistentFirstDeferredSelect hPersistent
        select_strict := D.persistentFirstDeferredSelect_strict hPersistent
        firstDeferred := D.persistentFirstDeferredSelect_spec hPersistent
      }⟩
  · unfold StandardNormalizationGeneratedObstructionTowerData.HasPersistentFirstDeferred
      at hPersistent
    push Not at hPersistent
    obtain ⟨N, hN⟩ := hPersistent
    let select : ℕ → ℕ := fun j => N + j
    have hstrict : StrictMono select := by
      intro a b hab
      exact Nat.add_lt_add_left hab N
    have hsync : ∀ j : ℕ, D.IsEventuallySynchronized (select j) := by
      intro j
      rcases D.normalizationKind_complete (select j) with hF | hI
      · exact False.elim ((hN (select j) (by dsimp [select]; omega)) hF)
      · exact hI
    exact Or.inr
      ⟨{
        select := select
        select_strict := hstrict
        eventuallySynchronized := hsync
      }⟩

end CollatzSecondLayer2
