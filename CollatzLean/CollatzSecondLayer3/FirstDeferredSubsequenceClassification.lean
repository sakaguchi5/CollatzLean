import CollatzLean.CollatzSecondLayer3.LongPlateauRefinement

/-!
# first-deferred towerの無限部分列分類

terminal endpointが固定多項式以下となる部分列がpersistentならPolynomial terminalへ、
そうでなければterminal endpointは全固定多項式を最終的に超える。そのtailで
critical captureがpersistentならcritical capture towerへ、そうでなければ
super-polynomial no-critical towerへ進む。

この無条件部分列分類と前三ファイルの局所定理を組み合わせ、
first-deferred towerをPolynomial Special C3 / critical capture / long plateauへ
実際にrefineする。
-/

namespace CollatzSecondLayer2

/-- Propが任意に遠い添字で成立すること。 -/
def Persistently (P : ℕ → Prop) : Prop :=
  ∀ N : ℕ, ∃ j : ℕ, N ≤ j ∧ P j

namespace Persistently

/-- persistentなPropを満たす添字を狭義単調に選ぶ。 -/
noncomputable def select
    (P : ℕ → Prop)
    (h : Persistently P) : ℕ → ℕ
  | 0 => Classical.choose (h 0)
  | n + 1 => Classical.choose (h (select P h n + 1))

/-- 選択添字は要求下限以上。 -/
theorem select_ge
    (P : ℕ → Prop)
    (h : Persistently P) :
    ∀ n : ℕ, n ≤ select P h n := by
  intro n
  induction n with
  | zero => omega
  | succ n ih =>
      have hs := Classical.choose_spec (h (select P h n + 1))
      have hstep : select P h n + 1 ≤ select P h (n + 1) := by
        simpa [select] using hs.1
      omega

/-- 選択列は狭義単調。 -/
theorem select_strict
    (P : ℕ → Prop)
    (h : Persistently P) :
    StrictMono (select P h) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hs := Classical.choose_spec (h (select P h n + 1))
  have hstep : select P h n + 1 ≤ select P h (n + 1) := by
    simpa [select] using hs.1
  omega

/-- 選択添字ではPropが成立する。 -/
theorem select_spec
    (P : ℕ → Prop)
    (h : Persistently P)
    (n : ℕ) :
    P (select P h n) := by
  cases n with
  | zero =>
      simpa [select] using (Classical.choose_spec (h 0)).2
  | succ n =>
      simpa [select] using
        (Classical.choose_spec (h (select P h n + 1))).2

/-- persistentでなければ十分後にPropは成立しない。 -/
theorem eventually_not_of_not
    (P : ℕ → Prop)
    (h : ¬ Persistently P) :
    ∃ N : ℕ, ∀ j : ℕ, N ≤ j → ¬ P j := by
  unfold Persistently at h
  push Not at h
  exact h

end Persistently

/-- terminal endpointがある固定多項式以下となる項がpersistentに現れること。 -/
def HasPersistentPolynomialTerminalBound
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    (T : FirstDeferredNormalizationTowerData D) : Prop :=
  ∃ K A : ℕ,
    Persistently (fun j =>
      T.terminalEndpoint j ≤ K * (T.windowLength j + 1) ^ A)

/-- critical captureを持つ項がpersistentに現れること。 -/
def HasPersistentCriticalCapture
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    (T : FirstDeferredNormalizationTowerData D) : Prop :=
  Persistently (fun j =>
    Nonempty (CriticalCaptureInFirstDeferred (T.data j)))

/-- persistent polynomial terminalから対応する部分towerを構成する。 -/
noncomputable def polynomialTerminalTowerOfPersistent
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    (T : FirstDeferredNormalizationTowerData D)
    (h : HasPersistentPolynomialTerminalBound T) :
    PolynomialTerminalFirstDeferredTowerData T := by
  classical
  let K := Classical.choose h
  let hA := Classical.choose_spec h
  let A := Classical.choose hA
  let hPersistent := Classical.choose_spec hA
  let P : ℕ → Prop := fun j =>
    T.terminalEndpoint j ≤ K * (T.windowLength j + 1) ^ A
  exact
    { select := Persistently.select P hPersistent
      select_strict := Persistently.select_strict P hPersistent
      K := K
      A := A
      endpointBound := by
        intro j
        exact Persistently.select_spec P hPersistent j }

/-- persistent critical captureからcritical capture towerを構成する。 -/
noncomputable def criticalCaptureTowerOfPersistent
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    (T : FirstDeferredNormalizationTowerData D)
    (h : HasPersistentCriticalCapture T) :
    CriticalCaptureTowerData hGap O := by
  classical
  let P : ℕ → Prop := fun j =>
    Nonempty (CriticalCaptureInFirstDeferred (T.data j))
  exact
    { source := D
      firstDeferred := T
      select := Persistently.select P h
      select_strict := Persistently.select_strict P h
      certificate := by
        intro j
        exact Classical.choice (Persistently.select_spec P h j) }

/-- polynomial terminalがpersistentでなければterminal endpointは全固定多項式を超える。 -/
theorem terminalSuperPolynomial_of_not_persistent
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    (T : FirstDeferredNormalizationTowerData D)
    (h : ¬ HasPersistentPolynomialTerminalBound T) :
    ∀ K A : ℕ, ∃ N : ℕ, ∀ j : ℕ, N ≤ j →
      K * (T.windowLength j + 1) ^ A < T.terminalEndpoint j := by
  intro K A
  unfold HasPersistentPolynomialTerminalBound Persistently at h
  push Not at h
  obtain ⟨N, hN⟩ := h K A
  refine ⟨N, ?_⟩
  intro j hj
  have hnot := hN j hj
  omega

/--
critical captureが十分後に存在しないなら、
その開始位置からのshift列はすべてno-critical。
-/
theorem shifted_noCritical_of_eventually_noCritical
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    (T : FirstDeferredNormalizationTowerData D)
    (N : ℕ)
    (hN :
      ∀ j : ℕ, N ≤ j →
        ¬ Nonempty
          (CriticalCaptureInFirstDeferred (T.data j))) :
    ∀ j : ℕ,
      NoCriticalCaptureInFirstDeferred
        (T.data (N + j)) := by
  intro j
  have hNo :
      ¬ Nonempty
        (CriticalCaptureInFirstDeferred
          (T.data (N + j))) := by
    apply hN
    omega
  simpa [NoCriticalCaptureInFirstDeferred] using hNo

/--
terminal endpointが全固定多項式を十分後に上回るなら、
さらに固定shiftした部分列でも同じsuper-polynomial性を持つ。
-/
theorem shifted_terminalSuperPolynomial_of_not_persistent
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    (T : FirstDeferredNormalizationTowerData D)
    (hPolynomial :
      ¬ HasPersistentPolynomialTerminalBound T)
    (Nshift : ℕ) :
    ∀ K A : ℕ,
      ∃ N : ℕ, ∀ j : ℕ, N ≤ j →
        K * (T.windowLength (Nshift + j) + 1) ^ A <
          T.terminalEndpoint (Nshift + j) := by
  intro K A
  obtain ⟨Npoly, hNpoly⟩ :=
    CollatzSecondLayer2.terminalSuperPolynomial_of_not_persistent
      T hPolynomial K A
  refine ⟨Npoly, ?_⟩
  intro j hj
  apply hNpoly (Nshift + j)
  omega

/--
polynomial terminalもpersistent critical captureもなければ、tailは
super-polynomialかつno-criticalとなる。
-/
noncomputable def superPolynomialNoCriticalOfExclusions
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    (T : FirstDeferredNormalizationTowerData D)
    (hPolynomial :
      ¬ HasPersistentPolynomialTerminalBound T)
    (hCritical :
      ¬ HasPersistentCriticalCapture T) :
    SuperPolynomialNoCriticalFirstDeferredTowerData T := by
  classical
  let P : ℕ → Prop := fun j =>
    Nonempty
      (CriticalCaptureInFirstDeferred (T.data j))
  have hEventuallyNoCritical :
      ∃ N : ℕ, ∀ j : ℕ, N ≤ j → ¬ P j := by
    exact
      Persistently.eventually_not_of_not
        P hCritical
  let Ncritical : ℕ :=
    Classical.choose hEventuallyNoCritical
  have hNcritical :
      ∀ j : ℕ, Ncritical ≤ j → ¬ P j :=
    Classical.choose_spec hEventuallyNoCritical
  let select : ℕ → ℕ :=
    fun j => Ncritical + j
  refine
    { select := select
      select_strict := ?_
      noCritical := ?_
      terminalSuperPolynomial := ?_ }
  · intro a b hab
    dsimp [select]
    exact Nat.add_lt_add_left hab Ncritical
  · simpa [select, P] using
      shifted_noCritical_of_eventually_noCritical
        T Ncritical hNcritical
  · simpa [select] using
      shifted_terminalSuperPolynomial_of_not_persistent
        T hPolynomial Ncritical

/-- first-deferred towerの三種類の無条件部分列分類。 -/
theorem firstDeferred_subsequence_classification
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    (T : FirstDeferredNormalizationTowerData D) :
    Nonempty (PolynomialTerminalFirstDeferredTowerData T) ∨
      Nonempty (CriticalCaptureTowerData hGap O) ∨
      Nonempty (SuperPolynomialNoCriticalFirstDeferredTowerData T) := by
  classical
  by_cases hPolynomial : HasPersistentPolynomialTerminalBound T
  · exact Or.inl ⟨polynomialTerminalTowerOfPersistent T hPolynomial⟩
  · by_cases hCritical : HasPersistentCriticalCapture T
    · exact Or.inr (Or.inl
        ⟨criticalCaptureTowerOfPersistent T hCritical⟩)
    · exact Or.inr (Or.inr
        ⟨superPolynomialNoCriticalOfExclusions
          T hPolynomial hCritical⟩)

end CollatzSecondLayer2
