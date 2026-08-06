import CollatzLean.CollatzSecondLayer3.PolynomialTerminalRefinement
import Mathlib.Data.Finset.Basic

/-!
# critical captureがない有限normalizationのcapture数評価

軌道上のcapture時刻とprefix capture数を一般的な統計として定義する。

有限normalizationについて、terminal以前の各時刻を
captureまたはsynchronizedへ分類し、window総指数をpotentialとして

`windowTwoSteps(t) + captureCountBefore(t) ≤ windowTwoSteps(0)`

を証明する。

critical shellを横断するcaptureがなければ全時刻で収縮側に残るため、
初期critical shell上端と合わせて`2^captureCount < q+1`を得る。
-/

namespace CollatzSecondLayer3

open CollatzSupport
open CollatzExternal
open CollatzCore

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

/-- critical captureを一つも持たない有限normalization。 -/
def NoCriticalCaptureInFirstDeferred
    {O : OddOrbit} {start q : ℕ}
    {D₀ : O.WindowDifferenceData start q}
    (F : O.FiniteCaptureNormalizationData D₀) : Prop :=
  ¬ Nonempty (CriticalCaptureInFirstDeferred F)

/-!
## 第一層：軌道上のcapture時刻とprefix capture数

この層の定義は、有限normalizationの選択やterminal時刻には依存しない。
`O`、開始位置`start`、window長`q`だけで決まる軌道上の統計である。
-/

namespace OddOrbit

/-- 開始位置から時刻`t`より前に現れるq-window capture時刻の有限集合。 -/
noncomputable def windowCaptureTimesBefore
    (O : OddOrbit)
    (start q t : ℕ) : Finset ℕ := by
  classical
  exact
    (Finset.range t).filter
      (fun k =>
        Nonempty (O.CapturedWindowAt (start + k) q))

/-- 開始位置から時刻`t`より前に現れるq-window capture数。 -/
noncomputable def windowCaptureCountBefore
    (O : OddOrbit)
    (start q t : ℕ) : ℕ :=
  (windowCaptureTimesBefore O start q t).card

@[simp]
theorem windowCaptureCountBefore_zero
    (O : OddOrbit)
    (start q : ℕ) :
    windowCaptureCountBefore O start q 0 = 0 := by
  simp [
    windowCaptureCountBefore,
    windowCaptureTimesBefore
  ]

/-- capture時刻ではprefix capture数が一つ増える。 -/
theorem windowCaptureCountBefore_succ_of_captured
    (O : OddOrbit)
    (start q t : ℕ)
    (h : Nonempty (O.CapturedWindowAt (start + t) q)) :
    windowCaptureCountBefore O start q (t + 1) =
      windowCaptureCountBefore O start q t + 1 := by
  classical
  unfold windowCaptureCountBefore
  unfold windowCaptureTimesBefore
  rw [Finset.range_add_one]
  have ht : t ∉ Finset.range t := by
    simp
  rw [Finset.filter_insert]
  simp [ht, h]


/-- 非capture時刻ではprefix capture数は変化しない。 -/
theorem windowCaptureCountBefore_succ_of_not_captured
    (O : OddOrbit)
    (start q t : ℕ)
    (h : ¬ Nonempty (O.CapturedWindowAt (start + t) q)) :
    windowCaptureCountBefore O start q (t + 1) =
      windowCaptureCountBefore O start q t := by
  classical
  unfold windowCaptureCountBefore
  unfold windowCaptureTimesBefore
  rw [Finset.range_add_one]
  rw [Finset.filter_insert]
  simp [h]

/-- prefix capture数は一段非減少。 -/
theorem windowCaptureCountBefore_le_succ
    (O : OddOrbit)
    (start q t : ℕ) :
    windowCaptureCountBefore O start q t ≤
      windowCaptureCountBefore O start q (t + 1) := by
  classical
  by_cases h :
      Nonempty (O.CapturedWindowAt (start + t) q)
  · rw [
      windowCaptureCountBefore_succ_of_captured O
        start q t h
    ]
    omega
  · rw [
      windowCaptureCountBefore_succ_of_not_captured O
        start q t h
    ]

/-- prefix capture数は時刻添字に関して単調。 -/
theorem windowCaptureCountBefore_mono
    (O : OddOrbit)
    (start q : ℕ)
    {a b : ℕ}
    (hab : a ≤ b) :
    windowCaptureCountBefore O start q a ≤
      windowCaptureCountBefore O start q b := by
  classical
  apply Finset.card_le_card
  intro k hk
  simp only [
    windowCaptureTimesBefore,
    Finset.mem_filter,
    Finset.mem_range
  ] at hk ⊢
  exact ⟨lt_of_lt_of_le hk.1 hab, hk.2⟩

/--
区間`[a,b)`内に一つcaptureがあれば、
時刻`b`までにprefix capture数は少なくとも一つ増える。
-/
theorem windowCaptureCountBefore_add_one_le_of_captured
    (O : OddOrbit)
    (start q : ℕ)
    {a k b : ℕ}
    (hak : a ≤ k)
    (hkb : k < b)
    (hcap : Nonempty (O.CapturedWindowAt (start + k) q)) :
    windowCaptureCountBefore O start q a + 1 ≤
      windowCaptureCountBefore O start q b := by
  have hleft :=
    windowCaptureCountBefore_mono O start q hak
  have hstep :=
    windowCaptureCountBefore_succ_of_captured O
      start q k hcap
  have hright :=
    windowCaptureCountBefore_mono O
      start q
      (show k + 1 ≤ b by omega)
  omega

end OddOrbit

/-!
## 第二層：有限normalizationとcapture統計の接続

この層では`FiniteCaptureNormalizationData`が持つ

* terminal時刻
* terminal以前のcapture/synchronized二分岐
* critical capture不在条件

を、第一層の軌道上capture統計と接続する。
-/

namespace OddOrbit.FiniteCaptureNormalizationData

/-- terminal以前の総capture数。 -/
noncomputable def captureCount
    {O : OddOrbit} {start q : ℕ}
    {D₀ : O.WindowDifferenceData start q}
    (F : O.FiniteCaptureNormalizationData D₀) : ℕ :=
  windowCaptureCountBefore O start q F.terminalTime

/-- terminal以前でcaptureでなければsynchronized。 -/
noncomputable def synchronized_of_not_captured
    {O : OddOrbit} {start q : ℕ}
    {D₀ : O.WindowDifferenceData start q}
    (F : O.FiniteCaptureNormalizationData D₀)
    (t : ℕ)
    (ht : t < F.terminalTime)
    (hNo :
      ¬ Nonempty (O.CapturedWindowAt (start + t) q)) :
    O.SynchronizedWindowAt (start + t) q := by
  classical
  let X := Classical.choice (F.before t ht)
  cases X with
  | inl C =>
      exact False.elim (hNo ⟨C⟩)
  | inr S =>
      exact S

/--
任意のterminal以前のprefixで、
現在window総指数とそれまでのcapture数の和は初期値以下。
-/
theorem windowTwoSteps_add_captureCountBefore_le
    {O : OddOrbit} {start q : ℕ}
    {D₀ : O.WindowDifferenceData start q}
    (F : O.FiniteCaptureNormalizationData D₀) :
    ∀ t : ℕ, t ≤ F.terminalTime →
      O.windowTwoSteps (start + t) q +
          windowCaptureCountBefore O start q t ≤
        O.windowTwoSteps start q := by
  intro t ht
  induction t with
  | zero =>
      simp
  | succ t ih =>
      have htlt : t < F.terminalTime := by
        omega
      have hprev := ih (by omega)
      classical
      by_cases hcap :
          Nonempty (O.CapturedWindowAt (start + t) q)
      · rcases hcap with ⟨C⟩
        have hdrop :
            O.windowTwoSteps (start + (t + 1)) q <
              O.windowTwoSteps (start + t) q := by
          simpa [Nat.add_assoc] using
            C.windowTwoSteps_strict_decrease
        have hcount :=
          windowCaptureCountBefore_succ_of_captured O
            start q t ⟨C⟩
        omega
      · let S :=
          synchronized_of_not_captured F
            t htlt hcap
        have heq :
            O.windowTwoSteps (start + (t + 1)) q =
              O.windowTwoSteps (start + t) q := by
          simpa [Nat.add_assoc] using
            S.windowTwoSteps_eq
        have hcount :=
          windowCaptureCountBefore_succ_of_not_captured O
            start q t hcap
        omega

/--
初期windowが収縮側で、critical captureがなければ
terminalまで収縮側に残る。
-/
theorem contracting_at_of_noCritical
    {O : OddOrbit} {start q : ℕ}
    {D₀ : O.WindowDifferenceData start q}
    (F : O.FiniteCaptureNormalizationData D₀)
    (hInitial :
      3 ^ q < 2 ^ O.windowTwoSteps start q)
    (hNoCritical :
      NoCriticalCaptureInFirstDeferred F) :
    ∀ t : ℕ, t ≤ F.terminalTime →
      3 ^ q <
        2 ^ O.windowTwoSteps (start + t) q := by
  intro t ht
  induction t with
  | zero =>
      simpa using hInitial
  | succ t ih =>
      have htlt : t < F.terminalTime := by
        omega
      have hbefore := ih (by omega)
      rcases F.before t htlt with ⟨C | S⟩
      · by_contra hnext
        have hnoncontracting :
            2 ^ O.windowTwoSteps (start + t + 1) q ≤
              3 ^ q :=
          Nat.le_of_not_gt hnext
        apply hNoCritical
        exact ⟨{
          time := t
          time_lt_terminal := htlt
          captured := C
          beforeContracting := by
            simpa [Nat.add_assoc] using hbefore
          afterNoncontracting := by
            simpa [Nat.add_assoc] using hnoncontracting
        }⟩
      · have heq :
            O.windowTwoSteps (start + (t + 1)) q =
              O.windowTwoSteps (start + t) q := by
          simpa [Nat.add_assoc] using
            S.windowTwoSteps_eq
        simpa [heq] using hbefore

/--
critical shell上端とno-critical条件から、
terminal以前のcapture回数の二冪は`q+1`未満。
-/
theorem twoPow_captureCount_lt_succ
    {O : OddOrbit} {start q : ℕ}
    {D₀ : O.WindowDifferenceData start q}
    (F : O.FiniteCaptureNormalizationData D₀)
    (hInitialLower :
      3 ^ q < 2 ^ O.windowTwoSteps start q)
    (hInitialUpper :
      2 ^ O.windowTwoSteps start q ≤
        (q + 1) * 3 ^ q)
    (hNoCritical :
      NoCriticalCaptureInFirstDeferred F) :
    2 ^ captureCount F < q + 1 := by
  let H₀ :=
    O.windowTwoSteps start q
  let H₁ :=
    O.windowTwoSteps
      (start + F.terminalTime) q
  let C :=
    captureCount F
  have hcontract :
      3 ^ q < 2 ^ H₁ := by
    simpa [H₁] using
      contracting_at_of_noCritical F
        hInitialLower
        hNoCritical
        F.terminalTime
        le_rfl
  have hbudget :
      H₁ + C ≤ H₀ := by
    simpa [
      H₀,
      H₁,
      C,
      captureCount
    ] using
      windowTwoSteps_add_captureCountBefore_le F
        F.terminalTime
        le_rfl
  have hpowC :
      0 < 2 ^ C :=
    Nat.pow_pos (by omega)
  have hpow3 :
      0 < 3 ^ q :=
    Nat.pow_pos (by omega)
  have hmul :
      2 ^ C * 3 ^ q <
        (q + 1) * 3 ^ q := by
    calc
      2 ^ C * 3 ^ q
          < 2 ^ C * 2 ^ H₁ :=
        (Nat.mul_lt_mul_left hpowC).2 hcontract
      _ = 2 ^ (C + H₁) := by
        rw [pow_add]
      _ ≤ 2 ^ H₀ := by
        exact
          Nat.pow_le_pow_right
            (by omega)
            (by omega)
      _ ≤ (q + 1) * 3 ^ q :=
        hInitialUpper
  exact
    (Nat.mul_lt_mul_right hpow3).1 hmul

end OddOrbit.FiniteCaptureNormalizationData

namespace FirstDeferredNormalizationTowerData

/-- towerの一項に対するno-critical capture数評価。 -/
theorem twoPow_captureCount_lt_windowLength_succ
    {hGap : TwoThreeGapPolynomialBound}
    {O : OddOrbit}
    {D :
      StandardNormalizationGeneratedObstructionTowerData
        hGap O}
    (T : FirstDeferredNormalizationTowerData D)
    (j : ℕ)
    (hNoCritical :
      NoCriticalCaptureInFirstDeferred (T.data j)) :
    2 ^ OddOrbit.FiniteCaptureNormalizationData.captureCount (T.data j) <
      T.windowLength j + 1 := by
  apply OddOrbit.FiniteCaptureNormalizationData.twoPow_captureCount_lt_succ (T.data j)
  · simpa [
      FirstDeferredNormalizationTowerData.start,
      FirstDeferredNormalizationTowerData.windowLength,
      StandardNormalizationGeneratedObstructionTowerData.start,
      StandardNormalizationGeneratedObstructionTowerData.windowLength,
      PolynomialPreparedFullWindowFamily.start
    ] using
      D.initial_threePow_lt_twoPow (T.select j)
  · simpa [
      FirstDeferredNormalizationTowerData.start,
      FirstDeferredNormalizationTowerData.windowLength,
      StandardNormalizationGeneratedObstructionTowerData.start,
      StandardNormalizationGeneratedObstructionTowerData.windowLength,
      PolynomialPreparedFullWindowFamily.start
    ] using
      D.initial_twoPow_le_succ_mul_threePow (T.select j)
  · exact hNoCritical

end FirstDeferredNormalizationTowerData

end CollatzSecondLayer3
