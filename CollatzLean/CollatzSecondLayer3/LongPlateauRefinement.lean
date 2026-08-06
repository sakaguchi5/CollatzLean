import CollatzLean.CollatzSecondLayer3.CaptureCountRefinement

/-!
# super-polynomial terminalからlong synchronized plateauへ

critical captureがないfinite normalizationではcapture数が対数的に抑えられる。
一方、長いsynchronized plateauが存在しなければterminal時刻もcapture数に比例して
抑えられ、標準prepared endpointからterminal endpointへ固定多項式上界が生じる。
したがってterminal endpointが全固定多項式を超えるtowerでは、plateau長が無限大へ進む。
-/

namespace CollatzSecondLayer2

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

namespace OddOrbit.FiniteCaptureNormalizationData

/--
terminal以前の区間`[a, a + L)`にcaptureがなければ、
その区間全体からsynchronized plateauを構成できる。
-/
noncomputable def synchronizedPlateauOfNoCaptureInterval
    {O : OddOrbit} {start q : ℕ}
    {D₀ : O.WindowDifferenceData start q}
    (F : O.FiniteCaptureNormalizationData D₀)
    (a L : ℕ)
    (hL : 0 < L)
    (hinside : a + L ≤ F.terminalTime)
    (hNoCapture :
      ∀ k : ℕ,
        a ≤ k →
        k < a + L →
        ¬ Nonempty
          (O.CapturedWindowAt (start + k) q)) :
    SynchronizedPlateauInFirstDeferred F where
  offset := a
  length := L
  length_pos := hL
  inside := hinside
  synchronized := by
    intro t ht
    let k := a + t
    have hkleft : a ≤ k := by
      dsimp [k]
      omega
    have hkright : k < a + L := by
      dsimp [k]
      omega
    have hNo :
        ¬ Nonempty
          (O.CapturedWindowAt (start + k) q) :=
      hNoCapture k hkleft hkright
    have hkt : k < F.terminalTime :=
      lt_of_lt_of_le hkright hinside
    have S :=
      F.synchronized_of_not_captured
        k hkt hNo
    simpa [k, Nat.add_assoc] using S

/--
長さ`M + 1`以上のsynchronized plateauが存在しないなら、
terminal以前の各長さ`M + 1`のblockにはcaptureが存在する。
-/
theorem exists_captured_in_block_of_no_long_plateau
    {O : OddOrbit} {start q : ℕ}
    {D₀ : O.WindowDifferenceData start q}
    (F : O.FiniteCaptureNormalizationData D₀)
    (M r : ℕ)
    (hend :
      (r + 1) * (M + 1) ≤ F.terminalTime)
    (hNoPlateau :
      ¬ ∃ P : SynchronizedPlateauInFirstDeferred F,
        M < P.length) :
    ∃ k : ℕ,
      r * (M + 1) ≤ k ∧
      k < (r + 1) * (M + 1) ∧
      Nonempty
        (O.CapturedWindowAt (start + k) q) := by
  classical
  by_contra hNoCapture
  push Not at hNoCapture
  let L := M + 1
  have hblockEnd :
      (r + 1) * L = r * L + L := by
    ring
  have hinside :
      r * L + L ≤ F.terminalTime := by
    simpa [L, hblockEnd] using hend
  have hNoCapture' :
      ∀ k : ℕ,
        r * L ≤ k →
        k < r * L + L →
        ¬ Nonempty
          (O.CapturedWindowAt (start + k) q) := by
    intro k hkleft hkright
    have hEmpty :
        IsEmpty
          (O.CapturedWindowAt (start + k) q) := by
      apply hNoCapture k
      · simpa [L] using hkleft
      · simpa [L, hblockEnd] using hkright
    intro hCaptured
    rcases hCaptured with ⟨C⟩
    exact isEmptyElim C
  let P :=
    F.synchronizedPlateauOfNoCaptureInterval
      (r * L)
      L
      (by
        dsimp [L]
        omega)
      hinside
      hNoCapture'
  apply hNoPlateau
  refine ⟨P, ?_⟩
  have hPlength : P.length = L := by
    rfl
  rw [hPlength]
  dsimp [L]
  omega

/--
最初の`N`個の長さ`L`のblockがそれぞれcaptureを持つなら、
第`r`block終端までのcapture数は少なくとも`r`。
-/
theorem blockNumber_le_windowCaptureCountBefore
    {O : OddOrbit} {start q : ℕ}
    {D₀ : O.WindowDifferenceData start q}
    (F : O.FiniteCaptureNormalizationData D₀)
    (L : ℕ)
    (hblockCapture :
      ∀ r : ℕ,
        r < F.captureCount + 1 →
        ∃ k : ℕ,
          r * L ≤ k ∧
          k < (r + 1) * L ∧
          Nonempty
            (O.CapturedWindowAt (start + k) q)) :
    ∀ r : ℕ,
      r ≤ F.captureCount + 1 →
      r ≤ O.windowCaptureCountBefore
        start q (r * L) := by
  intro r
  induction r with
  | zero =>
      intro _
      simp
  | succ r ih =>
      intro hr
      have hrlt :
          r < F.captureCount + 1 := by
        omega
      have hprev :
          r ≤
            O.windowCaptureCountBefore
              start q (r * L) :=
        ih (by omega)
      obtain ⟨k, hkleft, hkright, hcap⟩ :=
        hblockCapture r hrlt
      have hincrease :=
        O.windowCaptureCountBefore_add_one_le_of_captured
          start q
          hkleft
          hkright
          hcap
      omega

/--
terminal以前の任意のprefix capture数は、
terminal以前の総capture数以下。
-/
theorem windowCaptureCountBefore_le_captureCount_of_le_terminalTime
    {O : OddOrbit} {start q : ℕ}
    {D₀ : O.WindowDifferenceData start q}
    (F : O.FiniteCaptureNormalizationData D₀)
    {t : ℕ}
    (ht : t ≤ F.terminalTime) :
    O.windowCaptureCountBefore start q t ≤
      F.captureCount := by
  have hmono :=
    O.windowCaptureCountBefore_mono
      start q ht
  simpa [captureCount] using hmono

/--
normalization時間が`(captureCount+1)*(M+1)`以上なら、
長さ`M+1`以上のsynchronized plateauが存在する。
-/
theorem exists_synchronizedPlateau_of_mul_le_terminalTime
    {O : OddOrbit} {start q : ℕ}
    {D₀ : O.WindowDifferenceData start q}
    (F : O.FiniteCaptureNormalizationData D₀)
    (M : ℕ)
    (hTime :
      (F.captureCount + 1) * (M + 1) ≤
        F.terminalTime) :
    ∃ P : SynchronizedPlateauInFirstDeferred F,
      M < P.length := by
  classical
  by_contra hNoPlateau
  let L := M + 1
  have hTimeL :
      (F.captureCount + 1) * L ≤
        F.terminalTime := by
    simpa [L] using hTime
  have hblockCapture :
      ∀ r : ℕ,
        r < F.captureCount + 1 →
        ∃ k : ℕ,
          r * L ≤ k ∧
          k < (r + 1) * L ∧
          Nonempty
            (O.CapturedWindowAt (start + k) q) := by
    intro r hr
    have hrle :
        r + 1 ≤ F.captureCount + 1 := by
      omega
    have hend :
        (r + 1) * L ≤ F.terminalTime := by
      exact le_trans
        (Nat.mul_le_mul_right L hrle)
        hTimeL
    have hend' :
        (r + 1) * (M + 1) ≤
          F.terminalTime := by
      simpa [L] using hend
    simpa [L] using
      F.exists_captured_in_block_of_no_long_plateau
        M r hend' hNoPlateau
  have hmany :
      F.captureCount + 1 ≤
        O.windowCaptureCountBefore
          start q
          ((F.captureCount + 1) * L) := by
    exact
      F.blockNumber_le_windowCaptureCountBefore
        L
        hblockCapture
        (F.captureCount + 1)
        le_rfl
  have hprefix :
      O.windowCaptureCountBefore
          start q
          ((F.captureCount + 1) * L) ≤
        F.captureCount := by
    exact
      F.windowCaptureCountBefore_le_captureCount_of_le_terminalTime
        hTimeL
  omega

end OddOrbit.FiniteCaptureNormalizationData

namespace FirstDeferredNormalizationTowerData

/--
no-criticalかつ長さ`M+1`のplateauを持たない一項では、terminal endpointに
明示的な固定多項式上界が生じる。
-/
theorem terminalEndpoint_le_polynomial_of_noCritical_noLongPlateau
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    (T : FirstDeferredNormalizationTowerData D)
    (j M : ℕ)
    (hNoCritical : NoCriticalCaptureInFirstDeferred (T.data j))
    (hNoPlateau :
      ¬ ∃ P : SynchronizedPlateauInFirstDeferred (T.data j),
        M < P.length) :
    T.terminalEndpoint j ≤
      (4 ^ (M + 1) *
          ((polynomialPreparedFullWindowFamily hGap D.crossing).K + 1)) *
        (T.windowLength j + 1) ^
          (2 * (M + 1) +
            (polynomialPreparedFullWindowFamily hGap D.crossing).A) := by
  let F := T.data j
  let q := T.windowLength j
  let C := F.captureCount
  let L := M + 1
  let P := polynomialPreparedFullWindowFamily hGap D.crossing
  have htime : F.terminalTime < (C + 1) * L := by
    by_contra hnot
    have hle : (C + 1) * L ≤ F.terminalTime := Nat.le_of_not_gt hnot
    exact hNoPlateau
      (F.exists_synchronizedPlateau_of_mul_le_terminalTime M
        (by simpa [C, L] using hle))
  have hcount : 2 ^ C < q + 1 := by
    simpa [F, C, q] using
      T.twoPow_captureCount_lt_windowLength_succ j hNoCritical
  have htwoC : 2 ^ C ≤ q + 1 := hcount.le
  have hfourC : 4 ^ C = 2 ^ C * 2 ^ C := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, mul_pow]
  have hfourSucc : 4 ^ (C + 1) ≤ 4 * (q + 1) ^ 2 := by
    calc
      4 ^ (C + 1) = 4 ^ C * 4 := by rw [pow_succ]
      _ = (2 ^ C * 2 ^ C) * 4 := by rw [hfourC]
      _ ≤ ((q + 1) * (q + 1)) * 4 := by
        exact Nat.mul_le_mul_right 4 (Nat.mul_le_mul htwoC htwoC)
      _ = 4 * (q + 1) ^ 2 := by ring
  have hfourTime :
      4 ^ F.terminalTime ≤
        4 ^ (M + 1) * (q + 1) ^ (2 * (M + 1)) := by
    calc
      4 ^ F.terminalTime ≤ 4 ^ ((C + 1) * (M + 1)) := by
        exact Nat.pow_le_pow_right (by omega) (by simpa [L] using htime.le)
      _ = (4 ^ (C + 1)) ^ (M + 1) := by rw [pow_mul]
      _ ≤ (4 * (q + 1) ^ 2) ^ (M + 1) := by
        exact pow_le_pow_left' hfourSucc _
      _ = 4 ^ (M + 1) * (q + 1) ^ (2 * (M + 1)) := by
        rw [mul_pow, ← pow_mul]
  have hinitial :
      O.value (T.start j + q) ≤ P.K * (q + 1) ^ P.A := by
    have h := P.endpointBound (T.crossingIndex j)
    simpa [P, q,
      FirstDeferredNormalizationTowerData.start,
      FirstDeferredNormalizationTowerData.windowLength,
      FirstDeferredNormalizationTowerData.crossingIndex,
      StandardNormalizationGeneratedObstructionTowerData.start,
      StandardNormalizationGeneratedObstructionTowerData.windowLength,
      PolynomialPreparedFullWindowFamily.start,
      Nat.add_assoc] using h
  have hbasePos : 0 < (q + 1) ^ P.A := Nat.pow_pos (by omega)
  have hinitialOne :
      O.value (T.start j + q) + 1 ≤
        (P.K + 1) * (q + 1) ^ P.A := by
    calc
      O.value (T.start j + q) + 1
          ≤ P.K * (q + 1) ^ P.A + 1 := Nat.add_le_add_right hinitial 1
      _ ≤ P.K * (q + 1) ^ P.A + (q + 1) ^ P.A := by
        exact Nat.add_le_add_left hbasePos _
      _ = (P.K + 1) * (q + 1) ^ P.A := by ring
  have horbit :=
    O.value_add_one_le_fourPow_mul
      (T.start j + q) F.terminalTime
  have hterminalOne :
      T.terminalEndpoint j + 1 ≤
        (4 ^ (M + 1) * (q + 1) ^ (2 * (M + 1))) *
          ((P.K + 1) * (q + 1) ^ P.A) := by
    calc
      T.terminalEndpoint j + 1
          ≤ 4 ^ F.terminalTime *
              (O.value (T.start j + q) + 1) := by
            simpa [FirstDeferredNormalizationTowerData.terminalEndpoint,
              FirstDeferredNormalizationTowerData.terminalTime,
              F, q, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm] using horbit
      _ ≤ (4 ^ (M + 1) * (q + 1) ^ (2 * (M + 1))) *
            ((P.K + 1) * (q + 1) ^ P.A) :=
          Nat.mul_le_mul hfourTime hinitialOne
  have hpoly :
      (4 ^ (M + 1) * (q + 1) ^ (2 * (M + 1))) *
          ((P.K + 1) * (q + 1) ^ P.A) =
        (4 ^ (M + 1) * (P.K + 1)) *
          (q + 1) ^ (2 * (M + 1) + P.A) := by
    rw [pow_add]
    ring
  rw [hpoly] at hterminalOne
  have hself : T.terminalEndpoint j ≤ T.terminalEndpoint j + 1 := by omega
  simpa [q, P] using le_trans hself hterminalOne

end FirstDeferredNormalizationTowerData

/--
terminal endpointが全固定多項式を最終的に超え、選択項にcritical captureがないtower。
-/
structure SuperPolynomialNoCriticalFirstDeferredTowerData
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    (T : FirstDeferredNormalizationTowerData D) where
  select : ℕ → ℕ
  select_strict : StrictMono select
  noCritical : ∀ j : ℕ,
    NoCriticalCaptureInFirstDeferred (T.data (select j))
  terminalSuperPolynomial : ∀ K A : ℕ,
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      K * (T.windowLength (select j) + 1) ^ A <
        T.terminalEndpoint (select j)

namespace SuperPolynomialNoCriticalFirstDeferredTowerData

/-- 任意の固定長を超えるplateauが十分後の全選択項に存在する。 -/
theorem eventually_has_long_plateau
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    {T : FirstDeferredNormalizationTowerData D}
    (R : SuperPolynomialNoCriticalFirstDeferredTowerData T)
    (M : ℕ) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      ∃ P : SynchronizedPlateauInFirstDeferred (T.data (R.select j)),
        M < P.length := by
  let P₀ := polynomialPreparedFullWindowFamily hGap D.crossing
  let K := 4 ^ (M + 1) * (P₀.K + 1)
  let A := 2 * (M + 1) + P₀.A
  obtain ⟨J, hJ⟩ := R.terminalSuperPolynomial K A
  refine ⟨J, ?_⟩
  intro j hj
  by_contra hNoPlateau
  have hbound :=
    T.terminalEndpoint_le_polynomial_of_noCritical_noLongPlateau
      (R.select j) M (R.noCritical j) hNoPlateau
  have hlarge := hJ j hj
  have hbound' :
      T.terminalEndpoint (R.select j) ≤
        K * (T.windowLength (R.select j) + 1) ^ A := by
    simpa [K, A, P₀] using hbound
  omega

/-- 下限`N`以後で長さ`M`を超えるplateauを持つ添字を一つ選ぶ。 -/
noncomputable def longIndexAfter
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    {T : FirstDeferredNormalizationTowerData D}
    (R : SuperPolynomialNoCriticalFirstDeferredTowerData T)
    (N M : ℕ) : ℕ := by
  let J := Classical.choose (R.eventually_has_long_plateau M)
  exact max N J

/-- `longIndexAfter`は指定下限以上。 -/
theorem longIndexAfter_ge
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    {T : FirstDeferredNormalizationTowerData D}
    (R : SuperPolynomialNoCriticalFirstDeferredTowerData T)
    (N M : ℕ) :
    N ≤ R.longIndexAfter N M := by
  simp [longIndexAfter]

/-- 選択添字には要求長を超えるplateauが存在する。 -/
theorem longIndexAfter_spec
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    {T : FirstDeferredNormalizationTowerData D}
    (R : SuperPolynomialNoCriticalFirstDeferredTowerData T)
    (N M : ℕ) :
    ∃ P : SynchronizedPlateauInFirstDeferred
        (T.data (R.select (R.longIndexAfter N M))),
      M < P.length := by
  let J := Classical.choose (R.eventually_has_long_plateau M)
  have hJ := Classical.choose_spec (R.eventually_has_long_plateau M)
  apply hJ (R.longIndexAfter N M)
  simp [longIndexAfter]

/-- plateau長が段階的に増える添字列。 -/
noncomputable def longSelect
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    {T : FirstDeferredNormalizationTowerData D}
    (R : SuperPolynomialNoCriticalFirstDeferredTowerData T) : ℕ → ℕ
  | 0 => R.longIndexAfter 0 0
  | n + 1 => R.longIndexAfter (R.longSelect n + 1) (n + 1)

/-- `longSelect`は狭義単調。 -/
theorem longSelect_strict
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    {T : FirstDeferredNormalizationTowerData D}
    (R : SuperPolynomialNoCriticalFirstDeferredTowerData T) :
    StrictMono R.longSelect := by
  apply strictMono_nat_of_lt_succ
  intro n
  have h := R.longIndexAfter_ge (R.longSelect n + 1) (n + 1)
  simpa [longSelect] using h

/-- `longSelect j`で選ばれたplateau。 -/
noncomputable def longPlateau
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    {T : FirstDeferredNormalizationTowerData D}
    (R : SuperPolynomialNoCriticalFirstDeferredTowerData T)
    (j : ℕ) :
    SynchronizedPlateauInFirstDeferred
      (T.data (R.select (R.longSelect j))) := by
  cases j with
  | zero =>
      exact Classical.choose (R.longIndexAfter_spec 0 0)
  | succ j =>
      exact Classical.choose
        (R.longIndexAfter_spec (R.longSelect j + 1) (j + 1))

/-- 選択plateauの長さは添字より大きい。 -/
theorem longPlateau_length_gt
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    {T : FirstDeferredNormalizationTowerData D}
    (R : SuperPolynomialNoCriticalFirstDeferredTowerData T)
    (j : ℕ) :
    j < (R.longPlateau j).length := by
  cases j with
  | zero =>
      exact (Classical.choose_spec (R.longIndexAfter_spec 0 0))
  | succ j =>
      exact Classical.choose_spec
        (R.longIndexAfter_spec (R.longSelect j + 1) (j + 1))

/-- super-polynomial no-critical towerからlong plateau towerを構成する。 -/
noncomputable def toLongSynchronizedPlateauTower
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    {T : FirstDeferredNormalizationTowerData D}
    (R : SuperPolynomialNoCriticalFirstDeferredTowerData T) :
    LongSynchronizedPlateauTowerData hGap O where
  source := D
  firstDeferred := T
  select := fun j => R.select (R.longSelect j)
  select_strict := R.select_strict.comp R.longSelect_strict
  plateau := R.longPlateau
  plateauLengths_tend_to_infinity := by
    intro M
    refine ⟨M + 1, ?_⟩
    intro j hj
    have hlen := R.longPlateau_length_gt j
    omega

end SuperPolynomialNoCriticalFirstDeferredTowerData

end CollatzSecondLayer2
