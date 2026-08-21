import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBCriticalizationStartDyadicRigidity

set_option linter.style.nativeDecide false
/-!
# Pure B: good-scale / arbitrary-phase Wronskian counterexample certificate

このファイルは Stage 6--8 の正方向 theorem を強化するものではない。
むしろ、そこから先に必要だった

  「tail に入る standard scale のどこかで、canonical q-jump rigidity が
    arbitrary phase にもそのまま残る」

という選択原理が一般には成立しないことを、actual critical slope 上の
具体的 phase `a = 1000`, scale `j = 9` で固定する regression certificate である。

重要な点は、巨大な `Nat.find` を直接計算しないことである。
`j = 11` の actual Farey convergent

  (P_11,Q_11) = (31867,50508)

に対する既存 theorem

  beattyIndex k = floor(k Q_11 / P_11),  k < P_11

を使い、今回必要な全 interval `[1000,16601]` を整数除算座標で評価する。
その座標で interval numerator を one-cell recurrence

  Phi[a,a+r+1] = 3 Phi[a,a+r] + 2^(beta(a+r)-beta(a))

により tail-recursive に走査する。

最終 certificate は

  v_2(Wloc(1000,9)) = 24196,

一方 canonical q-jump route が必要とする exponent は

  Q_10 = 24727.

従って 531 powers of two 不足し、

  2^Q_10 ∤ Wloc(1000,9)

が exact に成立する。

注意:
これは `a = 1000` を criticalizationStart に持つ具体的
`PureBProfileObstruction` の存在を主張する theorem ではない。
固定しているのは「arbitrary phase へ canonical Wronskian rigidity を
無条件移植する」ルートの失敗である。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-! ## 1. P_11 corridor 内の高速 Beatty 座標 -/

/--
`P_11` 未満で actual Beatty index と一致する計算可能座標。
-/
def goodScaleCounterexampleCoordinate (n : ℕ) : ℕ :=
  (n * criticalPowerQ 11) / criticalPowerP 11

/-- `k < P_11` では上の計算可能座標は actual `beattyIndex` と exact に一致する。 -/
theorem beattyIndex_eq_goodScaleCounterexampleCoordinate
    {k : ℕ}
    (hk : k < criticalPowerP 11) :
    beattyIndex k = goodScaleCounterexampleCoordinate k := by
  simpa [goodScaleCounterexampleCoordinate] using
    (actual_beattyIndex_eq_div
      (j := 11) (i := k)
      (by norm_num : 9 ≤ 11)
      hk)

/-! ## 2. O(length) の local phase evaluator -/

/--
走査 state `(Phi, twoPow)`。

`r` 個読み終えた時点で第二成分は
`2^(beta(a+r)-beta(a))` を表す。
次 cell では Beatty rise の増分だけ 2 を掛けるので、巨大 exponent の
再計算を避けられる。
-/
def goodScaleCounterexamplePhaseStep
    (a r : ℕ)
    (s : ℤ × ℤ) : ℤ × ℤ :=
  let d :=
    goodScaleCounterexampleCoordinate (a + r + 1) -
      goodScaleCounterexampleCoordinate (a + r)
  (3 * s.1 + s.2, s.2 * (2 : ℤ) ^ d)

/-- `n` cell の高速 phase state。 -/
def goodScaleCounterexamplePhaseState
    (a n : ℕ) : ℤ × ℤ :=
  (List.range n).foldl
    (fun s r => goodScaleCounterexamplePhaseStep a r s)
    (0, 1)

/-- range を一つ延ばしたときの exact step law。 -/
theorem goodScaleCounterexamplePhaseState_succ
    (a n : ℕ) :
    goodScaleCounterexamplePhaseState a (n + 1) =
      goodScaleCounterexamplePhaseStep
        a n (goodScaleCounterexamplePhaseState a n) := by
  unfold goodScaleCounterexamplePhaseState
  rw [List.range_succ, List.foldl_append]
  simp

/--
`a+n < P_11` の範囲では高速 state は actual shifted interval numerator と
actual Beatty two-power を同時に返す。
-/
theorem goodScaleCounterexamplePhaseState_spec
    {a n : ℕ}
    (hEnd : a + n < criticalPowerP 11) :
    goodScaleCounterexamplePhaseState a n =
      (criticalIntervalPhiZ a (a + n),
        (2 : ℤ) ^ (beattyIndex (a + n) - beattyIndex a)) := by
  induction n with
  | zero =>
      simp [
        goodScaleCounterexamplePhaseState,
        criticalIntervalPhiZ
      ]
  | succ n ih =>
      have hPrev : a + n < criticalPowerP 11 := by
        omega
      have hNext : a + n + 1 < criticalPowerP 11 := by
        omega
      have hIH := ih hPrev
      rw [goodScaleCounterexamplePhaseState_succ, hIH]
      have hCoordCur :=
        beattyIndex_eq_goodScaleCounterexampleCoordinate
          (k := a + n) hPrev
      have hCoordNext :=
        beattyIndex_eq_goodScaleCounterexampleCoordinate
          (k := a + n + 1) hNext
      have hDelta :
          goodScaleCounterexampleCoordinate (a + n + 1) -
              goodScaleCounterexampleCoordinate (a + n) =
            beattyIndex (a + n + 1) - beattyIndex (a + n) := by
        rw [← hCoordNext, ← hCoordCur]
      have hOne :
          criticalIntervalPhiZ (a + n) (a + n + 1) = 1 := by
        simp [criticalIntervalPhiZ]
      have hRec :=
        criticalIntervalPhiZ_concat
          (a := a)
          (c := a + n)
          (b := a + n + 1)
          (by omega)
          (by omega)
      have hLen : a + n + 1 - (a + n) = 1 := by
        omega
      rw [hLen, pow_one, hOne] at hRec
      have hMonoA :
          beattyIndex a ≤ beattyIndex (a + n) := by
        by_cases hn0 : n = 0
        · subst n
          simp
        · exact
            le_of_lt
              (beattyIndex_strictMono (by omega))
      have hMonoNext :
          beattyIndex (a + n) ≤ beattyIndex (a + n + 1) := by
        exact le_of_lt (beattyIndex_lt_succ (a + n))
      have hSplit :
          beattyIndex (a + n + 1) - beattyIndex a =
            (beattyIndex (a + n) - beattyIndex a) +
              (beattyIndex (a + n + 1) - beattyIndex (a + n)) := by
        omega
      unfold goodScaleCounterexamplePhaseStep
      dsimp only [Prod.fst, Prod.snd]
      apply Prod.ext
      · simp only
        simpa [Nat.add_assoc] using hRec.symm
      · simp only
        rw [hDelta]
        have hSplit' :
            beattyIndex (a + (n + 1)) - beattyIndex a =
              (beattyIndex (a + n) - beattyIndex a) +
                (beattyIndex (a + n + 1) -
                  beattyIndex (a + n)) := by
          simpa [Nat.add_assoc] using hSplit
        rw [hSplit', pow_add]

/-- 高速 evaluator の numerator 成分。 -/
def goodScaleCounterexamplePhi
    (a n : ℕ) : ℤ :=
  (goodScaleCounterexamplePhaseState a n).1

/-- 高速 evaluator の local power-gap 成分。 -/
def goodScaleCounterexampleGap
    (a n : ℕ) : ℤ :=
  (goodScaleCounterexamplePhaseState a n).2 - (3 : ℤ) ^ n

/-- corridor 内では高速 numerator は既存 `criticalIntervalPhiZ` そのもの。 -/
theorem goodScaleCounterexamplePhi_eq_criticalIntervalPhiZ
    {a n : ℕ}
    (hEnd : a + n < criticalPowerP 11) :
    goodScaleCounterexamplePhi a n =
      criticalIntervalPhiZ a (a + n) := by
  have h := goodScaleCounterexamplePhaseState_spec (a := a) (n := n) hEnd
  simpa [goodScaleCounterexamplePhi] using congrArg Prod.fst h

/-- corridor 内では高速 gap は既存 `criticalIntervalGapZ` そのもの。 -/
theorem goodScaleCounterexampleGap_eq_criticalIntervalGapZ
    {a n : ℕ}
    (hEnd : a + n < criticalPowerP 11) :
    goodScaleCounterexampleGap a n =
      criticalIntervalGapZ a (a + n) := by
  have h := goodScaleCounterexamplePhaseState_spec (a := a) (n := n) hEnd
  have hSecond := congrArg Prod.snd h
  unfold goodScaleCounterexampleGap criticalIntervalGapZ
  rw [hSecond]
  have hLen : a + n - a = n := by
    omega
  rw [hLen]

/-! ## 3. arbitrary-phase local Wronskian -/

/-- 高速 evaluator で計算する local Wronskian。 -/
def goodScaleCounterexampleWronskian
    (a j : ℕ) : ℤ :=
  goodScaleCounterexampleGap a (criticalPowerP (j + 1)) *
      goodScaleCounterexamplePhi a (criticalPowerP j) -
    goodScaleCounterexampleGap a (criticalPowerP j) *
      goodScaleCounterexamplePhi a (criticalPowerP (j + 1))

/-- 既存 interval definitions だけで書いた同じ local Wronskian。 -/
def shiftedCriticalIntervalWronskian
    (a j : ℕ) : ℤ :=
  criticalIntervalGapZ a (a + criticalPowerP (j + 1)) *
      criticalIntervalPhiZ a (a + criticalPowerP j) -
    criticalIntervalGapZ a (a + criticalPowerP j) *
      criticalIntervalPhiZ a (a + criticalPowerP (j + 1))

/-- 高速 certificate と repo 本体の local Wronskian の exact bridge。 -/
theorem goodScaleCounterexampleWronskian_eq_shifted
    {a j : ℕ}
    (hJ : a + criticalPowerP j < criticalPowerP 11)
    (hNext : a + criticalPowerP (j + 1) < criticalPowerP 11) :
    goodScaleCounterexampleWronskian a j =
      shiftedCriticalIntervalWronskian a j := by
  have hPhiJ :=
    goodScaleCounterexamplePhi_eq_criticalIntervalPhiZ
      (a := a) (n := criticalPowerP j) hJ
  have hPhiNext :=
    goodScaleCounterexamplePhi_eq_criticalIntervalPhiZ
      (a := a) (n := criticalPowerP (j + 1)) hNext
  have hGapJ :=
    goodScaleCounterexampleGap_eq_criticalIntervalGapZ
      (a := a) (n := criticalPowerP j) hJ
  have hGapNext :=
    goodScaleCounterexampleGap_eq_criticalIntervalGapZ
      (a := a) (n := criticalPowerP (j + 1)) hNext
  unfold goodScaleCounterexampleWronskian shiftedCriticalIntervalWronskian
  rw [hPhiJ, hPhiNext, hGapJ, hGapNext]

/-! ## 4. concrete certificate: a = 1000, j = 9 -/

/-- finite table values used by the certificate。 -/
theorem goodScaleCounterexample_power_table :
    criticalPowerP 9 = 665 ∧
    criticalPowerQ 9 = 1054 ∧
    criticalPowerP 10 = 15601 ∧
    criticalPowerQ 10 = 24727 ∧
    criticalPowerP 11 = 31867 ∧
    criticalPowerQ 11 = 50508 := by
  decide

/-- certificate 全体が `P_11` corridor 内に収まる。 -/
theorem goodScaleCounterexample_inside_P11 :
    1000 + criticalPowerP 9 < criticalPowerP 11 ∧
    1000 + criticalPowerP 10 < criticalPowerP 11 := by
  decide

/-- 具体 phase の Beatty endpoint values。 -/
theorem goodScaleCounterexample_beatty_endpoints :
    beattyIndex 1000 = 1584 ∧
    beattyIndex 1665 = 2638 ∧
    beattyIndex 16601 = 26311 := by
  have h1000 :=
    beattyIndex_eq_goodScaleCounterexampleCoordinate
      (k := 1000) (by decide)
  have h1665 :=
    beattyIndex_eq_goodScaleCounterexampleCoordinate
      (k := 1665) (by decide)
  have h16601 :=
    beattyIndex_eq_goodScaleCounterexampleCoordinate
      (k := 16601) (by decide)
  constructor
  · rw [h1000]
    decide
  · constructor
    · rw [h1665]
      decide
    · rw [h16601]
      decide

/--
endpoint rise 自体は canonical 値と一致する。
したがって failure は単なる endpoint-height mismatch ではない。
-/
theorem goodScaleCounterexample_endpoint_rises_are_canonical :
    beattyIndex (1000 + criticalPowerP 9) - beattyIndex 1000 =
      criticalPowerQ 9 ∧
    beattyIndex (1000 + criticalPowerP 10) - beattyIndex 1000 =
      criticalPowerQ 10 := by
  rcases goodScaleCounterexample_power_table with
    ⟨hP9, hQ9, hP10, hQ10, hP11, hQ11⟩
  rcases goodScaleCounterexample_beatty_endpoints with
    ⟨hB0, hB9, hB10⟩
  rw [hP9, hP10, hQ9, hQ10]
  norm_num [hB0, hB9, hB10]

/--
現在の Stage 8B/8D が要求する precision side condition は、この唯一の
small fitting scale `j=9` では既に失敗する。
-/
theorem goodScaleCounterexample_stage8_precision_fails :
    ¬ beattyIndex 1000 < criticalPowerQ 9 := by
  rcases goodScaleCounterexample_power_table with
    ⟨hP9, hQ9, hP10, hQ10, hP11, hQ11⟩
  rcases goodScaleCounterexample_beatty_endpoints with
    ⟨hB0, hB9, hB10⟩
  rw [hB0, hQ9]
  norm_num

/--
高速 evaluator 上の exact 2-adic certificate。
`W mod 2^24196 = 0`。
-/
theorem goodScaleCounterexample_fast_emod_24196 :
    goodScaleCounterexampleWronskian 1000 9 %
        (2 : ℤ) ^ 24196 = 0 := by
  native_decide

/--
次の一段では residue が exact に `2^24196`。
従って 2-adic order は 24196 で止まる。
-/
theorem goodScaleCounterexample_fast_emod_24197 :
    goodScaleCounterexampleWronskian 1000 9 %
        (2 : ℤ) ^ 24197 =
      (2 : ℤ) ^ 24196 := by
  native_decide

/-- repo 本体の shifted local Wronskian へ同じ certificate を移す。 -/
theorem shiftedCriticalIntervalWronskian_1000_9_emod_24196 :
    shiftedCriticalIntervalWronskian 1000 9 %
        (2 : ℤ) ^ 24196 = 0 := by
  have hBridge :=
    goodScaleCounterexampleWronskian_eq_shifted
      (a := 1000) (j := 9)
      (by decide)
      (by decide)
  rw [← hBridge]
  exact goodScaleCounterexample_fast_emod_24196

/-- 一段上では nonzero residue。 -/
theorem shiftedCriticalIntervalWronskian_1000_9_emod_24197 :
    shiftedCriticalIntervalWronskian 1000 9 %
        (2 : ℤ) ^ 24197 =
      (2 : ℤ) ^ 24196 := by
  have hBridge :=
    goodScaleCounterexampleWronskian_eq_shifted
      (a := 1000) (j := 9)
      (by decide)
      (by decide)
  rw [← hBridge]
  exact goodScaleCounterexample_fast_emod_24197

/-- `v_2(Wloc(1000,9)) = 24196` の divisibility 版。 -/
theorem shiftedCriticalIntervalWronskian_1000_9_exact_twoAdic :
    (2 : ℤ) ^ 24196 ∣ shiftedCriticalIntervalWronskian 1000 9 ∧
    ¬ (2 : ℤ) ^ 24197 ∣ shiftedCriticalIntervalWronskian 1000 9 := by
  constructor
  · exact
      (Int.dvd_iff_emod_eq_zero).2
        shiftedCriticalIntervalWronskian_1000_9_emod_24196
  · intro hDvd
    have hZero :
        shiftedCriticalIntervalWronskian 1000 9 %
            (2 : ℤ) ^ 24197 = 0 :=
      Int.emod_eq_zero_of_dvd hDvd
    rw [shiftedCriticalIntervalWronskian_1000_9_emod_24197] at hZero
    have hPowNe : (2 : ℤ) ^ 24196 ≠ 0 := by
      positivity
    exact hPowNe hZero

/-- canonical route が要求する exponent と actual local order の差は 531。 -/
theorem goodScaleCounterexample_twoAdic_shortfall :
    criticalPowerQ 10 - 24196 = 531 := by
  decide

/--
決定的な negative certificate:

  2^Q_10 ∤ Wloc(1000,9).

従って canonical corrected Wronskian から得た q-jump divisibility を
この arbitrary phase へ無条件に移すことはできない。
-/
theorem twoPow_Q10_not_dvd_shiftedCriticalIntervalWronskian_1000_9 :
    ¬ (2 : ℤ) ^ criticalPowerQ 10 ∣
      shiftedCriticalIntervalWronskian 1000 9 := by
  rcases goodScaleCounterexample_power_table with
    ⟨hP9, hQ9, hP10, hQ10, hP11, hQ11⟩
  rw [hQ10]
  intro hBig
  have hSmallBig :
      (2 : ℤ) ^ 24197 ∣ (2 : ℤ) ^ 24727 := by
    refine ⟨(2 : ℤ) ^ 530, ?_⟩
    rw [show 24727 = 24197 + 530 by norm_num, pow_add]
  have hSmall :
      (2 : ℤ) ^ 24197 ∣
        shiftedCriticalIntervalWronskian 1000 9 :=
    dvd_trans hSmallBig hBig
  exact
    shiftedCriticalIntervalWronskian_1000_9_exact_twoAdic.2 hSmall

end ExternalArithmetic
end CSTMicro
end Collatz2
