import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBLocalSquareRigidity
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalBeattyOneShortSquares

set_option linter.style.emptyLine false

/-!
# Pure B local one-short square rigidity

完全 square の既存証明は、criticalization start `a` の直前 `a-1` から始まる
period `r` の二 block について最初の一文字を落とし、length `r-1` の
二 transfer を比較していた。

one-short square では最後の一文字だけ不足するため、さらに最後の一文字も落として
length `r-2` の二 transfer を比較する。同じ affine constant cancellation により

  2^F | (Z_(a+r)-Z_a),
  F >= r-2

を得る。

state return が起きると first-symbol equality だけで `a-1` への integral predecessor
を復元できるため、criticalization start の最小性に反する。従って

  2^(r-2) <= 4*yNat

が成立する。

完全 square 版より指数が 1 だけ弱いが、terminal contradiction には十分である。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

namespace PureBProfileObstruction

namespace CriticalBeattyOneShortSquareAt

/-- `a-1` 始まりの first-step equality を actual 座標へ正規化する。 -/
theorem firstStep_eq_of_predStart
    {a r : ℕ}
    (B : CriticalBeattyOneShortSquareAt (a - 1) r)
    (ha : 0 < a) :
    beattyIndex a - beattyIndex (a - 1) =
      beattyIndex (a + r) - beattyIndex (a + r - 1) := by
  have haOneLe : 1 ≤ a := Nat.succ_le_iff.mpr ha
  have hLeft : (a - 1) + 1 = a := Nat.sub_add_cancel haOneLe
  have hRightBase : (a - 1) + r = a + r - 1 := by omega
  have haRPos : 0 < a + r := by omega
  have haROneLe : 1 ≤ a + r := Nat.succ_le_iff.mpr haRPos
  have hRightSucc : (a + r - 1) + 1 = a + r :=
    Nat.sub_add_cancel haROneLe
  simpa only [hLeft, hRightBase, hRightSucc] using B.firstStep_eq

/-- `a-1` 始まりの length `r-2` tail rise を actual 座標へ正規化する。 -/
theorem tailTotalRise_eq_of_predStart
    {a r : ℕ}
    (B : CriticalBeattyOneShortSquareAt (a - 1) r)
    (ha : 0 < a) :
    beattyIndex (a + (r - 2)) - beattyIndex a =
      beattyIndex (a + r + (r - 2)) - beattyIndex (a + r) := by
  have haOneLe : 1 ≤ a := Nat.succ_le_iff.mpr ha
  have hLeft : (a - 1) + 1 = a := Nat.sub_add_cancel haOneLe
  have hRightBase : (a - 1) + r + 1 = a + r := by omega
  have h := B.tailTotalRise_eq
  simpa only [hLeft, hRightBase, Nat.add_assoc] using h

/-- `a-1` 始まりの length `r-2` tail Phi を actual 座標へ正規化する。 -/
theorem tailPhi_eq_of_predStart
    {a r : ℕ}
    (B : CriticalBeattyOneShortSquareAt (a - 1) r)
    (ha : 0 < a) :
    criticalIntervalPhiZ
        a
        (a + (r - 2)) =
      criticalIntervalPhiZ
        (a + r)
        (a + r + (r - 2)) := by
  have haOneLe : 1 ≤ a := Nat.succ_le_iff.mpr ha
  have hLeft : (a - 1) + 1 = a := Nat.sub_add_cancel haOneLe
  have hRightBase : (a - 1) + r + 1 = a + r := by omega
  have h := B.tailPhi_eq
  simpa only [hLeft, hRightBase, Nat.add_assoc] using h

end CriticalBeattyOneShortSquareAt

/--
one-short square の二 tail transfer を引き算し、state difference の dyadic divisor を得る。
-/
theorem twoPow_tailRise_dvd_stateDifference_of_oneShortSquare
    (P : PureBProfileObstruction)
    {r : ℕ}
    (hStartPos : 0 < P.criticalizationStart)
    (hrTwo : 2 ≤ r)
    (hEnd : P.criticalizationStart + 2 * r - 2 ≤ P.m)
    (B : CriticalBeattyOneShortSquareAt (P.criticalizationStart - 1) r) :
    (2 : ℤ) ^
        (beattyIndex (P.criticalizationStart + r - 2) -
          beattyIndex P.criticalizationStart) ∣
      (P.integralCriticalTailStateInt
          P.criticalizationStart_spec
          (P.criticalizationStart + r)
          (by omega)
          (by omega) -
        P.integralCriticalTailStateInt
          P.criticalizationStart_spec
          P.criticalizationStart
          le_rfl
          P.criticalizationStart_spec.1) := by
  let a := P.criticalizationStart
  let A : IsIntegralCriticalTail P a := P.criticalizationStart_spec
  let n := r - 2
  let F : ℕ := beattyIndex (a + n) - beattyIndex a
  let Za : ℤ := P.integralCriticalTailStateInt A a le_rfl A.1
  let Z1 : ℤ :=
    P.integralCriticalTailStateInt A (a + n) (by omega) (by dsimp [n]; omega)
  let Zr : ℤ :=
    P.integralCriticalTailStateInt A (a + r) (by omega) (by omega)
  let Z2 : ℤ :=
    P.integralCriticalTailStateInt
      A (a + r + n) (by omega) (by dsimp [n]; omega)
  have hTailRise' :
      beattyIndex (a + n) - beattyIndex a =
        beattyIndex (a + r + n) - beattyIndex (a + r) := by
    have h :=
      CriticalBeattyOneShortSquareAt.tailTotalRise_eq_of_predStart
        B hStartPos
    simpa [n] using h
  have hPhi' :
      criticalIntervalPhiZ a (a + n) =
        criticalIntervalPhiZ (a + r) (a + r + n) := by
    have h :=
      CriticalBeattyOneShortSquareAt.tailPhi_eq_of_predStart
        B hStartPos
    simpa [n] using h
  have hT1 :=
    P.integralCriticalTailStateInt_interval_transport
      (A := A)
      (s := a)
      (r := n)
      le_rfl
      (by dsimp [n]; omega)
  have hT2 :=
    P.integralCriticalTailStateInt_interval_transport
      (A := A)
      (s := a + r)
      (r := n)
      (by omega)
      (by dsimp [n]; omega)
  have hT1' :
      (2 : ℤ) ^ F * Z1 =
        (3 : ℤ) ^ n * Za + criticalIntervalPhiZ a (a + n) := by
    simpa [F, Z1, Za] using hT1
  have hT2' :
      (2 : ℤ) ^ F * Z2 =
        (3 : ℤ) ^ n * Zr + criticalIntervalPhiZ (a + r) (a + r + n) := by
    rw [← hTailRise'] at hT2
    simpa [F, Z2, Zr] using hT2
  have hCross :
      (2 : ℤ) ^ F * (Z2 - Z1) =
        (3 : ℤ) ^ n * (Zr - Za) := by
    rw [hPhi'] at hT1'
    linarith
  have hProd :
      (2 : ℤ) ^ F ∣ (3 : ℤ) ^ n * (Zr - Za) := by
    refine ⟨Z2 - Z1, ?_⟩
    exact hCross.symm
  have hCoprime :
      IsCoprime ((2 : ℤ) ^ F) ((3 : ℤ) ^ n) := by
    exact (threePow_isCoprime_twoPow n F).symm
  have hDiv : (2 : ℤ) ^ F ∣ Zr - Za :=
    hCoprime.dvd_of_dvd_mul_left hProd
  have hIndex : a + n = a + r - 2 := by
    dsimp [n]
    omega
  have hF : F = beattyIndex (a + r - 2) - beattyIndex a := by
    dsimp [F]
    rw [hIndex]
  have hDiv' :
      (2 : ℤ) ^ (beattyIndex (a + r - 2) - beattyIndex a) ∣ Zr - Za := by
    rw [← hF]
    exact hDiv
  simpa [Zr, Za, a, A] using hDiv'

/--
one-short square の root shift で state return すると predecessor bracket が生じる。
-/
theorem exists_predecessorBracket_of_oneShortSquare_return
    (P : PureBProfileObstruction)
    {a r : ℕ}
    (A : IsIntegralCriticalTail P a)
    (haPos : 0 < a)
    (hrTwo : 2 ≤ r)
    (hEnd : a + 2 * r - 2 ≤ P.m)
    (B : CriticalBeattyOneShortSquareAt (a - 1) r)
    (hReturn :
      P.integralCriticalTailStateInt
          A
          (a + r)
          (by omega)
          (by omega) =
        P.integralCriticalTailStateInt
          A a le_rfl A.1) :
    ∃ Zprev : ℤ,
      (2 : ℤ) ^ (beattyIndex a - beattyIndex (a - 1)) *
            P.integralCriticalTailStateInt A a le_rfl A.1 -
          1 =
        3 * Zprev := by
  have hStepEq :
      beattyIndex a - beattyIndex (a - 1) =
        beattyIndex (a + r) - beattyIndex (a + r - 1) :=
    CriticalBeattyOneShortSquareAt.firstStep_eq_of_predStart B haPos
  have hShiftStart : a ≤ a + r - 1 := by omega
  have hEndR : a + r ≤ P.m := by omega
  have hShiftLt : a + r - 1 < P.m := by omega
  have hShiftLe : a + r - 1 ≤ P.m := Nat.le_of_lt hShiftLt
  have hShiftStartR : a ≤ a + r := by omega
  have hRec0 :=
    P.integralCriticalTailStateInt_step
      (A := A)
      (s := a + r - 1)
      hShiftStart
      hShiftLt
  have hSucc : (a + r - 1) + 1 = a + r := by omega
  have hRec :
      (2 : ℤ) ^ (beattyIndex a - beattyIndex (a - 1)) *
            P.integralCriticalTailStateInt A (a + r) hShiftStartR hEndR =
        3 *
            P.integralCriticalTailStateInt
              A (a + r - 1) hShiftStart hShiftLe +
          1 := by
    simpa [hSucc, hStepEq] using hRec0
  have hReturn' :
      P.integralCriticalTailStateInt A (a + r) hShiftStartR hEndR =
        P.integralCriticalTailStateInt A a le_rfl A.1 := by
    simpa using hReturn
  let Zprev : ℤ :=
    P.integralCriticalTailStateInt A (a + r - 1) hShiftStart hShiftLe
  have hRecReturn :
      (2 : ℤ) ^ (beattyIndex a - beattyIndex (a - 1)) *
            P.integralCriticalTailStateInt A a le_rfl A.1 =
        3 * Zprev + 1 := by
    simpa [hReturn', Zprev] using hRec
  refine ⟨Zprev, ?_⟩
  linarith [hRecReturn]

/--
criticalization start の直前から始まる one-short square では root shift の state return は不可能。
-/
theorem criticalizationStart_state_ne_of_oneShortSquare
    (P : PureBProfileObstruction)
    {r : ℕ}
    (hStartPos : 0 < P.criticalizationStart)
    (hrTwo : 2 ≤ r)
    (hEnd : P.criticalizationStart + 2 * r - 2 ≤ P.m)
    (B : CriticalBeattyOneShortSquareAt (P.criticalizationStart - 1) r) :
    P.integralCriticalTailStateInt
        P.criticalizationStart_spec
        (P.criticalizationStart + r)
        (by omega)
        (by omega) ≠
      P.integralCriticalTailStateInt
        P.criticalizationStart_spec
        P.criticalizationStart
        le_rfl
        P.criticalizationStart_spec.1 := by
  intro hReturn
  let a := P.criticalizationStart
  let A : IsIntegralCriticalTail P a := P.criticalizationStart_spec
  have haPos : 0 < a := by simpa [a] using hStartPos
  have hEndA : a + 2 * r - 2 ≤ P.m := by simpa [a] using hEnd
  have hSquareA : CriticalBeattyOneShortSquareAt (a - 1) r := by
    simpa [a] using B
  have hReturnA :
      P.integralCriticalTailStateInt A (a + r) (by omega) (by omega) =
        P.integralCriticalTailStateInt A a le_rfl A.1 := by
    simpa [a, A] using hReturn
  obtain ⟨Zprev, hBracket⟩ :=
    P.exists_predecessorBracket_of_oneShortSquare_return
      A haPos hrTwo hEndA hSquareA hReturnA
  have hPrev : IsIntegralCriticalTail P (a - 1) :=
    P.integralCriticalTail_pred_of_bracket A haPos hBracket
  have hMin0 := P.criticalizationStart_minimal hPrev
  have hMin : a ≤ a - 1 := by simpa [a] using hMin0
  have hPredLt : a - 1 < a := Nat.sub_lt haPos (by norm_num)
  exact (not_lt_of_ge hMin) hPredLt

/--
local one-short rigidity の主定理。

one-short square が integral critical tail に収まれば

  2^(r-2) <= 4*yNat.
-/
theorem criticalizationStart_oneShortSquare_dyadic_bound
    (P : PureBProfileObstruction)
    (hy : 0 ≤ P.y)
    {r : ℕ}
    (hStartPos : 0 < P.criticalizationStart)
    (hrTwo : 2 ≤ r)
    (hEnd : P.criticalizationStart + 2 * r - 2 ≤ P.m)
    (B : CriticalBeattyOneShortSquareAt (P.criticalizationStart - 1) r) :
    2 ^ (r - 2) ≤ 4 * P.yNat := by
  let a := P.criticalizationStart
  let A : IsIntegralCriticalTail P a := P.criticalizationStart_spec
  let F : ℕ := beattyIndex (a + r - 2) - beattyIndex a
  let Za : ℤ := P.integralCriticalTailStateInt A a le_rfl A.1
  let Zr : ℤ :=
    P.integralCriticalTailStateInt A (a + r) (by omega) (by omega)
  let D : ℤ := Zr - Za
  have hDiv0 :=
    P.twoPow_tailRise_dvd_stateDifference_of_oneShortSquare
      hStartPos hrTwo hEnd B
  have hDiv : (2 : ℤ) ^ F ∣ D := by
    simpa [F, D, Zr, Za, a, A] using hDiv0
  have hNe0 :=
    P.criticalizationStart_state_ne_of_oneShortSquare
      hStartPos hrTwo hEnd B
  have hDNe : D ≠ 0 := by
    intro hZero
    apply hNe0
    have hEq : Zr = Za := by
      dsimp [D] at hZero
      linarith
    simpa [Zr, Za, a, A] using hEq
  have hZaNonneg : 0 ≤ Za := by
    dsimp [Za]
    exact P.integralCriticalTailStateInt_nonneg A hy le_rfl A.1
  have hZrNonneg : 0 ≤ Zr := by
    dsimp [Zr]
    exact P.integralCriticalTailStateInt_nonneg A hy (by omega) (by omega)
  have hZaLe : Za ≤ 4 * P.y := by
    dsimp [Za]
    exact P.integralCriticalTailStateInt_le_four_y A hy le_rfl A.1
  have hZrLe : Zr ≤ 4 * P.y := by
    dsimp [Zr]
    exact P.integralCriticalTailStateInt_le_four_y A hy (by omega) (by omega)
  have hPowPos : 0 < (2 : ℤ) ^ F := by
    positivity
  have hBoundInt : (2 : ℤ) ^ F ≤ 4 * P.y := by
    rcases lt_or_gt_of_ne hDNe with hDNeg | hDPos
    · have hDivNeg : (2 : ℤ) ^ F ∣ -D := dvd_neg.mpr hDiv
      rcases hDivNeg with ⟨u, hu⟩
      have huPos : 0 < u := by
        have hNegPos : 0 < -D := by linarith
        nlinarith
      have hPowLeNeg : (2 : ℤ) ^ F ≤ -D := by
        rw [hu]
        have huOne : (1 : ℤ) ≤ u := by omega
        nlinarith
      have hNegLe : -D ≤ Za := by
        dsimp [D]
        linarith
      exact le_trans hPowLeNeg (le_trans hNegLe hZaLe)
    · rcases hDiv with ⟨u, hu⟩
      have huPos : 0 < u := by nlinarith
      have hPowLeD : (2 : ℤ) ^ F ≤ D := by
        rw [hu]
        have huOne : (1 : ℤ) ≤ u := by omega
        nlinarith
      have hDLe : D ≤ Zr := by
        dsimp [D]
        linarith
      exact le_trans hPowLeD (le_trans hDLe hZrLe)
  have hBoundCast : (2 : ℤ) ^ F ≤ 4 * (P.yNat : ℤ) := by
    rw [P.yNat_cast hy]
    exact hBoundInt
  have hBoundNat : 2 ^ F ≤ 4 * P.yNat := by
    exact_mod_cast hBoundCast
  have hLenRise : r - 2 ≤ F := by
    dsimp [F]
    have h := intervalLength_le_beattyRise a (r - 2)
    have hEndEq : a + (r - 2) = a + r - 2 := by omega
    simpa [hEndEq] using h
  have hPowLe : 2 ^ (r - 2) ≤ 2 ^ F :=
    Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hLenRise
  exact le_trans hPowLe hBoundNat

end PureBProfileObstruction

end ExternalArithmetic
end CSTMicro
end Collatz2
