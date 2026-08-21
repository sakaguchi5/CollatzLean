import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBIntegralCriticalTail
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalBeattyLocalSquares

set_option linter.style.emptyLine false
/-!
# Pure B local square rigidity

criticalization start `a` の一つ左 `a-1` から critical Beatty exponent block `XX`
(root length `r>=2`) が始まり、その square が integral critical tail 内に収まるとする。

最初の文字を落とした二つの length `r-1` block は同じ affine transfer を持つので、
二本の state transport を引き算すると affine constant が消え、

  2^F | (Z_(a+r) - Z_a)

を得る。ここで `F >= r-1`。

さらに `Z_(a+r)=Z_a` なら square の最初の one-cell exponent の一致により
critical recurrence を `a-1` へ整数のまま延長でき、criticalization start の最小性に反する。
従って state difference は nonzero で、uniform state bound から

  2^(r-1) <= 4*yNat

が従う。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

namespace PureBProfileObstruction

namespace CriticalBeattySquareAt

/--
`a - 1` から始まる square の first-step equality を
actual 座標 `a` / `a+r` に正規化する。
-/
theorem firstStep_eq_of_predStart
    {a r : ℕ}
    (B : CriticalBeattySquareAt (a - 1) r)
    (ha : 0 < a) :
    beattyIndex a - beattyIndex (a - 1) =
      beattyIndex (a + r) - beattyIndex (a + r - 1) := by
  have haOneLe : 1 ≤ a :=
    Nat.succ_le_iff.mpr ha
  have hLeft :
      (a - 1) + 1 = a :=
    Nat.sub_add_cancel haOneLe
  have hRightBase :
      (a - 1) + r = a + r - 1 := by
    omega
  have haRPos :
      0 < a + r := by
    omega
  have haROneLe :
      1 ≤ a + r :=
    Nat.succ_le_iff.mpr haRPos
  have hRightSucc :
      (a + r - 1) + 1 = a + r :=
    Nat.sub_add_cancel haROneLe
  simpa only [
    hLeft,
    hRightBase,
    hRightSucc
  ] using B.firstStep_eq


/--
`a - 1` から始まる square の、first cell を落とした tail rise を
actual 座標へ正規化する。
-/
theorem tailTotalRise_eq_of_predStart
    {a r : ℕ}
    (B : CriticalBeattySquareAt (a - 1) r)
    (ha : 0 < a)
    (hrTwo : 2 ≤ r) :
    beattyIndex (a + (r - 1)) - beattyIndex a =
      beattyIndex (a + r + (r - 1)) -
        beattyIndex (a + r) := by
  have haOneLe : 1 ≤ a :=
    Nat.succ_le_iff.mpr ha
  have hLeft :
      (a - 1) + 1 = a :=
    Nat.sub_add_cancel haOneLe
  have hRightBase :
      (a - 1) + r = a + r - 1 := by
    omega
  have haRPos :
      0 < a + r := by
    omega
  have haROneLe :
      1 ≤ a + r :=
    Nat.succ_le_iff.mpr haRPos
  have hRightSucc :
      (a + r - 1) + 1 = a + r :=
    Nat.sub_add_cancel haROneLe
  have h :=
    B.tailTotalRise_eq
  simpa only [
    hLeft,
    hRightBase,
    hRightSucc,
    Nat.add_assoc
  ] using h


/--
`a - 1` から始まる square の、first cell を落とした tail Phi を
actual 座標へ正規化する。
-/
theorem tailPhi_eq_of_predStart
    {a r : ℕ}
    (B : CriticalBeattySquareAt (a - 1) r)
    (ha : 0 < a)
    (hrTwo : 2 ≤ r) :
    criticalIntervalPhiZ
        a
        (a + (r - 1)) =
      criticalIntervalPhiZ
        (a + r)
        (a + r + (r - 1)) := by
  have haOneLe : 1 ≤ a :=
    Nat.succ_le_iff.mpr ha
  have hLeft :
      (a - 1) + 1 = a :=
    Nat.sub_add_cancel haOneLe
  have hRightBase :
      (a - 1) + r = a + r - 1 := by
    omega
  have haRPos :
      0 < a + r := by
    omega
  have haROneLe :
      1 ≤ a + r :=
    Nat.succ_le_iff.mpr haRPos
  have hRightSucc :
      (a + r - 1) + 1 = a + r :=
    Nat.sub_add_cancel haROneLe
  have h :=
    B.tailPhi_eq
  simpa only [
    hLeft,
    hRightBase,
    hRightSucc,
    Nat.add_assoc
  ] using h

end CriticalBeattySquareAt

/--
criticalization start の直前から始まる square は、最初の文字を落とした二 transfer の
差から residual dyadic divisor を作る。
-/
theorem twoPow_tailRise_dvd_stateDifference_of_square
    (P : PureBProfileObstruction)
    {r : ℕ}
    (hStartPos : 0 < P.criticalizationStart)
    (hrTwo : 2 ≤ r)
    (hEnd : P.criticalizationStart + 2 * r - 1 ≤ P.m)
    (B : CriticalBeattySquareAt (P.criticalizationStart - 1) r) :
    (2 : ℤ) ^
        (beattyIndex (P.criticalizationStart + r - 1) -
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
  let n := r - 1
  let F : ℕ := beattyIndex (a + n) - beattyIndex a
  let Za : ℤ := P.integralCriticalTailStateInt A a le_rfl A.1
  let Z1 : ℤ :=
    P.integralCriticalTailStateInt A (a + n) (by omega) (by dsimp [n]; omega)
  let Zr : ℤ :=
    P.integralCriticalTailStateInt A (a + r) (by omega) (by omega)
  let Z2 : ℤ :=
    P.integralCriticalTailStateInt
      A (a + r + n) (by omega) (by dsimp [n]; omega)
  have hFirst' :
      beattyIndex a - beattyIndex (a - 1) =
        beattyIndex (a + r) -
          beattyIndex (a + r - 1) := by
    exact
      CriticalBeattySquareAt.firstStep_eq_of_predStart B hStartPos
  have hTailRise' :
      beattyIndex (a + n) - beattyIndex a =
        beattyIndex (a + r + n) -
          beattyIndex (a + r) := by
    have h :=
      CriticalBeattySquareAt.tailTotalRise_eq_of_predStart
        B hStartPos hrTwo
    simpa [n] using h
  have hPhi' :
      criticalIntervalPhiZ a (a + n) =
        criticalIntervalPhiZ
          (a + r) (a + r + n) := by
    have h :=
      CriticalBeattySquareAt.tailPhi_eq_of_predStart
        B hStartPos hrTwo
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
  have hIndex :
      a + n = a + r - 1 := by
    dsimp [n]
    omega
  have hF :
      F =
        beattyIndex (a + r - 1) - beattyIndex a := by
    dsimp [F]
    rw [hIndex]
  have hDiv' :
      (2 : ℤ) ^
          (beattyIndex (a + r - 1) - beattyIndex a) ∣
        Zr - Za := by
    rw [← hF]
    exact hDiv
  simpa [Zr, Za, a, A] using hDiv'
/--
square の root shift `r` で integral state が return すると、
first square symbol の一致と一歩前の recurrence から

`2^Δ Z_a - 1 = 3 Z_prev`

を満たす predecessor state が存在する。
-/
theorem exists_predecessorBracket_of_square_return
    (P : PureBProfileObstruction)
    {a r : ℕ}
    (A : IsIntegralCriticalTail P a)
    (haPos : 0 < a)
    (hrTwo : 2 ≤ r)
    (hEnd : a + 2 * r - 1 ≤ P.m)
    (B : CriticalBeattySquareAt (a - 1) r)
    (hReturn :
      P.integralCriticalTailStateInt
          A
          (a + r)
          (by omega)
          (by omega) =
        P.integralCriticalTailStateInt
          A
          a
          le_rfl
          A.1) :
    ∃ Zprev : ℤ,
      (2 : ℤ) ^
          (beattyIndex a - beattyIndex (a - 1)) *
            P.integralCriticalTailStateInt
              A a le_rfl A.1 -
          1 =
        3 * Zprev := by

  have hStepEq :
      beattyIndex a - beattyIndex (a - 1) =
        beattyIndex (a + r) -
          beattyIndex (a + r - 1) :=
    CriticalBeattySquareAt.firstStep_eq_of_predStart B haPos

  have hShiftStart :
      a ≤ a + r - 1 := by
    omega

  have hEndR :
      a + r ≤ P.m := by
    omega

  have hShiftLt :
      a + r - 1 < P.m := by
    omega

  have hShiftLe :
      a + r - 1 ≤ P.m :=
    Nat.le_of_lt hShiftLt

  have hShiftStartR :
      a ≤ a + r := by
    omega

  have hRec0 :=
    P.integralCriticalTailStateInt_step
      (A := A)
      (s := a + r - 1)
      hShiftStart
      hShiftLt

  have hSucc :
      (a + r - 1) + 1 = a + r := by
    omega

  have hRec :
      (2 : ℤ) ^
          (beattyIndex a - beattyIndex (a - 1)) *
            P.integralCriticalTailStateInt
              A
              (a + r)
              hShiftStartR
              hEndR =
        3 *
            P.integralCriticalTailStateInt
              A
              (a + r - 1)
              hShiftStart
              hShiftLe +
          1 := by
    simpa [hSucc, hStepEq] using hRec0

  have hReturn' :
      P.integralCriticalTailStateInt
          A
          (a + r)
          hShiftStartR
          hEndR =
        P.integralCriticalTailStateInt
          A
          a
          le_rfl
          A.1 := by
    simpa using hReturn

  let Zprev : ℤ :=
    P.integralCriticalTailStateInt
      A
      (a + r - 1)
      hShiftStart
      hShiftLe

  have hRecReturn :
      (2 : ℤ) ^
          (beattyIndex a - beattyIndex (a - 1)) *
            P.integralCriticalTailStateInt
              A a le_rfl A.1 =
        3 * Zprev + 1 := by
    simpa [hReturn', Zprev] using hRec

  refine ⟨Zprev, ?_⟩
  linarith [hRecReturn]

/--
integral critical tail の start `a` で

`2^(β(a)-β(a-1)) Z_a - 1 = 3 Z_prev`

を満たす整数 `Z_prev` が存在すれば、
integral critical tail は `a-1` まで一歩延長できる。
-/
theorem integralCriticalTail_pred_of_bracket
    (P : PureBProfileObstruction)
    {a : ℕ}
    (A : IsIntegralCriticalTail P a)
    (haPos : 0 < a)
    {Zprev : ℤ}
    (hBracket :
      (2 : ℤ) ^
          (beattyIndex a - beattyIndex (a - 1)) *
            P.integralCriticalTailStateInt
              A a le_rfl A.1 -
          1 =
        3 * Zprev) :
    IsIntegralCriticalTail P (a - 1) := by
  have hPredLtA :
      a - 1 < a :=
    Nat.sub_lt haPos (by norm_num)
  have hPredLtM :
      a - 1 < P.m :=
    lt_of_lt_of_le hPredLtA A.1
  have hPredLeM :
      a - 1 ≤ P.m :=
    Nat.le_of_lt hPredLtM
  have hRaw0 :=
    P.terminalRawTail_step_raw
      (s := a - 1)
      hPredLtM
  have haOneLe :
      1 ≤ a :=
    Nat.succ_le_iff.mpr haPos
  have hPredSucc :
      (a - 1) + 1 = a :=
    Nat.sub_add_cancel haOneLe
  have hRaw :
      P.terminalRawTail (a - 1) =
        (2 : ℤ) ^
            (beattyIndex a - beattyIndex (a - 1)) *
              P.terminalRawTail a -
          (3 : ℤ) ^ (P.m - a) := by
    simpa [hPredSucc] using hRaw0
  have hSpecA :=
    P.integralCriticalTailStateInt_spec
      (A := A)
      (s := a)
      le_rfl
      A.1
  /-
  `rw [hSpecA]` は `A` の型が `terminalRawTail a` に依存するため危険。
  必要な affine context を congrArg で直接作用させる。
  -/
  have hSpecA_scaled :
      (2 : ℤ) ^
            (beattyIndex a - beattyIndex (a - 1)) *
            P.terminalRawTail a -
          (3 : ℤ) ^ (P.m - a) =
        (2 : ℤ) ^
            (beattyIndex a - beattyIndex (a - 1)) *
            ((3 : ℤ) ^ (P.m - a) *
              P.integralCriticalTailStateInt
                A a le_rfl A.1) -
          (3 : ℤ) ^ (P.m - a) := by
    exact
      congrArg
        (fun z : ℤ =>
          (2 : ℤ) ^
                (beattyIndex a - beattyIndex (a - 1)) *
              z -
            (3 : ℤ) ^ (P.m - a))
        hSpecA
  have hLen :
      P.m - (a - 1) =
        (P.m - a) + 1 := by
    have ham : a ≤ P.m := A.1
    omega
  constructor
  · exact hPredLeM
  · refine ⟨Zprev, ?_⟩
    rw [hLen, pow_succ]
    calc
      P.terminalRawTail (a - 1)
          =
        (2 : ℤ) ^
              (beattyIndex a - beattyIndex (a - 1)) *
              P.terminalRawTail a -
            (3 : ℤ) ^ (P.m - a) := hRaw
      _ =
        (2 : ℤ) ^
              (beattyIndex a - beattyIndex (a - 1)) *
              ((3 : ℤ) ^ (P.m - a) *
                P.integralCriticalTailStateInt
                  A a le_rfl A.1) -
            (3 : ℤ) ^ (P.m - a) := hSpecA_scaled
      _ =
        (3 : ℤ) ^ (P.m - a) *
          ((2 : ℤ) ^
                (beattyIndex a - beattyIndex (a - 1)) *
                P.integralCriticalTailStateInt
                  A a le_rfl A.1 -
              1) := by
        ring
      _ =
        (3 : ℤ) ^ (P.m - a) *
          (3 * Zprev) := by
        rw [hBracket]
      _ =
        ((3 : ℤ) ^ (P.m - a) * 3) *
          Zprev := by
        ring

/--
criticalization start の一つ左から square が始まると、
root shift `r` で state return は不可能。

return を仮定すると square の first-symbol rigidity から
predecessor bracket が生じ、それにより integral critical tail を
`a-1` まで延長できるため、criticalization start の minimality に矛盾する。
-/
theorem criticalizationStart_state_ne_of_square
    (P : PureBProfileObstruction)
    {r : ℕ}
    (hStartPos : 0 < P.criticalizationStart)
    (hrTwo : 2 ≤ r)
    (hEnd :
      P.criticalizationStart + 2 * r - 1 ≤ P.m)
    (B :
      CriticalBeattySquareAt
        (P.criticalizationStart - 1) r) :
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
  let A : IsIntegralCriticalTail P a :=
    P.criticalizationStart_spec

  have haPos :
      0 < a := by
    simpa [a] using hStartPos

  have hEndA :
      a + 2 * r - 1 ≤ P.m := by
    simpa [a] using hEnd

  have hSquareA :
      CriticalBeattySquareAt (a - 1) r := by
    simpa [a] using B

  have hReturnA :
      P.integralCriticalTailStateInt
          A
          (a + r)
          (by omega)
          (by omega) =
        P.integralCriticalTailStateInt
          A
          a
          le_rfl
          A.1 := by
    simpa [a, A] using hReturn

  obtain ⟨Zprev, hBracket⟩ :=
    P.exists_predecessorBracket_of_square_return
      A
      haPos
      hrTwo
      hEndA
      hSquareA
      hReturnA

  have hPrev :
      IsIntegralCriticalTail P (a - 1) :=
    P.integralCriticalTail_pred_of_bracket
      A
      haPos
      hBracket

  have hMin0 :=
    P.criticalizationStart_minimal hPrev

  have hMin :
      a ≤ a - 1 := by
    simpa [a] using hMin0

  have hPredLt :
      a - 1 < a :=
    Nat.sub_lt haPos (by norm_num)

  exact (not_lt_of_ge hMin) hPredLt

/--
local square rigidity の主定理。

criticalization start の直前から root `r>=2` の square が始まり、square 全体が
integral tail 内に収まれば

  2^(r-1) <= 4*yNat.
-/
theorem criticalizationStart_square_dyadic_bound
    (P : PureBProfileObstruction)
    (hy : 0 ≤ P.y)
    {r : ℕ}
    (hStartPos : 0 < P.criticalizationStart)
    (hrTwo : 2 ≤ r)
    (hEnd : P.criticalizationStart + 2 * r - 1 ≤ P.m)
    (B : CriticalBeattySquareAt (P.criticalizationStart - 1) r) :
    2 ^ (r - 1) ≤ 4 * P.yNat := by
  let a := P.criticalizationStart
  let A : IsIntegralCriticalTail P a := P.criticalizationStart_spec
  let F : ℕ := beattyIndex (a + r - 1) - beattyIndex a
  let Za : ℤ := P.integralCriticalTailStateInt A a le_rfl A.1
  let Zr : ℤ :=
    P.integralCriticalTailStateInt A (a + r) (by omega) (by omega)
  let D : ℤ := Zr - Za
  have hDiv0 :=
    P.twoPow_tailRise_dvd_stateDifference_of_square
      hStartPos hrTwo hEnd B
  have hDiv : (2 : ℤ) ^ F ∣ D := by
    simpa [F, D, Zr, Za, a, A] using hDiv0
  have hNe0 :=
    P.criticalizationStart_state_ne_of_square
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
  have hPowPos : 0 < (2 : ℤ) ^ F := by positivity
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
  have hLenRise : r - 1 ≤ F := by
    dsimp [F]
    have h := intervalLength_le_beattyRise a (r - 1)
    have hEndEq : a + (r - 1) = a + r - 1 := by omega
    simpa [hEndEq] using h
  have hPowLe : 2 ^ (r - 1) ≤ 2 ^ F :=
    Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hLenRise
  exact le_trans hPowLe hBoundNat

end PureBProfileObstruction

end ExternalArithmetic
end CSTMicro
end Collatz2
