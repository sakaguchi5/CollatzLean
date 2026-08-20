import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBIntegralTailPolylog
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.ChristoffelDefectValuation

/-!
# Pure B: criticalization start = profile numerator の exact 3-adic order

`terminalRawTail` と global profile numerator の間には、任意 cut `a <= m` で

  T(0) = 2^β(a) T(a) - 3^(m-a) Ψ(a)

という exact relation がある。
`2^β(a)` は 3-adic unit なので、これと既存 origin balance

  T(0) = 3^m (y-q) - N(h)

を合わせると

  IsIntegralCriticalTail P a
    <-> 3^(m-a) | N(h)

が得られる。

従って canonical 最左 start `a = criticalizationStart` が正なら

  v_3(N(h)) = m-a

であり、repo で既に使っていた `3^m ∤ N(h)` はその弱い帰結になる。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

namespace PureBProfileObstruction

/--
origin raw tail を任意 cut `a` の raw tail と critical prefix に分解する exact identity。
-/
theorem terminalRawTail_zero_eq_scaled_tail_sub_prefix
    (P : PureBProfileObstruction)
    {a : ℕ}
    (ha : a ≤ P.m) :
    P.terminalRawTail 0 =
      (2 : ℤ) ^ beattyIndex a * P.terminalRawTail a -
        (3 : ℤ) ^ (P.m - a) * criticalPrefixPhiZ a := by
  have hPhi :=
    criticalIntervalPhiZ_concat
      (a := 0) (c := a) (b := P.m)
      (by omega) ha
  have hBeta :
      beattyIndex a ≤ beattyIndex P.m := by
    by_cases hEq : a = P.m
    · subst a
      exact le_rfl
    · exact le_of_lt (beattyIndex_strictMono (by omega))
  have hBetaSplit :
      beattyIndex P.m =
        beattyIndex a +
          (beattyIndex P.m - beattyIndex a) := by
    omega
  rw [beattyIndex_zero, Nat.sub_zero] at hPhi
  have hPrefixA :
      criticalPrefixPhiZ a =
        criticalIntervalPhiZ 0 a := by
    exact criticalPrefixPhiZ_eq_interval_zero a
  have hBetaCancel :
      beattyIndex a +
          (beattyIndex P.m - beattyIndex a) -
        beattyIndex a =
      beattyIndex P.m - beattyIndex a := by
    omega
  unfold terminalRawTail
  rw [beattyIndex_zero, Nat.sub_zero]
  rw [hBetaSplit, pow_add]
  rw [hPhi, hPrefixA]
  rw [hBetaCancel]
  ring


/--
任意 cut `a <= m` で、arithmetic criticality は global profile numerator の
対応する 3-power divisibility と exact に同値。
-/
theorem integralCriticalTail_iff_profileNumerator_dvd_at
    (P : PureBProfileObstruction)
    {a : ℕ}
    (ha : a ≤ P.m) :
    IsIntegralCriticalTail P a ↔
      (3 : ℤ) ^ (P.m - a) ∣
        (profileDyadicCellNumerator P.m P.h : ℤ) := by
  let d := P.m - a
  have hPowDvdM : (3 : ℤ) ^ d ∣ (3 : ℤ) ^ P.m := by
    dsimp [d]
    exact threePow_sub_dvd_threePow ha
  have hMainDvd :
      (3 : ℤ) ^ d ∣
        (3 : ℤ) ^ P.m * (P.y - (P.q : ℤ)) :=
    dvd_mul_of_dvd_left hPowDvdM _
  have hPrefixDvd :
      (3 : ℤ) ^ d ∣
        (3 : ℤ) ^ d * criticalPrefixPhiZ a := by
    refine ⟨criticalPrefixPhiZ a, ?_⟩
    ring
  constructor
  · intro A
    have hTailScaled :
        (3 : ℤ) ^ d ∣
          (2 : ℤ) ^ beattyIndex a * P.terminalRawTail a :=
      dvd_mul_of_dvd_right A.2 _
    have hZeroDvd : (3 : ℤ) ^ d ∣ P.terminalRawTail 0 := by
      rw [P.terminalRawTail_zero_eq_scaled_tail_sub_prefix ha]
      exact dvd_sub hTailScaled hPrefixDvd
    have hN0 :
        (3 : ℤ) ^ d ∣
          (3 : ℤ) ^ P.m * (P.y - (P.q : ℤ)) -
            P.terminalRawTail 0 :=
      dvd_sub hMainDvd hZeroDvd
    have hBalance := P.terminalRawTail_zero_eq_profile_balance
    have hEq :
        (3 : ℤ) ^ P.m * (P.y - (P.q : ℤ)) -
            P.terminalRawTail 0 =
          (profileDyadicCellNumerator P.m P.h : ℤ) := by
      linarith
    rw [hEq] at hN0
    exact hN0
  · intro hN
    have hZero0 :
        (3 : ℤ) ^ d ∣
          (3 : ℤ) ^ P.m * (P.y - (P.q : ℤ)) -
            (profileDyadicCellNumerator P.m P.h : ℤ) :=
      dvd_sub hMainDvd hN
    have hBalance := P.terminalRawTail_zero_eq_profile_balance
    have hZeroDvd : (3 : ℤ) ^ d ∣ P.terminalRawTail 0 := by
      rw [hBalance]
      exact hZero0
    have hProduct0 :
        (3 : ℤ) ^ d ∣
          P.terminalRawTail 0 +
            (3 : ℤ) ^ d * criticalPrefixPhiZ a :=
      dvd_add hZeroDvd hPrefixDvd
    have hCut := P.terminalRawTail_zero_eq_scaled_tail_sub_prefix ha
    have hProduct :
        (3 : ℤ) ^ d ∣
          (2 : ℤ) ^ beattyIndex a * P.terminalRawTail a := by
      have hEq :
          P.terminalRawTail 0 +
              (3 : ℤ) ^ d * criticalPrefixPhiZ a =
            (2 : ℤ) ^ beattyIndex a * P.terminalRawTail a := by
        dsimp [d] at hCut ⊢
        linarith
      rw [← hEq]
      exact hProduct0
    have hTail :
        (3 : ℤ) ^ d ∣ P.terminalRawTail a :=
      (threePow_isCoprime_twoPow d (beattyIndex a)).dvd_of_dvd_mul_left hProduct
    exact ⟨ha, by simpa [d] using hTail⟩

/--
positive canonical start では profile numerator の 3-adic order は exact `m-start`。
-/
theorem profileNumerator_exactThreeAdicOrder_at_criticalization
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart) :
    ExactThreeAdicOrder
      (profileDyadicCellNumerator P.m P.h : ℤ)
      (P.m - P.criticalizationStart) := by
  let a := P.criticalizationStart
  have hA : IsIntegralCriticalTail P a := by
    simpa [a] using P.criticalizationStart_spec
  have ha : a ≤ P.m := hA.1
  constructor
  · exact
      (P.integralCriticalTail_iff_profileNumerator_dvd_at ha).1 hA
  · intro hDeep
    have haPos : 0 < a := by simpa [a] using hStart
    have hPrevLe : a - 1 ≤ P.m := by omega
    have hExp :
        P.m - (a - 1) = (P.m - a) + 1 := by
      omega
    have hPrevDvd :
        (3 : ℤ) ^ (P.m - (a - 1)) ∣
          (profileDyadicCellNumerator P.m P.h : ℤ) := by
      rw [hExp]
      simpa [a] using hDeep
    have hPrev : IsIntegralCriticalTail P (a - 1) :=
      (P.integralCriticalTail_iff_profileNumerator_dvd_at hPrevLe).2 hPrevDvd
    have hMin := P.criticalizationStart_minimal hPrev
    dsimp [a] at hMin haPos
    omega

/-- exact order の lower divisibility を直接読む wrapper。 -/
theorem threePow_criticalizationDepth_dvd_profileNumerator
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart) :
    (3 : ℤ) ^ (P.m - P.criticalizationStart) ∣
      (profileDyadicCellNumerator P.m P.h : ℤ) :=
  (P.profileNumerator_exactThreeAdicOrder_at_criticalization hStart).1

/-- criticalization depth より一段深い 3-power は profile numerator を割らない。 -/
theorem not_threePow_criticalizationDepth_succ_dvd_profileNumerator
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart) :
    ¬ (3 : ℤ) ^ (P.m - P.criticalizationStart + 1) ∣
      (profileDyadicCellNumerator P.m P.h : ℤ) := by
  simpa [Nat.add_assoc] using
    (P.profileNumerator_exactThreeAdicOrder_at_criticalization hStart).2

/--
exact order から origin full-depth exclusion `3^m ∤ N(h)` を再導出する。
-/
theorem not_threePow_m_dvd_profileNumerator_of_positive_criticalization
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart) :
    ¬ (3 : ℤ) ^ P.m ∣
      (profileDyadicCellNumerator P.m P.h : ℤ) := by
  intro hFull
  let d := P.m - P.criticalizationStart
  have hCritLe :
      P.criticalizationStart ≤ P.m :=
    (P.criticalizationStart_spec).1
  let d := P.m - P.criticalizationStart
  have hLe : d + 1 ≤ P.m := by
    dsimp [d]
    omega
  have hPow : (3 : ℤ) ^ (d + 1) ∣ (3 : ℤ) ^ P.m := by
    refine ⟨(3 : ℤ) ^ (P.m - (d + 1)), ?_⟩
    have hExp : P.m = (d + 1) + (P.m - (d + 1)) := by omega
    rw [hExp, pow_add]
    simp
  have hTooDeep :
      (3 : ℤ) ^ (d + 1) ∣
        (profileDyadicCellNumerator P.m P.h : ℤ) :=
    hPow.trans hFull
  have hExact := P.profileNumerator_exactThreeAdicOrder_at_criticalization hStart
  dsimp [d] at hTooDeep
  exact hExact.2 hTooDeep

end PureBProfileObstruction

namespace MinimalActualABObstructionPacket

/-- actual minimal B では profile numerator の exact order が canonical window width。 -/
theorem profileNumerator_exactThreeAdicOrder_at_criticalization
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    ExactThreeAdicOrder
      (profileDyadicCellNumerator
        (M.toPureBProfileObstruction hL).m
        (M.toPureBProfileObstruction hL).h : ℤ)
      ((M.toPureBProfileObstruction hL).m -
        (M.toPureBProfileObstruction hL).criticalizationStart) := by
  let P := M.toPureBProfileObstruction hL
  have hPos : 0 < P.criticalizationStart := by
    simpa [P] using M.criticalizationStart_pos R hL
  simpa [P] using P.profileNumerator_exactThreeAdicOrder_at_criticalization hPos

/-- actual B の exact order から既存 origin full-depth exclusion を再取得。 -/
theorem not_threePow_dvd_profileNumerator_from_criticalizationOrder
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    ¬ (3 : ℤ) ^ (M.toPureBProfileObstruction hL).m ∣
      (profileDyadicCellNumerator
        (M.toPureBProfileObstruction hL).m
        (M.toPureBProfileObstruction hL).h : ℤ) := by
  let P := M.toPureBProfileObstruction hL
  have hPos : 0 < P.criticalizationStart := by
    simpa [P] using M.criticalizationStart_pos R hL
  simpa [P] using
    P.not_threePow_m_dvd_profileNumerator_of_positive_criticalization hPos

end MinimalActualABObstructionPacket

end ExternalArithmetic
end CSTMicro
end Collatz2
