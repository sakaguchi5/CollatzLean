import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBProfileNumeratorValuation
import CollatzLean.Collatz2.CSTMicro.CarryGeometry.ProfileCostClosedForm

/-!
# Pure B: geometric terminal start と noncritical profile core の exact 3-adic order

`c = terminalCriticalStart` 以右では `h(k)=0` なので profile numerator の closed form

  N_m(h) = Σ_{k<m} D_k 3^(m-k-1)

は

  N_m(h) = 3^(m-c) N_c(h)

と exact に factor する。
ここで `N_c(h)` を terminal noncritical profile core と呼ぶ。

前段の

  v_3(N_m(h)) = m-a,
  a = criticalizationStart,

と `a <= c` を合わせると

  v_3(core) = c-a.

従って arithmetic criticalization と geometric criticalization の corridor width は、
右端 noncritical profile core の exact 3-adic cancellation depth そのものになる。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

namespace PureBProfileObstruction

/-- geometric terminal start より左側だけを local terminal exponent で畳んだ core。 -/
noncomputable def terminalNoncriticalProfileCore
    (P : PureBProfileObstruction) : ℕ :=
  profileDyadicClosedNumerator P.terminalCriticalStart P.h

/-- terminal critical suffix の zero columns を除くと global numerator は core times `3^(m-c)`。 -/
theorem profileNumerator_cast_eq_threePow_mul_terminalCore
    (P : PureBProfileObstruction) :
    (profileDyadicCellNumerator P.m P.h : ℤ) =
      (3 : ℤ) ^ (P.m - P.terminalCriticalStart) *
        (P.terminalNoncriticalProfileCore : ℤ) := by
  let c := P.terminalCriticalStart
  have S : IsTerminalCriticalSuffix P c := by
    simpa [c] using P.terminalCriticalStart_spec
  have hc : c ≤ P.m := S.1
  have hClosed := profileDyadicCellNumerator_eq_closed P.admissible
  have hSplit :=
    Finset.sum_range_add
      (f := fun k => profileDyadicClosedColumn P.m k (P.h k))
      c (P.m - c)
  have hMass : c + (P.m - c) = P.m := by omega
  rw [hMass] at hSplit
  have hTailZero :
      Finset.sum (Finset.range (P.m - c))
          (fun i => profileDyadicClosedColumn P.m (c + i) (P.h (c + i))) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hiLt : i < P.m - c := Finset.mem_range.mp hi
    have hci : c ≤ c + i := by omega
    have hcim : c + i < P.m := by omega
    have hZero := S.2 (c + i) hci hcim
    simp [profileDyadicClosedColumn, hZero]
  have hFirst :
      Finset.sum (Finset.range c)
          (fun k => profileDyadicClosedColumn P.m k (P.h k)) =
        3 ^ (P.m - c) *
          profileDyadicClosedNumerator c P.h := by
    unfold profileDyadicClosedNumerator
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hkLt : k < c := Finset.mem_range.mp hk
    have hExp :
        P.m - (k + 1) =
          (P.m - c) + (c - (k + 1)) := by
      omega
    unfold profileDyadicClosedColumn
    rw [hExp, pow_add]
    ring
  have hNat :
      profileDyadicCellNumerator P.m P.h =
        3 ^ (P.m - c) * profileDyadicClosedNumerator c P.h := by
    calc
      profileDyadicCellNumerator P.m P.h
          =
        profileDyadicClosedNumerator P.m P.h :=
        hClosed
      _ =
        Finset.sum (Finset.range P.m)
          (fun k =>
            profileDyadicClosedColumn P.m k (P.h k)) := by
        rfl
      _ =
        Finset.sum (Finset.range c)
            (fun k =>
              profileDyadicClosedColumn P.m k (P.h k)) +
          Finset.sum (Finset.range (P.m - c))
            (fun i =>
              profileDyadicClosedColumn
                P.m (c + i) (P.h (c + i))) :=
        hSplit
      _ =
        Finset.sum (Finset.range c)
          (fun k =>
            profileDyadicClosedColumn P.m k (P.h k)) := by
        rw [hTailZero, Nat.add_zero]
      _ =
        3 ^ (P.m - c) *
          profileDyadicClosedNumerator c P.h :=
        hFirst
  have hCast := congrArg (fun n : ℕ => (n : ℤ)) hNat
  push_cast at hCast
  simpa [terminalNoncriticalProfileCore, c] using hCast

/--
`3^e * z` の exact order `e+r` から、factor `z` の exact order `r` を cancel する。
-/
theorem exactThreeAdicOrder_of_threePow_mul
    {e r : ℕ}
    {z : ℤ}
    (h : ExactThreeAdicOrder ((3 : ℤ) ^ e * z) (e + r)) :
    ExactThreeAdicOrder z r := by
  constructor
  · rcases h.1 with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have hEq :
        (3 : ℤ) ^ e * z =
          (3 : ℤ) ^ e * ((3 : ℤ) ^ r * k) := by
      calc
        (3 : ℤ) ^ e * z
            = (3 : ℤ) ^ (e + r) * k := hk
        _ = (3 : ℤ) ^ e * ((3 : ℤ) ^ r * k) := by
              rw [pow_add]
              ring
    exact mul_left_cancel₀ (pow_ne_zero _ (by norm_num : (3 : ℤ) ≠ 0)) hEq
  · intro hDeep
    apply h.2
    rcases hDeep with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    calc
      (3 : ℤ) ^ e * z
          = (3 : ℤ) ^ e * ((3 : ℤ) ^ (r + 1) * k) := by rw [hk]
      _ = (3 : ℤ) ^ ((e + r) + 1) * k := by
            rw [show (e + r) + 1 = e + (r + 1) by omega, pow_add]
            ring

/-- terminal noncritical core の exact 3-adic order は geometric/arithmetic start の差。 -/
theorem terminalCore_exactThreeAdicOrder
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart) :
    ExactThreeAdicOrder
      (P.terminalNoncriticalProfileCore : ℤ)
      (P.terminalCriticalStart - P.criticalizationStart) := by
  have hStartLe :
      P.criticalizationStart ≤ P.terminalCriticalStart :=
    P.criticalizationStart_le_terminalCriticalStart
  have hTerminalLe : P.terminalCriticalStart ≤ P.m :=
    P.terminalCriticalStart_spec.1
  have hExp :
      P.m - P.criticalizationStart =
        (P.m - P.terminalCriticalStart) +
          (P.terminalCriticalStart - P.criticalizationStart) := by
    omega
  have hN := P.profileNumerator_exactThreeAdicOrder_at_criticalization hStart
  rw [P.profileNumerator_cast_eq_threePow_mul_terminalCore] at hN
  rw [hExp] at hN
  exact exactThreeAdicOrder_of_threePow_mul hN

/-- corridor が正なら terminal core は 3 で割れる。逆も exact order から従う。 -/
theorem three_dvd_terminalCore_iff_criticalization_lt_terminalCriticalStart
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart) :
    (3 : ℤ) ∣ (P.terminalNoncriticalProfileCore : ℤ) ↔
      P.criticalizationStart < P.terminalCriticalStart := by
  have hLe := P.criticalizationStart_le_terminalCriticalStart
  have hExact := P.terminalCore_exactThreeAdicOrder hStart
  constructor
  · intro hThree
    by_contra hnot
    have hEq : P.criticalizationStart = P.terminalCriticalStart := by omega
    have hZero :
        P.terminalCriticalStart - P.criticalizationStart = 0 := by omega
    have hNot := hExact.2
    rw [hZero] at hNot
    norm_num at hNot
    exact hNot hThree
  · intro hLt
    have hPos :
        0 < P.terminalCriticalStart - P.criticalizationStart := by omega
    have hPowDvd :
        (3 : ℤ) ∣
          (3 : ℤ) ^
            (P.terminalCriticalStart - P.criticalizationStart) := by
      refine ⟨(3 : ℤ) ^
          (P.terminalCriticalStart - P.criticalizationStart - 1), ?_⟩
      have hExp :
          P.terminalCriticalStart - P.criticalizationStart =
            1 + (P.terminalCriticalStart - P.criticalizationStart - 1) := by
        omega
      rw [hExp, pow_add]
      norm_num
    exact hPowDvd.trans hExact.1

/-- core が 3-adic unit であることと arithmetic/geometric start の一致は同値。 -/
theorem not_three_dvd_terminalCore_iff_criticalization_eq_terminalCriticalStart
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart) :
    (¬ (3 : ℤ) ∣ (P.terminalNoncriticalProfileCore : ℤ)) ↔
      P.criticalizationStart = P.terminalCriticalStart := by
  have hLe := P.criticalizationStart_le_terminalCriticalStart
  have hIff :=
    P.three_dvd_terminalCore_iff_criticalization_lt_terminalCriticalStart hStart
  constructor
  · intro hNot
    by_contra hNe
    have hLt : P.criticalizationStart < P.terminalCriticalStart := by omega
    exact hNot (hIff.2 hLt)
  · intro hEq hThree
    have hLt := hIff.1 hThree
    omega

end PureBProfileObstruction

namespace MinimalActualABObstructionPacket

/-- actual minimal B の noncritical corridor width も terminal core の exact order。 -/
theorem terminalCore_exactThreeAdicOrder
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    ExactThreeAdicOrder
      ((M.toPureBProfileObstruction hL).terminalNoncriticalProfileCore : ℤ)
      ((M.toPureBProfileObstruction hL).terminalCriticalStart -
        (M.toPureBProfileObstruction hL).criticalizationStart) := by
  let P := M.toPureBProfileObstruction hL
  have hPos : 0 < P.criticalizationStart := by
    simpa [P] using M.criticalizationStart_pos R hL
  simpa [P] using P.terminalCore_exactThreeAdicOrder hPos

/-- actual B では core が 3-adic unit なら arithmetic/geometric starts は一致する。 -/
theorem criticalization_eq_terminalCriticalStart_of_terminalCore_not_three_dvd
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (hUnit :
      ¬ (3 : ℤ) ∣
        ((M.toPureBProfileObstruction hL).terminalNoncriticalProfileCore : ℤ)) :
    (M.toPureBProfileObstruction hL).criticalizationStart =
      (M.toPureBProfileObstruction hL).terminalCriticalStart := by
  let P := M.toPureBProfileObstruction hL
  have hPos : 0 < P.criticalizationStart := by
    simpa [P] using M.criticalizationStart_pos R hL
  exact
    (P.not_three_dvd_terminalCore_iff_criticalization_eq_terminalCriticalStart hPos).1
      (by simpa [P] using hUnit)

end MinimalActualABObstructionPacket

end ExternalArithmetic
end CSTMicro
end Collatz2
