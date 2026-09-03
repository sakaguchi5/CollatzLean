import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBTerminalState

/-!
# Pure B: maximal integral critical tail

`IsTerminalCriticalSuffix P a` は profile 自身が `[a,m)` で critical roof に戻るという
幾何条件である。一方、後段の Xi / Christoffel calculus が本当に必要とするのは

  3^(m-s) ∣ terminalRawTail(s)

という整数可解性である。

ここではこの二つを分離し、profile がまだ noncritical でも critical recurrence が
整数のまま通る区間を `IsIntegralCriticalTail P a` として定義する。

重要な点は、full-depth が一つの start で成立すれば右側へ自動的に伝播することである。
従って `m` 自身から始めて最小 start を取ると canonical な
`criticalizationStart` が得られる。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/--
`a` から terminal まで critical backward equation が full 3-adic depth で整数化できる。
右側への伝播は theorem として導くため、定義には start 一点の divisibility だけを持つ。
-/
def IsIntegralCriticalTail
    (P : PureBProfileObstruction)
    (a : ℕ) : Prop :=
  a ≤ P.m ∧
    (3 : ℤ) ^ (P.m - a) ∣ P.terminalRawTail a

/-- critical tail が整数化可能かどうかは判定可能。 -/
instance instDecidableIsIntegralCriticalTail
    (P : PureBProfileObstruction) :
    DecidablePred (IsIntegralCriticalTail P) := by
  intro a
  unfold IsIntegralCriticalTail
  infer_instance

namespace IsIntegralCriticalTail

/-- terminal 自身は常に integral critical tail の start。 -/
theorem terminal
    (P : PureBProfileObstruction) :
    IsIntegralCriticalTail P P.m := by
  constructor
  · exact le_rfl
  · simp

/-- genuine terminal critical suffix は integral critical tail を与える。 -/
theorem of_terminalCriticalSuffix
    {P : PureBProfileObstruction}
    {a : ℕ}
    (S : IsTerminalCriticalSuffix P a) :
    IsIntegralCriticalTail P a := by
  exact ⟨S.1, P.terminalRawTail_dvd S⟩

end IsIntegralCriticalTail

namespace PureBProfileObstruction

/-- raw tail の profile 非依存 one-cell identity。 -/
theorem terminalRawTail_step_raw
    (P : PureBProfileObstruction)
    {s : ℕ}
    (hsm : s < P.m) :
    P.terminalRawTail s =
      (2 : ℤ) ^ (beattyIndex (s + 1) - beattyIndex s) *
          P.terminalRawTail (s + 1) -
        (3 : ℤ) ^ (P.m - (s + 1)) := by
  have hPhi :=
    criticalIntervalPhiZ_concat
      (a := s) (c := s + 1) (b := P.m)
      (by omega) (by omega)
  rw [criticalIntervalPhiZ_step_eq_one_stage8] at hPhi
  have hBetaMono1 : beattyIndex s ≤ beattyIndex (s + 1) :=
    le_of_lt (beattyIndex_lt_succ s)
  have hBetaMono2 : beattyIndex (s + 1) ≤ beattyIndex P.m := by
    by_cases heq : s + 1 = P.m
    · rw [← heq]
    · exact le_of_lt (beattyIndex_strictMono (by omega))
  have hBetaSplit :
      beattyIndex P.m - beattyIndex s =
        (beattyIndex (s + 1) - beattyIndex s) +
          (beattyIndex P.m - beattyIndex (s + 1)) := by
    omega
  unfold terminalRawTail
  rw [hBetaSplit, pow_add, hPhi]
  ring

/-- full-depth は一つ右の column へ必ず伝播する。 -/
theorem integralCriticalTail_succ
    (P : PureBProfileObstruction)
    {s : ℕ}
    (A : IsIntegralCriticalTail P s)
    (hsm : s < P.m) :
    IsIntegralCriticalTail P (s + 1) := by
  constructor
  · omega
  · let d := P.m - (s + 1)
    let g := beattyIndex (s + 1) - beattyIndex s
    have hRaw := P.terminalRawTail_step_raw hsm
    have hLen : P.m - s = d + 1 := by
      dsimp [d]
      omega
    rcases A.2 with ⟨z, hz⟩
    have hz' :
        P.terminalRawTail s =
          (3 : ℤ) ^ d * (3 * z) := by
      rw [hz, hLen, pow_succ]
      ring
    have hProd :
        (3 : ℤ) ^ d ∣
          (2 : ℤ) ^ g * P.terminalRawTail (s + 1) := by
      refine ⟨3 * z + 1, ?_⟩
      dsimp [g]
      calc
        (2 : ℤ) ^ (beattyIndex (s + 1) - beattyIndex s) *
            P.terminalRawTail (s + 1)
            = P.terminalRawTail s + (3 : ℤ) ^ d := by
                dsimp [d] at hRaw ⊢
                linarith
        _ = (3 : ℤ) ^ d * (3 * z + 1) := by
              rw [hz']
              ring
    exact
      (threePow_isCoprime_twoPow d g).dvd_of_dvd_mul_left hProd

/-- full-depth start から任意の右側 start へ伝播する。 -/
theorem integralCriticalTail_of_le
    (P : PureBProfileObstruction)
    {a s : ℕ}
    (A : IsIntegralCriticalTail P a)
    (has : a ≤ s)
    (hsm : s ≤ P.m) :
    IsIntegralCriticalTail P s := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le has
  induction d with
  | zero =>
      simpa using A
  | succ d ih =>
      have hPrevLe : a + d ≤ P.m := by
        omega
      have hPrev : a + d < P.m := by
        omega
      have hIH :
          IsIntegralCriticalTail P (a + d) :=
        ih (by omega) hPrevLe
      have hStep :=
        P.integralCriticalTail_succ hIH hPrev
      simpa [Nat.add_assoc] using hStep

/-- integral critical tail の canonical integer state。 -/
def integralCriticalTailStateInt
    (P : PureBProfileObstruction)
    {a : ℕ}
    (A : IsIntegralCriticalTail P a)
    (s : ℕ)
    (has : a ≤ s)
    (hsm : s ≤ P.m) : ℤ :=
  Int.divExact
    (P.terminalRawTail s)
    ((3 : ℤ) ^ (P.m - s))
    (P.integralCriticalTail_of_le A has hsm).2

/-- canonical state の exact specification。 -/
theorem integralCriticalTailStateInt_spec
    (P : PureBProfileObstruction)
    {a s : ℕ}
    (A : IsIntegralCriticalTail P a)
    (has : a ≤ s)
    (hsm : s ≤ P.m) :
    P.terminalRawTail s =
      (3 : ℤ) ^ (P.m - s) *
        P.integralCriticalTailStateInt A s has hsm := by
  unfold integralCriticalTailStateInt
  rw [Int.divExact_eq_ediv]
  exact
    (Int.mul_ediv_cancel'
      (P.integralCriticalTail_of_le A has hsm).2).symm

/-- state quotient の一意性。 -/
theorem integralCriticalTailStateInt_unique
    (P : PureBProfileObstruction)
    {s : ℕ}
    {z₁ z₂ : ℤ}
    (h₁ : P.terminalRawTail s = (3 : ℤ) ^ (P.m - s) * z₁)
    (h₂ : P.terminalRawTail s = (3 : ℤ) ^ (P.m - s) * z₂) :
    z₁ = z₂ := by
  have hPowNe : (3 : ℤ) ^ (P.m - s) ≠ 0 := by positivity
  apply mul_left_cancel₀ hPowNe
  linarith

/-- terminal state は exact に `2y`。 -/
theorem integralCriticalTailStateInt_at_terminal
    (P : PureBProfileObstruction)
    {a : ℕ}
    (A : IsIntegralCriticalTail P a) :
    P.integralCriticalTailStateInt A P.m A.1 le_rfl = 2 * P.y := by
  apply P.integralCriticalTailStateInt_unique
  · exact P.integralCriticalTailStateInt_spec A A.1 le_rfl
  · simp [terminalRawTail, criticalIntervalPhiZ]

/-- integral critical tail の one-cell recurrence。 -/
theorem integralCriticalTailStateInt_step
    (P : PureBProfileObstruction)
    {a s : ℕ}
    (A : IsIntegralCriticalTail P a)
    (has : a ≤ s)
    (hsm : s < P.m) :
    (2 : ℤ) ^ (beattyIndex (s + 1) - beattyIndex s) *
        P.integralCriticalTailStateInt A (s + 1) (by omega) (by omega) =
      3 * P.integralCriticalTailStateInt A s has (by omega) + 1 := by
  let Zs := P.integralCriticalTailStateInt A s has (by omega : s ≤ P.m)
  let Zn := P.integralCriticalTailStateInt A (s + 1) (by omega) (by omega)
  have hSpecS := P.integralCriticalTailStateInt_spec A has (by omega : s ≤ P.m)
  have hSpecN := P.integralCriticalTailStateInt_spec A (s := s + 1) (by omega) (by omega)
  have hRaw := P.terminalRawTail_step_raw hsm
  have hLen : P.m - s = (P.m - (s + 1)) + 1 := by omega
  rw [hLen, pow_succ] at hSpecS
  have hScaled :
      (3 : ℤ) ^ (P.m - (s + 1)) *
          ((2 : ℤ) ^ (beattyIndex (s + 1) - beattyIndex s) * Zn - 1) =
        (3 : ℤ) ^ (P.m - (s + 1)) * (3 * Zs) := by
    calc
      (3 : ℤ) ^ (P.m - (s + 1)) *
          ((2 : ℤ) ^ (beattyIndex (s + 1) - beattyIndex s) * Zn - 1)
          =
        (2 : ℤ) ^ (beattyIndex (s + 1) - beattyIndex s) *
            ((3 : ℤ) ^ (P.m - (s + 1)) * Zn) -
          (3 : ℤ) ^ (P.m - (s + 1)) := by ring
      _ =
        (2 : ℤ) ^ (beattyIndex (s + 1) - beattyIndex s) *
            P.terminalRawTail (s + 1) -
          (3 : ℤ) ^ (P.m - (s + 1)) := by
            rw [← hSpecN]
      _ = P.terminalRawTail s := by
            rw [hRaw]
      _ = (3 : ℤ) ^ (P.m - (s + 1)) * (3 * Zs) := by
            rw [hSpecS]
            ring
  have hPowNe : (3 : ℤ) ^ (P.m - (s + 1)) ≠ 0 := by positivity
  have hCancel := mul_left_cancel₀ hPowNe hScaled
  dsimp [Zs, Zn] at hCancel ⊢
  linarith

/-- 右隣 state が非負なら現在 state も非負。 -/
theorem integralCriticalTailStateInt_nonneg_of_succ
    (P : PureBProfileObstruction)
    {a s : ℕ}
    (A : IsIntegralCriticalTail P a)
    (has : a ≤ s)
    (hsm : s < P.m)
    (hNext :
      0 ≤ P.integralCriticalTailStateInt A (s + 1) (by omega) (by omega)) :
    0 ≤ P.integralCriticalTailStateInt A s has (by omega) := by
  have hStep := P.integralCriticalTailStateInt_step A has hsm
  have hLeft :
      0 ≤
        (2 : ℤ) ^ (beattyIndex (s + 1) - beattyIndex s) *
          P.integralCriticalTailStateInt A (s + 1) (by omega) (by omega) := by
    exact mul_nonneg (by positivity) hNext
  rw [hStep] at hLeft
  omega

/-- terminal から距離 `d` だけ戻した integral state は非負。 -/
theorem integralCriticalTailStateInt_nonneg_at_sub
    (P : PureBProfileObstruction)
    {a d : ℕ}
    (A : IsIntegralCriticalTail P a)
    (hy : 0 ≤ P.y)
    (hd : d ≤ P.m - a) :
    0 ≤
      P.integralCriticalTailStateInt
        A
        (P.m - d)
        (by
          have ha : a ≤ P.m := A.1
          omega)
        (by omega) := by
  induction d with
  | zero =>
      simp only [Nat.sub_zero]
      rw [P.integralCriticalTailStateInt_at_terminal A]
      positivity
  | succ d ih =>
      have hdPrev : d ≤ P.m - a := by omega
      have hNext := ih hdPrev
      let u : ℕ := P.m - (d + 1)
      have huA : a ≤ u := by
        dsimp [u]
        omega
      have huLt : u < P.m := by
        dsimp [u]
        omega
      have huSucc : u + 1 = P.m - d := by
        dsimp [u]
        omega
      have hNextU :
          0 ≤ P.integralCriticalTailStateInt A (u + 1) (by omega) (by omega) := by
        simpa [huSucc] using hNext
      have hCurrent :=
        P.integralCriticalTailStateInt_nonneg_of_succ A huA huLt hNextU
      simpa [u] using hCurrent

/-- integral critical tail の全 state は `y>=0` の下で非負。 -/
theorem integralCriticalTailStateInt_nonneg
    (P : PureBProfileObstruction)
    {a s : ℕ}
    (A : IsIntegralCriticalTail P a)
    (hy : 0 ≤ P.y)
    (has : a ≤ s)
    (hsm : s ≤ P.m) :
    0 ≤ P.integralCriticalTailStateInt A s has hsm := by
  have hd : P.m - s ≤ P.m - a := by omega
  have h := P.integralCriticalTailStateInt_nonneg_at_sub A hy hd
  have hEq : P.m - (P.m - s) = s := by omega
  simpa [hEq] using h

/-- integral critical tail state も同じ uniform `<=4y` bound を持つ。 -/
theorem integralCriticalTailStateInt_le_four_y
    (P : PureBProfileObstruction)
    {a s : ℕ}
    (A : IsIntegralCriticalTail P a)
    (hy : 0 ≤ P.y)
    (has : a ≤ s)
    (hsm : s ≤ P.m) :
    P.integralCriticalTailStateInt A s has hsm ≤ 4 * P.y := by
  have hSpec := P.integralCriticalTailStateInt_spec A has hsm
  have hStateNonneg := P.integralCriticalTailStateInt_nonneg A hy has hsm
  have hPhiNonneg := criticalIntervalPhiZ_nonneg s P.m
  have hRawLe :
      (3 : ℤ) ^ (P.m - s) * P.integralCriticalTailStateInt A s has hsm ≤
        (2 : ℤ) ^ (beattyIndex P.m - beattyIndex s) * (2 * P.y) := by
    dsimp [terminalRawTail] at hSpec
    linarith
  have hBeta := beattyIndex_sub_le_beattyIndex_sub_add_one hsm
  have hTwoNat :
      2 ^ (beattyIndex P.m - beattyIndex s) ≤
        2 * 3 ^ (P.m - s) := by
    calc
      2 ^ (beattyIndex P.m - beattyIndex s)
          ≤ 2 ^ (beattyIndex (P.m - s) + 1) :=
        Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hBeta
      _ = 2 * 2 ^ beattyIndex (P.m - s) := by
        rw [pow_succ]
        ring
      _ ≤ 2 * 3 ^ (P.m - s) :=
        Nat.mul_le_mul_left 2 (beattyIndex_lower (P.m - s))
  have hTwo :
      (2 : ℤ) ^ (beattyIndex P.m - beattyIndex s) ≤
        2 * (3 : ℤ) ^ (P.m - s) := by
    exact_mod_cast hTwoNat
  have hYNonneg : (0 : ℤ) ≤ 2 * P.y := by positivity
  have hScaled :
      (3 : ℤ) ^ (P.m - s) * P.integralCriticalTailStateInt A s has hsm ≤
        (3 : ℤ) ^ (P.m - s) * (4 * P.y) := by
    calc
      (3 : ℤ) ^ (P.m - s) * P.integralCriticalTailStateInt A s has hsm
          ≤ (2 : ℤ) ^ (beattyIndex P.m - beattyIndex s) * (2 * P.y) := hRawLe
      _ ≤ (2 * (3 : ℤ) ^ (P.m - s)) * (2 * P.y) :=
        mul_le_mul_of_nonneg_right hTwo hYNonneg
      _ = (3 : ℤ) ^ (P.m - s) * (4 * P.y) := by ring
  have hPowPos : 0 < (3 : ℤ) ^ (P.m - s) := by positivity
  nlinarith

/-- nonnegative integral critical state の Nat version。 -/
noncomputable def integralCriticalTailStateNat
    (P : PureBProfileObstruction)
    {a : ℕ}
    (A : IsIntegralCriticalTail P a)
    (_hy : 0 ≤ P.y)
    (s : ℕ)
    (has : a ≤ s)
    (hsm : s ≤ P.m) : ℕ :=
  (P.integralCriticalTailStateInt A s has hsm).toNat

/-- Nat state の cast。 -/
theorem integralCriticalTailStateNat_cast
    (P : PureBProfileObstruction)
    {a s : ℕ}
    (A : IsIntegralCriticalTail P a)
    (hy : 0 ≤ P.y)
    (has : a ≤ s)
    (hsm : s ≤ P.m) :
    (P.integralCriticalTailStateNat A hy s has hsm : ℤ) =
      P.integralCriticalTailStateInt A s has hsm := by
  unfold integralCriticalTailStateNat
  exact Int.toNat_of_nonneg
    (P.integralCriticalTailStateInt_nonneg A hy has hsm)

/-- Nat state は `4*yNat` 以下。 -/
theorem integralCriticalTailStateNat_le_four_yNat
    (P : PureBProfileObstruction)
    {a s : ℕ}
    (A : IsIntegralCriticalTail P a)
    (hy : 0 ≤ P.y)
    (has : a ≤ s)
    (hsm : s ≤ P.m) :
    P.integralCriticalTailStateNat A hy s has hsm ≤ 4 * P.yNat := by
  have h := P.integralCriticalTailStateInt_le_four_y A hy has hsm
  rw [← P.yNat_cast hy] at h
  rw [← P.integralCriticalTailStateNat_cast A hy has hsm] at h
  exact_mod_cast h

/-- integral state の arbitrary interval transport。 -/
theorem integralCriticalTailStateInt_interval_transport
    (P : PureBProfileObstruction)
    {a s r : ℕ}
    (A : IsIntegralCriticalTail P a)
    (has : a ≤ s)
    (hend : s + r ≤ P.m) :
    (2 : ℤ) ^ (beattyIndex (s + r) - beattyIndex s) *
        P.integralCriticalTailStateInt A (s + r) (by omega) hend =
      (3 : ℤ) ^ r * P.integralCriticalTailStateInt A s has (by omega) +
        criticalIntervalPhiZ s (s + r) := by
  let t := s + r
  let d := P.m - t
  let Zs := P.integralCriticalTailStateInt A s has (by omega : s ≤ P.m)
  let Zt := P.integralCriticalTailStateInt A t (by omega) (by simpa [t] using hend)
  have hSpecS := P.integralCriticalTailStateInt_spec A has (by omega : s ≤ P.m)
  have hSpecT := P.integralCriticalTailStateInt_spec A (s := t) (by omega) (by simpa [t] using hend)
  have hPhi :=
    criticalIntervalPhiZ_concat
      (a := s) (c := t) (b := P.m)
      (by dsimp [t]; omega) (by simpa [t] using hend)
  have hBetaST : beattyIndex s ≤ beattyIndex t := by
    by_cases hr0 : r = 0
    · subst r
      dsimp [t]
      exact le_rfl
    · exact le_of_lt (beattyIndex_strictMono (by dsimp [t]; omega))
  have hBetaTM : beattyIndex t ≤ beattyIndex P.m := by
    by_cases hEq : t = P.m
    · rw [hEq]
    · exact le_of_lt (beattyIndex_strictMono (by omega))
  have hBetaSplit :
      beattyIndex P.m - beattyIndex s =
        (beattyIndex t - beattyIndex s) +
          (beattyIndex P.m - beattyIndex t) := by
    omega
  have hLenS : P.m - s = d + r := by
    dsimp [d, t]
    omega
  have hLenT : P.m - t = d := by rfl
  dsimp [terminalRawTail, Zs, Zt] at hSpecS hSpecT
  rw [hBetaSplit, pow_add, hLenS, pow_add] at hSpecS
  rw [hLenT] at hSpecT
  rw [hPhi] at hSpecS
  have hScaled :
      (3 : ℤ) ^ d *
          ((2 : ℤ) ^ (beattyIndex t - beattyIndex s) * Zt -
            criticalIntervalPhiZ s t) =
        (3 : ℤ) ^ d * ((3 : ℤ) ^ r * Zs) := by
    calc
      (3 : ℤ) ^ d *
          ((2 : ℤ) ^ (beattyIndex t - beattyIndex s) * Zt -
            criticalIntervalPhiZ s t)
          =
        (2 : ℤ) ^ (beattyIndex t - beattyIndex s) *
            ((3 : ℤ) ^ d * Zt) -
          (3 : ℤ) ^ d * criticalIntervalPhiZ s t := by ring
      _ =
        (2 : ℤ) ^ (beattyIndex t - beattyIndex s) *
            ((2 : ℤ) ^ (beattyIndex P.m - beattyIndex t) * (2 * P.y) -
              criticalIntervalPhiZ t P.m) -
          (3 : ℤ) ^ d * criticalIntervalPhiZ s t := by
            rw [← hSpecT]
      _ = (3 : ℤ) ^ d * ((3 : ℤ) ^ r * Zs) := by
            linear_combination hSpecS
  have hPowNe : (3 : ℤ) ^ d ≠ 0 := by positivity
  have hCancel := mul_left_cancel₀ hPowNe hScaled
  dsimp [t, Zs, Zt] at hCancel ⊢
  linarith

/-- origin raw tail と profile numerator の exact relation。 -/
theorem terminalRawTail_zero_eq_profile_balance
    (P : PureBProfileObstruction) :
    P.terminalRawTail 0 =
      (3 : ℤ) ^ P.m * (P.y - (P.q : ℤ)) -
        (profileDyadicCellNumerator P.m P.h : ℤ) := by
  have hDeep := P.deep_profile_defect
  have hGap := P.gap_cast_eq_twoPow_terminal_sub_threePow
  have hPhi0 := criticalPrefixPhiZ_eq_interval_zero P.m
  have hRaw :
      P.terminalRawTail 0 =
        (2 : ℤ) ^ (beattyIndex P.m + 1) * P.y -
          criticalPrefixPhiZ P.m := by
    unfold terminalRawTail
    rw [beattyIndex_zero, Nat.sub_zero, ← hPhi0]
    rw [pow_succ]
    ring
  rw [hRaw]
  have hGapColumn :
      (columnLayerGap P.H P.m : ℤ) =
        (2 : ℤ) ^ (beattyIndex P.m + 1) - (3 : ℤ) ^ P.m := by
    simpa [PureBProfileObstruction.gap] using hGap
  rw [hGapColumn] at hDeep
  linear_combination -hDeep

/-- origin full-depth と global profile numerator の `3^m` divisibility は同値。 -/
theorem originIntegralCriticalTail_iff_profileNumerator_dvd
    (P : PureBProfileObstruction) :
    IsIntegralCriticalTail P 0 ↔
      (3 : ℤ) ^ P.m ∣
        (profileDyadicCellNumerator P.m P.h : ℤ) := by
  constructor
  · intro A
    have hRaw := P.terminalRawTail_zero_eq_profile_balance
    rcases A.2 with ⟨u, hu⟩
    refine ⟨P.y - (P.q : ℤ) - u, ?_⟩
    rw [hRaw] at hu
    simp only [Nat.sub_zero] at hu
    linear_combination -hu
  · intro hN
    constructor
    · omega
    · have hRaw := P.terminalRawTail_zero_eq_profile_balance
      rcases hN with ⟨u, hu⟩
      refine ⟨P.y - (P.q : ℤ) - u, ?_⟩
      rw [hRaw, hu]
      ring_nf
      simp

/-- integral tail start は必ず存在する。 -/
theorem exists_integralCriticalTailStart
    (P : PureBProfileObstruction) :
    ∃ a : ℕ, IsIntegralCriticalTail P a := by
  exact ⟨P.m, IsIntegralCriticalTail.terminal P⟩

/--
`P` の integral critical tail start を有限集合として列挙する。
候補は `0, ..., P.m` だけなので完全に計算可能。
-/
def integralCriticalTailStarts
    (P : PureBProfileObstruction) : Finset ℕ :=
  (Finset.range (P.m + 1)).filter
    (fun a => IsIntegralCriticalTail P a)

/-- integral critical tail start の有限集合は空でない。 -/
theorem integralCriticalTailStarts_nonempty
    (P : PureBProfileObstruction) :
    P.integralCriticalTailStarts.Nonempty := by
  refine ⟨P.m, ?_⟩
  rw [integralCriticalTailStarts, Finset.mem_filter]
  exact
    ⟨Finset.mem_range.mpr (Nat.lt_succ_self P.m),
      IsIntegralCriticalTail.terminal P⟩

/-- 最左の integral critical tail start。 -/
def criticalizationStart
    (P : PureBProfileObstruction) : ℕ :=
  P.integralCriticalTailStarts.min'
    P.integralCriticalTailStarts_nonempty

/-- canonical start は integral critical tail。 -/
theorem criticalizationStart_spec
    (P : PureBProfileObstruction) :
    IsIntegralCriticalTail P P.criticalizationStart := by
  have hMem :
      P.criticalizationStart ∈
        P.integralCriticalTailStarts := by
    unfold criticalizationStart
    exact
      Finset.min'_mem
        P.integralCriticalTailStarts
        P.integralCriticalTailStarts_nonempty
  exact (Finset.mem_filter.mp hMem).2

/-- canonical start より左には full-depth start はない。 -/
theorem criticalizationStart_minimal
    (P : PureBProfileObstruction)
    {a : ℕ}
    (A : IsIntegralCriticalTail P a) :
    P.criticalizationStart ≤ a := by
  have haMem :
      a ∈ P.integralCriticalTailStarts := by
    rw [integralCriticalTailStarts, Finset.mem_filter]
    exact
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le A.1), A⟩
  unfold criticalizationStart
  exact
    Finset.min'_le
      P.integralCriticalTailStarts
      a
      haMem

/-- arithmetic criticalization は geometric terminal critical suffix より左か同じ。 -/
theorem criticalizationStart_le_terminalCriticalStart
    (P : PureBProfileObstruction) :
    P.criticalizationStart ≤ P.terminalCriticalStart := by
  exact
    P.criticalizationStart_minimal
      (IsIntegralCriticalTail.of_terminalCriticalSuffix P.terminalCriticalStart_spec)

end PureBProfileObstruction

end ExternalArithmetic
end CSTMicro
end Collatz2
