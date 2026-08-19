import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.TerminalCriticalRecord
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBProfileBlockReduction
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.BoundaryACandidate
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.RhinLinearForm14
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalIntervalPhasePeriodicity

/-!
# Pure B terminal suffix -> small Xi tail states

terminal critical suffix `h(k)=0` を pure B deep equationへ代入すると、任意 suffix start `s` で

  3^(m-s) | 2^(beta_m-beta_s) (2y) - Phi[s,m]

が得られる。この quotient を tail state `Z_s` とする。

* `Z_m = 2y`,
* `2^g Z_(s+1) = 3 Z_s + 1`,
* actual B 由来で `y>=0` なら `0 <= Z_s <= 4y`,
* first-carry record `[s,s+r)` では

    2^Q Z_(s+r) = 3^r Z_s + Psi(r),

  かつ `beta_r <= Q`。

従って `Z_s` は precision `beta_r` の `BoundaryXiCandidate` になる。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

open scoped BigOperators

/-- pure profile が `[a,m)` で critical roof に戻っていること。 -/
def IsTerminalCriticalSuffix
    (P : PureBProfileObstruction)
    (a : ℕ) : Prop :=
  a ≤ P.m ∧
    ∀ k : ℕ, a ≤ k → k < P.m → P.h k = 0

namespace PureBProfileObstruction

/-- `a=m` は常に terminal critical suffix。 -/
theorem exists_terminalCriticalSuffix
    (P : PureBProfileObstruction) :
    ∃ a : ℕ, IsTerminalCriticalSuffix P a := by
  refine ⟨P.m, le_rfl, ?_⟩
  intro k hmk hkm
  omega

/-- 最長 terminal critical suffix の canonical start。 -/
noncomputable def terminalCriticalStart
    (P : PureBProfileObstruction) : ℕ := by
  classical
  exact Nat.find P.exists_terminalCriticalSuffix

/-- canonical start は実際に terminal critical suffix を与える。 -/
theorem terminalCriticalStart_spec
    (P : PureBProfileObstruction) :
    IsTerminalCriticalSuffix P P.terminalCriticalStart := by
  classical
  exact Nat.find_spec P.exists_terminalCriticalSuffix

/-- canonical start より前から terminal critical suffix を始めることはできない。 -/
theorem terminalCriticalStart_minimal
    (P : PureBProfileObstruction)
    {a : ℕ}
    (ha : IsTerminalCriticalSuffix P a) :
    P.terminalCriticalStart ≤ a := by
  classical
  exact Nat.find_min' P.exists_terminalCriticalSuffix ha

/-- canonical terminal critical suffix length `t`。 -/
noncomputable def terminalCriticalLength
    (P : PureBProfileObstruction) : ℕ :=
  P.m - terminalCriticalStart P


end PureBProfileObstruction

namespace IsTerminalCriticalSuffix

/-- terminal criticality は suffix start を右へ動かしても保存される。 -/
theorem restrict
    {P : PureBProfileObstruction}
    {a s : ℕ}
    (S : IsTerminalCriticalSuffix P a)
    (has : a ≤ s)
    (hsm : s ≤ P.m) :
    IsTerminalCriticalSuffix P s := by
  refine ⟨hsm, ?_⟩
  intro k hsk hkm
  exact S.2 k (le_trans has hsk) hkm

end IsTerminalCriticalSuffix

namespace PureBProfileObstruction

/-- pure packet equation を profile affine numerator の形で読む。 -/
theorem profileAffine_sub_gap_mul_y_eq_deep
    (P : PureBProfileObstruction) :
    (profileAffineNumerator P.m P.h : ℤ) -
        (P.gap : ℤ) * P.y =
      (3 : ℤ) ^ P.m * (P.q : ℤ) := by
  calc
    (profileAffineNumerator P.m P.h : ℤ) - (P.gap : ℤ) * P.y
        = P.profileDefect := by
            rw [P.profileDefect_eq_profileAffine_sub_gap_mul_y]
    _ = (3 : ℤ) ^ P.m * (P.q : ℤ) :=
      P.profileDefect_eq_threePow_mul_q

/-- profile affine numerator の各 term は `3^m` 以下。 -/
theorem profileAffineTerm_le_threePow_m
    (P : PureBProfileObstruction)
    {k : ℕ}
    (hk : k < P.m) :
    2 ^ profileCheckpoint P.h k * 3 ^ (P.m - (k + 1)) ≤
      3 ^ P.m := by
  have hCheckpoint : profileCheckpoint P.h k ≤ beattyIndex k := by
    unfold profileCheckpoint
    omega
  have hTwo :
      2 ^ profileCheckpoint P.h k ≤ 2 ^ beattyIndex k :=
    Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hCheckpoint
  have hBeatty : 2 ^ beattyIndex k ≤ 3 ^ k := beattyIndex_lower k
  have hExp : P.m - (k + 1) ≤ P.m - k := by omega
  have hThree :
      3 ^ (P.m - (k + 1)) ≤ 3 ^ (P.m - k) :=
    Nat.pow_le_pow_right (by omega : 0 < (3 : ℕ)) hExp
  calc
    2 ^ profileCheckpoint P.h k * 3 ^ (P.m - (k + 1))
        ≤ 3 ^ k * 3 ^ (P.m - k) :=
      Nat.mul_le_mul (le_trans hTwo hBeatty) hThree
    _ = 3 ^ (k + (P.m - k)) := by rw [pow_add]
    _ = 3 ^ P.m := by
      congr 1
      omega

/-- profile affine numerator 全体の粗い bound。 -/
theorem profileAffineNumerator_le_m_mul_threePow
    (P : PureBProfileObstruction) :
    profileAffineNumerator P.m P.h ≤ P.m * 3 ^ P.m := by
  unfold profileAffineNumerator
  calc
    Finset.sum (Finset.range P.m)
        (fun k => 2 ^ profileCheckpoint P.h k * 3 ^ (P.m - (k + 1)))
      ≤ Finset.sum (Finset.range P.m) (fun _ => 3 ^ P.m) := by
        apply Finset.sum_le_sum
        intro k hk
        exact P.profileAffineTerm_le_threePow_m (Finset.mem_range.mp hk)
    _ = P.m * 3 ^ P.m := by simp

/-- nonnegative integer witness を Nat に戻す。 -/
def yNat (P : PureBProfileObstruction) : ℕ := P.y.toNat

/-- `y>=0` の下で yNat の cast は元の integer witness。 -/
theorem yNat_cast
    (P : PureBProfileObstruction)
    (hy : 0 ≤ P.y) :
    (P.yNat : ℤ) = P.y := by
  exact Int.toNat_of_nonneg hy

/-- actual B 由来の y に対する Rhin polynomial bound。 -/
theorem yNat_le_rhinPolynomial
    (R : RhinLinearForm14)
    (P : PureBProfileObstruction)
    (hy : 0 ≤ P.y) :
    P.yNat ≤ rhinGapK * (P.m + 1) ^ 15 := by
  have hEq := P.profileAffine_sub_gap_mul_y_eq_deep
  have hyCast := P.yNat_cast hy
  rw [← hyCast] at hEq
  have hGapAffineZ :
      (P.gap : ℤ) * (P.yNat : ℤ) ≤
        (profileAffineNumerator P.m P.h : ℤ) := by
    have hDeepNonneg :
        (0 : ℤ) ≤ (3 : ℤ) ^ P.m * (P.q : ℤ) := by positivity
    linarith
  have hGapAffine :
      P.gap * P.yNat ≤ profileAffineNumerator P.m P.h := by
    exact_mod_cast hGapAffineZ
  have hAffineBound := P.profileAffineNumerator_le_m_mul_threePow
  have hContract : 3 ^ P.m < 2 ^ P.H := by
    have hGapPos : 0 < 2 ^ P.H - 3 ^ P.m := by
      simpa [PureBProfileObstruction.gap, columnLayerGap] using P.gap_pos
    exact Nat.sub_pos_iff_lt.mp hGapPos
  have hmPos : 0 < P.m := by
    have hm := P.one_lt_m
    omega
  have hGapRhin :=
    R.boundaryGap P.m P.H hmPos hContract
  have hGapEq : 2 ^ P.H - 3 ^ P.m = P.gap := by
    rfl
  rw [hGapEq] at hGapRhin
  have hScaled :
      P.gap * P.yNat ≤
        P.gap * (rhinGapK * (P.m + 1) ^ 15) := by
    calc
      P.gap * P.yNat
          ≤ profileAffineNumerator P.m P.h := hGapAffine
      _ ≤ P.m * 3 ^ P.m := hAffineBound
      _ ≤ P.m * (rhinGapK * (P.m + 1) ^ 14 * P.gap) :=
        Nat.mul_le_mul_left P.m hGapRhin
      _ = P.gap * (rhinGapK * (P.m + 1) ^ 14 * P.m) := by ring
      _ ≤ P.gap * (rhinGapK * (P.m + 1) ^ 14 * (P.m + 1)) := by
        exact Nat.mul_le_mul_left P.gap
          (Nat.mul_le_mul_left (rhinGapK * (P.m + 1) ^ 14)
            (Nat.le_succ P.m))
      _ = P.gap * (rhinGapK * (P.m + 1) ^ 15) := by
        rw [show (15 : ℕ) = 14 + 1 by norm_num, pow_succ]
        ring
  by_contra hnot
  have hgt : rhinGapK * (P.m + 1) ^ 15 < P.yNat := by
    omega
  have hmul := Nat.mul_lt_mul_of_pos_left hgt P.gap_pos
  exact (not_lt_of_ge hScaled) hmul

/-- full-m exponents を持つ prefix part。 -/
def profileAffinePrefixZ
    (P : PureBProfileObstruction)
    (a : ℕ) : ℤ :=
  Finset.sum (Finset.range a)
    (fun k =>
      (2 : ℤ) ^ profileCheckpoint P.h k *
        (3 : ℤ) ^ (P.m - (k + 1)))

/-- local exponentsを持つ同じ prefix part。 -/
def profileAffineLocalPrefixZ
    (P : PureBProfileObstruction)
    (a : ℕ) : ℤ :=
  Finset.sum (Finset.range a)
    (fun k =>
      (2 : ℤ) ^ profileCheckpoint P.h k *
        (3 : ℤ) ^ (a - (k + 1)))

/-- full prefix part は `3^(m-a)` を exact に因数として持つ。 -/
theorem profileAffinePrefixZ_factor
    (P : PureBProfileObstruction)
    {a : ℕ}
    (ha : a ≤ P.m) :
    P.profileAffinePrefixZ a =
      (3 : ℤ) ^ (P.m - a) * P.profileAffineLocalPrefixZ a := by
  unfold profileAffinePrefixZ profileAffineLocalPrefixZ
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hkMem
  have hk : k < a := Finset.mem_range.mp hkMem
  have hExp :
      P.m - (k + 1) = (P.m - a) + (a - (k + 1)) := by
    omega
  rw [hExp, pow_add]
  ring

/-- terminal critical suffix では profile affine numerator の suffix が critical interval numerator。 -/
theorem profileAffineNumerator_cast_eq_prefix_add_criticalInterval
    (P : PureBProfileObstruction)
    {a : ℕ}
    (S : IsTerminalCriticalSuffix P a) :
    (profileAffineNumerator P.m P.h : ℤ) =
      P.profileAffinePrefixZ a +
        (2 : ℤ) ^ beattyIndex a * criticalIntervalPhiZ a P.m := by
  classical
  let f : ℕ → ℤ := fun k =>
    (2 : ℤ) ^ profileCheckpoint P.h k *
      (3 : ℤ) ^ (P.m - (k + 1))
  have hCast :
      (profileAffineNumerator P.m P.h : ℤ) =
        Finset.sum (Finset.range P.m) f := by
    unfold profileAffineNumerator
    push_cast
    rfl
  have ha : a ≤ P.m := S.1
  have hm : P.m = a + (P.m - a) := by omega
  have hSplit :
      Finset.sum (Finset.range P.m) f =
        Finset.sum (Finset.range a) f +
          Finset.sum (Finset.range (P.m - a)) (fun i => f (a + i)) := by
    rw [hm, Finset.sum_range_add]
    simp
    rfl
  rw [hCast, hSplit]
  have hPrefix :
      Finset.sum (Finset.range a) f = P.profileAffinePrefixZ a := by
    rfl
  rw [hPrefix]
  congr 1
  unfold criticalIntervalPhiZ
  rw [CriticalRecordPiece.sum_Ico_eq_sum_range_sub_public
    (fun k =>
      (2 : ℤ) ^ (beattyIndex k - beattyIndex a) *
        (3 : ℤ) ^ (P.m - 1 - k)) S.1]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hiMem
  have hi : i < P.m - a := Finset.mem_range.mp hiMem
  have hai : a ≤ a + i := by omega
  have haim : a + i < P.m := by omega
  have hzero := S.2 (a + i) hai haim
  have hCheckpoint :
      profileCheckpoint P.h (a + i) = beattyIndex (a + i) := by
    unfold profileCheckpoint
    rw [hzero]
    simp
  have hBetaMono : beattyIndex a ≤ beattyIndex (a + i) := by
    by_cases hi0 : i = 0
    · subst i
      exact le_rfl
    · exact le_of_lt (beattyIndex_strictMono (by omega))
  have hBeta :
      beattyIndex (a + i) =
        beattyIndex a + (beattyIndex (a + i) - beattyIndex a) := by
    omega
  have hThree :
      P.m - (a + i + 1) = P.m - 1 - (a + i) := by
    omega
  dsimp [f]
  rw [hCheckpoint, hBeta, pow_add, hThree]
  ring_nf
  simp


/-- terminal gap の integer form。 -/
theorem gap_cast_eq_twoPow_terminal_sub_threePow
    (P : PureBProfileObstruction) :
    (P.gap : ℤ) =
      (2 : ℤ) ^ (beattyIndex P.m + 1) - (3 : ℤ) ^ P.m := by
  have h := P.gap_cast_eq_criticalPrefixGapZ_add_twoPow
  rw [h]
  unfold criticalPrefixGapZ
  rw [pow_succ]
  ring

/-- 3-power は shorter terminal depth を割る。 -/
theorem threePow_sub_dvd_threePow
    {a m : ℕ}
    (ha : a ≤ m) :
    (3 : ℤ) ^ (m - a) ∣ (3 : ℤ) ^ m := by
  refine ⟨(3 : ℤ) ^ a, ?_⟩
  have hm : m = (m - a) + a := by omega
  rw [hm, pow_add]
  ring_nf
  simp
  ac_rfl

/-- 3-power と 2-power は整数環で coprime。 -/
theorem threePow_isCoprime_twoPow
    (a b : ℕ) :
    IsCoprime ((3 : ℤ) ^ a) ((2 : ℤ) ^ b) := by
  have hBase : IsCoprime (3 : ℤ) (2 : ℤ) := by
    refine ⟨1, -1, ?_⟩
    norm_num
  exact hBase.pow

/--
terminal critical suffix の raw tail numerator は自分の suffix length だけ3で割れる。
-/
theorem terminalRawTail_dvd
    (P : PureBProfileObstruction)
    {a : ℕ}
    (S : IsTerminalCriticalSuffix P a) :
    (3 : ℤ) ^ (P.m - a) ∣
      (2 : ℤ) ^ (beattyIndex P.m - beattyIndex a) * (2 * P.y) -
        criticalIntervalPhiZ a P.m := by
  have hAffine :=
    P.profileAffineNumerator_cast_eq_prefix_add_criticalInterval S
  have hDeep := P.profileAffine_sub_gap_mul_y_eq_deep
  rw [hAffine, P.gap_cast_eq_twoPow_terminal_sub_threePow] at hDeep
  have ha : a ≤ P.m := S.1
  have hBetaMono : beattyIndex a ≤ beattyIndex P.m := by
    by_cases ham : a = P.m
    · subst a
      exact le_rfl
    · exact le_of_lt (beattyIndex_strictMono (by omega))
  have hBetaSplit :
      beattyIndex P.m =
        beattyIndex a + (beattyIndex P.m - beattyIndex a) := by
    omega
  have hTwoExp :
      beattyIndex P.m + 1 =
        beattyIndex a + ((beattyIndex P.m - beattyIndex a) + 1) := by
    omega
  have hTwoTerminal :
      (2 : ℤ) ^ (beattyIndex P.m + 1) =
        (2 : ℤ) ^ beattyIndex a *
          ((2 : ℤ) ^ (beattyIndex P.m - beattyIndex a) * 2) := by
    rw [hTwoExp, pow_add, pow_succ]
  rw [hTwoTerminal] at hDeep
  have hPrefixFactor := P.profileAffinePrefixZ_factor S.1
  rw [hPrefixFactor] at hDeep
  let d := P.m - a
  let raw : ℤ :=
    criticalIntervalPhiZ a P.m -
      (2 : ℤ) ^ (beattyIndex P.m - beattyIndex a) * (2 * P.y)
  have hEq :
      (2 : ℤ) ^ beattyIndex a * raw =
        (3 : ℤ) ^ P.m * ((P.q : ℤ) - P.y) -
          (3 : ℤ) ^ d * P.profileAffineLocalPrefixZ a := by
    dsimp [raw, d]
    linarith
  have hDvdM : (3 : ℤ) ^ d ∣ (3 : ℤ) ^ P.m := by
    dsimp [d]
    exact threePow_sub_dvd_threePow S.1
  have hRightDvd :
      (3 : ℤ) ^ d ∣
        (3 : ℤ) ^ P.m * ((P.q : ℤ) - P.y) -
          (3 : ℤ) ^ d * P.profileAffineLocalPrefixZ a := by
    apply dvd_sub
    · exact dvd_mul_of_dvd_left hDvdM _
    · refine ⟨P.profileAffineLocalPrefixZ a, ?_⟩
      ring
  have hProductDvd :
      (3 : ℤ) ^ d ∣ (2 : ℤ) ^ beattyIndex a * raw := by
    rw [hEq]
    exact hRightDvd
  have hRawDvd : (3 : ℤ) ^ d ∣ raw :=
    (threePow_isCoprime_twoPow d (beattyIndex a)).dvd_of_dvd_mul_left hProductDvd
  have hNeg : (3 : ℤ) ^ d ∣ -raw := dvd_neg.mpr hRawDvd
  simpa [raw, d] using hNeg

/-- suffix start `s` 用の raw numerator。 -/
def terminalRawTail
    (P : PureBProfileObstruction)
    (s : ℕ) : ℤ :=
  (2 : ℤ) ^ (beattyIndex P.m - beattyIndex s) * (2 * P.y) -
    criticalIntervalPhiZ s P.m

/-- terminal suffix の任意 sub-suffix で raw tail divisibility。 -/
theorem terminalRawTail_dvd_of_inside
    (P : PureBProfileObstruction)
    {a s : ℕ}
    (S : IsTerminalCriticalSuffix P a)
    (has : a ≤ s)
    (hsm : s ≤ P.m) :
    (3 : ℤ) ^ (P.m - s) ∣ P.terminalRawTail s := by
  have Ss := S.restrict has hsm
  simpa [terminalRawTail] using P.terminalRawTail_dvd Ss

/-- divisibility の canonical integer quotient。 -/
noncomputable def terminalTailStateInt
    (P : PureBProfileObstruction)
    {a : ℕ}
    (S : IsTerminalCriticalSuffix P a)
    (s : ℕ)
    (has : a ≤ s)
    (hsm : s ≤ P.m) : ℤ :=
  Classical.choose (P.terminalRawTail_dvd_of_inside S has hsm)

/-- tail state の exact specification。 -/
theorem terminalTailStateInt_spec
    (P : PureBProfileObstruction)
    {a : ℕ}
    (S : IsTerminalCriticalSuffix P a)
    (s : ℕ)
    (has : a ≤ s)
    (hsm : s ≤ P.m) :
    P.terminalRawTail s =
      (3 : ℤ) ^ (P.m - s) *
        P.terminalTailStateInt S s has hsm := by
  exact Classical.choose_spec (P.terminalRawTail_dvd_of_inside S has hsm)

/-- tail state quotient は一意。 -/
theorem terminalTailStateInt_unique
    (P : PureBProfileObstruction)
    {s : ℕ}
    (_hsm : s ≤ P.m)
    {z₁ z₂ : ℤ}
    (h₁ : P.terminalRawTail s = (3 : ℤ) ^ (P.m - s) * z₁)
    (h₂ : P.terminalRawTail s = (3 : ℤ) ^ (P.m - s) * z₂) :
    z₁ = z₂ := by
  have hPowNe : (3 : ℤ) ^ (P.m - s) ≠ 0 := by positivity
  apply mul_left_cancel₀ hPowNe
  linarith

/-- terminal state は exact に `2y`。 -/
theorem terminalTailStateInt_at_terminal
    (P : PureBProfileObstruction)
    {a : ℕ}
    (S : IsTerminalCriticalSuffix P a) :
    P.terminalTailStateInt S P.m S.1 le_rfl = 2 * P.y := by
  apply P.terminalTailStateInt_unique le_rfl
  · exact P.terminalTailStateInt_spec S P.m S.1 le_rfl
  · simp [terminalRawTail, criticalIntervalPhiZ]

/-- adjacent Beatty rise は正。 -/
theorem beattyIndex_succ_sub_pos (s : ℕ) :
    0 < beattyIndex (s + 1) - beattyIndex s := by
  have h := beattyIndex_lt_succ s
  omega

/-- tail states の one-cell recurrence。 -/
theorem terminalTailStateInt_step
    (P : PureBProfileObstruction)
    {a s : ℕ}
    (S : IsTerminalCriticalSuffix P a)
    (has : a ≤ s)
    (hsm : s < P.m) :
    (2 : ℤ) ^ (beattyIndex (s + 1) - beattyIndex s) *
        P.terminalTailStateInt S (s + 1) (by omega) (by omega) =
      3 * P.terminalTailStateInt S s has (by omega) + 1 := by
  let Zs := P.terminalTailStateInt S s has (by omega : s ≤ P.m)
  let Zn := P.terminalTailStateInt S (s + 1) (by omega) (by omega)
  have hSpecS := P.terminalTailStateInt_spec S s has (by omega : s ≤ P.m)
  have hSpecN := P.terminalTailStateInt_spec S (s + 1) (by omega) (by omega)
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
  have hLenSplit :
      P.m - s = (P.m - (s + 1)) + 1 := by omega
  dsimp [terminalRawTail, Zs, Zn] at hSpecS hSpecN
  rw [hBetaSplit, pow_add, hLenSplit, pow_succ] at hSpecS
  rw [hPhi] at hSpecS
  have hPowD : (3 : ℤ) ^ (P.m - (s + 1)) ≠ 0 := by positivity
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
            ((2 : ℤ) ^ (beattyIndex P.m - beattyIndex (s + 1)) * (2 * P.y) -
              criticalIntervalPhiZ (s + 1) P.m) -
          (3 : ℤ) ^ (P.m - (s + 1)) := by
            rw [← hSpecN]
      _ = (3 : ℤ) ^ (P.m - (s + 1)) * (3 * Zs) := by
            linear_combination hSpecS
  have hCancel := mul_left_cancel₀ hPowD hScaled
  dsimp [Zs, Zn] at hCancel ⊢
  linarith

/--
one-cell recurrence

  2^g Z_(s+1) = 3 Z_s + 1

において、右隣の state が非負なら現在の state も非負。
-/
theorem terminalTailStateInt_nonneg_of_succ
    (P : PureBProfileObstruction)
    {a s : ℕ}
    (S : IsTerminalCriticalSuffix P a)
    (has : a ≤ s)
    (hsm : s < P.m)
    (hNext :
      0 ≤
        P.terminalTailStateInt
          S (s + 1) (by omega) (by omega)) :
    0 ≤ P.terminalTailStateInt S s has (by omega) := by
  have hStep :=
    P.terminalTailStateInt_step S has hsm
  have hLeft :
      0 ≤
        (2 : ℤ) ^ (beattyIndex (s + 1) - beattyIndex s) *
          P.terminalTailStateInt
            S (s + 1) (by omega) (by omega) := by
    exact mul_nonneg (by positivity) hNext
  rw [hStep] at hLeft
  /-
  0 ≤ 3 * Z_s + 1
  から、Z_s が整数であることを使って 0 ≤ Z_s。
  Z_s ≤ -1 なら右辺 ≤ -2 なので矛盾。
  -/
  omega


/--
terminal `Z_m = 2y` から `d` cell 左へ戻った state は非負。

induction の index を `P.m - d` に固定しておくことで、
main theorem から distance induction の bookkeeping を分離する。
-/
theorem terminalTailStateInt_nonneg_at_sub
    (P : PureBProfileObstruction)
    {a d : ℕ}
    (S : IsTerminalCriticalSuffix P a)
    (hy : 0 ≤ P.y)
    (hd : d ≤ P.m - a) :
    0 ≤
      P.terminalTailStateInt
        S
        (P.m - d)
        (by
          have ha : a ≤ P.m := S.1
          omega)
        (by omega) := by
  induction d with
  | zero =>
      simp only [Nat.sub_zero]
      rw [P.terminalTailStateInt_at_terminal S]
      positivity
  | succ d ih =>
      have hdPrev : d ≤ P.m - a := by
        omega
      have hNext :=
        ih hdPrev
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
          0 ≤
            P.terminalTailStateInt
              S (u + 1) (by omega) (by omega) := by
        simpa [huSucc] using hNext
      have hCurrent :=
        P.terminalTailStateInt_nonneg_of_succ
          S huA huLt hNextU
      /-
      ここで初めて
        u = P.m - (d+1)
      を明示的に戻す。

      これを omega 内部に任せないことが重要。
      -/
      simpa [u] using hCurrent

/-- tail state は `y >= 0` の下で非負。 -/
theorem terminalTailStateInt_nonneg
    (P : PureBProfileObstruction)
    {a s : ℕ}
    (S : IsTerminalCriticalSuffix P a)
    (hy : 0 ≤ P.y)
    (has : a ≤ s)
    (hsm : s ≤ P.m) :
    0 ≤ P.terminalTailStateInt S s has hsm := by
  have ha : a ≤ P.m := S.1
  have hd :
      P.m - s ≤ P.m - a := by
    omega
  have h :=
    P.terminalTailStateInt_nonneg_at_sub
      (d := P.m - s) S hy hd
  have hEq :
      P.m - (P.m - s) = s := by
    omega
  simpa [hEq] using h

/-- interval numerator は nonnegative。 -/
theorem criticalIntervalPhiZ_nonneg (a b : ℕ) :
    0 ≤ criticalIntervalPhiZ a b := by
  unfold criticalIntervalPhiZ
  apply Finset.sum_nonneg
  intro k hk
  positivity

/-- Beatty difference は origin difference +1 以下。 -/
theorem beattyIndex_sub_le_beattyIndex_sub_add_one
    {s m : ℕ}
    (hsm : s ≤ m) :
    beattyIndex m - beattyIndex s ≤ beattyIndex (m - s) + 1 := by
  have hm : m = s + (m - s) := by omega
  have hAdd := beattyIndex_add_eq_add_carry s (m - s)
  rw [← hm] at hAdd
  have hCarry := Collatz2.Word.criticalCarry_le_one s (m - s)
  omega

/-- tail state の uniform `<= 4y` bound。 -/
theorem terminalTailStateInt_le_four_y
    (P : PureBProfileObstruction)
    {a s : ℕ}
    (S : IsTerminalCriticalSuffix P a)
    (hy : 0 ≤ P.y)
    (has : a ≤ s)
    (hsm : s ≤ P.m) :
    P.terminalTailStateInt S s has hsm ≤ 4 * P.y := by
  have hSpec := P.terminalTailStateInt_spec S s has hsm
  have hStateNonneg := P.terminalTailStateInt_nonneg S hy has hsm
  have hPhiNonneg := criticalIntervalPhiZ_nonneg s P.m
  have hRawLe :
      (3 : ℤ) ^ (P.m - s) * P.terminalTailStateInt S s has hsm ≤
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
      (3 : ℤ) ^ (P.m - s) * P.terminalTailStateInt S s has hsm ≤
        (3 : ℤ) ^ (P.m - s) * (4 * P.y) := by
    calc
      (3 : ℤ) ^ (P.m - s) * P.terminalTailStateInt S s has hsm
          ≤ (2 : ℤ) ^ (beattyIndex P.m - beattyIndex s) * (2 * P.y) := hRawLe
      _ ≤ (2 * (3 : ℤ) ^ (P.m - s)) * (2 * P.y) :=
        mul_le_mul_of_nonneg_right hTwo hYNonneg
      _ = (3 : ℤ) ^ (P.m - s) * (4 * P.y) := by ring
  have hPowPos : 0 < (3 : ℤ) ^ (P.m - s) := by positivity
  nlinarith

/-- nonnegative tail state の Nat version。 -/
noncomputable def terminalTailStateNat
    (P : PureBProfileObstruction)
    {a : ℕ}
    (S : IsTerminalCriticalSuffix P a)
    (_hy : 0 ≤ P.y)
    (s : ℕ)
    (has : a ≤ s)
    (hsm : s ≤ P.m) : ℕ :=
  (P.terminalTailStateInt S s has hsm).toNat

/-- Nat tail state の cast。 -/
theorem terminalTailStateNat_cast
    (P : PureBProfileObstruction)
    {a s : ℕ}
    (S : IsTerminalCriticalSuffix P a)
    (hy : 0 ≤ P.y)
    (has : a ≤ s)
    (hsm : s ≤ P.m) :
    (P.terminalTailStateNat S hy s has hsm : ℤ) =
      P.terminalTailStateInt S s has hsm := by
  unfold terminalTailStateNat
  exact Int.toNat_of_nonneg
    (P.terminalTailStateInt_nonneg S hy has hsm)

/-- Nat tail state は global polynomial boundを持つ。 -/
theorem terminalTailStateNat_le_four_yNat
    (P : PureBProfileObstruction)
    {a s : ℕ}
    (S : IsTerminalCriticalSuffix P a)
    (hy : 0 ≤ P.y)
    (has : a ≤ s)
    (hsm : s ≤ P.m) :
    P.terminalTailStateNat S hy s has hsm ≤ 4 * P.yNat := by
  have h := P.terminalTailStateInt_le_four_y S hy has hsm
  rw [← P.yNat_cast hy] at h
  rw [← P.terminalTailStateNat_cast S hy has hsm] at h
  exact_mod_cast h

/-- tail state の arbitrary interval transport。 -/
theorem terminalTailStateInt_interval_transport
    (P : PureBProfileObstruction)
    {a s r : ℕ}
    (S : IsTerminalCriticalSuffix P a)
    (has : a ≤ s)
    (hend : s + r ≤ P.m) :
    (2 : ℤ) ^ (beattyIndex (s + r) - beattyIndex s) *
        P.terminalTailStateInt S (s + r) (by omega) hend =
      (3 : ℤ) ^ r * P.terminalTailStateInt S s has (by omega) +
        criticalIntervalPhiZ s (s + r) := by
  let t := s + r
  let d := P.m - t
  let Zs := P.terminalTailStateInt S s has (by omega : s ≤ P.m)
  let Zt := P.terminalTailStateInt S t (by omega) (by simpa [t] using hend)
  have hSpecS := P.terminalTailStateInt_spec S s has (by omega : s ≤ P.m)
  have hSpecT :=
    P.terminalTailStateInt_spec S t (by omega) (by simpa [t] using hend)
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

/-! ## finite Xi algebra -/

/-- critical prefix numerator の one-step recurrence。 -/
theorem criticalPrefixPhiZ_succ_record (r : ℕ) :
    criticalPrefixPhiZ (r + 1) =
      3 * criticalPrefixPhiZ r + (2 : ℤ) ^ beattyIndex r := by
  have h :=
    criticalPrefixPhiZ_endpoint_decomposition
      (a := r) (b := r + 1) (by omega : r ≤ r + 1)
  rw [criticalIntervalPhiZ_step_eq_one_stage8] at h
  norm_num at h
  simpa [mul_comm, mul_left_comm, mul_assoc] using h

/-- finite Xi truncation satisfies `3^r Xi_r + Psi(r)=0` in every dyadic precision。 -/
theorem criticalXiTruncationClass_threePow_add_phi_eq_zero
    (e r : ℕ) :
    (3 : ZMod (2 ^ e)) ^ r * criticalXiTruncationClass e r +
      (criticalPrefixPhiZ r : ZMod (2 ^ e)) = 0 := by
  induction r with
  | zero =>
      simp [criticalXiTruncationClass, criticalPrefixPhiZ]
  | succ r ih =>
      rw [criticalXiTruncationClass]
      rw [beattyInverseContribution_succ]
      rw [criticalPrefixPhiZ_succ_record]
      push_cast
      have hInv := threePow_mul_invThreePow e (r + 1)
      rw [pow_succ]
      have ih' :
          (3 : ZMod (2 ^ e)) ^ r *
              (-beattyInverseContribution e r) +
            (criticalPrefixPhiZ r : ZMod (2 ^ e)) = 0 := by
        simpa [criticalXiTruncationClass] using ih
      linear_combination
        3 * ih' -
          (2 : ZMod (2 ^ e)) ^ beattyIndex r * hInv

/-- integer `3^r Z + Psi(r)` が `2^e` で割れれば Z は Xi truncation class。 -/
theorem natCast_eq_criticalXi_of_threePow_add_phi_dvd
    {e r Z : ℕ}
    (hDiv :
      (2 : ℤ) ^ e ∣
        (3 : ℤ) ^ r * (Z : ℤ) + criticalPrefixPhiZ r) :
    ((Z : ℕ) : ZMod (2 ^ e)) = criticalXiTruncationClass e r := by
  have hCastZero :
      (3 : ZMod (2 ^ e)) ^ r * ((Z : ℕ) : ZMod (2 ^ e)) +
        (criticalPrefixPhiZ r : ZMod (2 ^ e)) = 0 := by
    rcases hDiv with ⟨c, hc⟩
    have hZ :
        (((3 : ℤ) ^ r * (Z : ℤ) + criticalPrefixPhiZ r : ℤ) :
            ZMod (2 ^ e)) = 0 := by
      rw [hc]
      push_cast
      have hMod :
          (2 : ZMod (2 ^ e)) ^ e = 0 := by
        have hSelf :
            (((2 ^ e : ℕ) : ZMod (2 ^ e))) = 0 :=
          ZMod.natCast_self (2 ^ e)
        simpa only [Nat.cast_pow, Nat.cast_ofNat] using hSelf
      rw [hMod]
      simp
    simpa using hZ
  have hXi := criticalXiTruncationClass_threePow_add_phi_eq_zero e r
  have hMul :
      (3 : ZMod (2 ^ e)) ^ r *
        (((Z : ℕ) : ZMod (2 ^ e)) - criticalXiTruncationClass e r) = 0 := by
    linear_combination hCastZero - hXi
  have hInv := threePow_mul_invThreePow e r
  have hDiff :
      ((Z : ℕ) : ZMod (2 ^ e)) - criticalXiTruncationClass e r = 0 := by
    calc
      ((Z : ℕ) : ZMod (2 ^ e)) - criticalXiTruncationClass e r
          = 1 *
              (((Z : ℕ) : ZMod (2 ^ e)) - criticalXiTruncationClass e r) := by
                simp
      _ =
          ((3 : ZMod (2 ^ e)) ^ r * invThreePow e r) *
            (((Z : ℕ) : ZMod (2 ^ e)) - criticalXiTruncationClass e r) := by
              rw [hInv]
      _ =
          invThreePow e r *
            ((3 : ZMod (2 ^ e)) ^ r *
              (((Z : ℕ) : ZMod (2 ^ e)) - criticalXiTruncationClass e r)) := by
              ring
      _ = 0 := by rw [hMul]; simp
  exact sub_eq_zero.mp hDiff

/-- record start tail state は precision `beta_r` の critical Xi candidate。 -/
theorem terminalRecordStart_isBoundaryXiCandidate
    (P : PureBProfileObstruction)
    {a s r : ℕ}
    (S : IsTerminalCriticalSuffix P a)
    (hy : 0 ≤ P.y)
    (has : a ≤ s)
    (hend : s + r ≤ P.m)
    (B : CriticalRecordPiece s r) :
    BoundaryXiCandidate
      (beattyIndex r)
      (P.terminalTailStateNat S hy s has (by omega)) := by
  let Zs := P.terminalTailStateNat S hy s has (by omega : s ≤ P.m)
  have hTransport :=
    P.terminalTailStateInt_interval_transport S has hend
  rw [B.intervalPhi_eq_prefixPhi] at hTransport
  have hStartCast := P.terminalTailStateNat_cast S hy has (by omega : s ≤ P.m)
  rw [← hStartCast] at hTransport
  have hQ := B.terminal_beatty_eq
  let Q := beattyIndex (s + r) - beattyIndex s
  have hEqQ : Q = beattyIndex r + 1 := by simpa [Q] using hQ
  have hDivPow :
      (2 : ℤ) ^ beattyIndex r ∣ (2 : ℤ) ^ Q := by
    rw [hEqQ]
    refine ⟨2, ?_⟩
    rw [pow_succ]
  have hDiv :
      (2 : ℤ) ^ beattyIndex r ∣
        (3 : ℤ) ^ r * (Zs : ℤ) + criticalPrefixPhiZ r := by
    rw [← hTransport]
    exact dvd_mul_of_dvd_left hDivPow _
  have hCastEq :=
    natCast_eq_criticalXi_of_threePow_add_phi_dvd hDiv
  refine ⟨r, rfl, ?_⟩
  have hVal := congrArg ZMod.val hCastEq
  simpa [ZMod.val_natCast] using hVal

/-- final no-carry fragment start も precision `beta_r` の Xi candidate。 -/
theorem terminalNoCarryStart_isBoundaryXiCandidate
    (P : PureBProfileObstruction)
    {a s r : ℕ}
    (S : IsTerminalCriticalSuffix P a)
    (hy : 0 ≤ P.y)
    (has : a ≤ s)
    (hend : s + r ≤ P.m)
    (F : CriticalNoCarryFragment s r) :
    BoundaryXiCandidate
      (beattyIndex r)
      (P.terminalTailStateNat S hy s has (by omega)) := by
  let Zs := P.terminalTailStateNat S hy s has (by omega : s ≤ P.m)
  have hTransport :=
    P.terminalTailStateInt_interval_transport S has hend
  rw [F.intervalPhi_eq_prefixPhi] at hTransport
  have hStartCast := P.terminalTailStateNat_cast S hy has (by omega : s ≤ P.m)
  rw [← hStartCast] at hTransport
  have hQ := F.terminal_beatty_eq
  have hDiv :
      (2 : ℤ) ^ beattyIndex r ∣
        (3 : ℤ) ^ r * (Zs : ℤ) + criticalPrefixPhiZ r := by
    rw [← hTransport, hQ]
    refine ⟨_, rfl⟩
  have hCastEq := natCast_eq_criticalXi_of_threePow_add_phi_dvd hDiv
  refine ⟨r, rfl, ?_⟩
  have hVal := congrArg ZMod.val hCastEq
  simpa [ZMod.val_natCast] using hVal

end PureBProfileObstruction

end ExternalArithmetic
end CSTMicro
end Collatz2
