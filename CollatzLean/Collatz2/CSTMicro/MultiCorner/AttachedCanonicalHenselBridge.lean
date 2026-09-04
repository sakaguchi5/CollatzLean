import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedCarryNormalizedTail
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.FreeBaseMonotoneHenselChain
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.MonotoneSuffixHenselChain

/-!
# MultiCorner attached branch: canonical Hensel bridge

attached geometry から arbitrary witness `x,xNext` を仮定するのではなく、
actual closed tail から canonical quotient family を構成する。

right endpoint を

  c = terminalCriticalStart

に固定し、cut `k` に対して

  Tail(k,c)
    = 2^(carryCheckpoint(k))
      * 3^(c-k)
      * q_k

と exact に factor する。

これにより

* `q_c = 0`,
* `3 q_k = 2^e_k q_(k+1) + 2^h_k - 1`,
* previous corner の existing `AttachedCornerHenselState` は actual quotient から構成できる、
* previous+1 から terminal endpoint までは free-base monotone Hensel chain になる、

ことを示す。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

/--
criticalization corridor 内の cut では closed tail が
`2^checkpoint * 3^localWidth` を同時に因子として持つ。
-/
theorem exists_terminalCarryTailQuotient
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart)
    {k : ℕ}
    (hsk : P.criticalizationStart ≤ k)
    (hkc : k ≤ P.terminalCriticalStart) :
    ∃ q : ℤ,
      restartedClosedTailZ P k P.terminalCriticalStart =
        (2 : ℤ) ^ carryCheckpoint P P.terminalCriticalStart k *
          (3 : ℤ) ^ (P.terminalCriticalStart - k) * q := by
  have hcM : P.terminalCriticalStart ≤ P.m :=
    P.terminalCriticalStart_spec.1
  have hTwo :=
    restartedClosedTailZ_twoPow_dvd_carryCheckpoint P hkc hcM
  rcases hTwo with ⟨u, hu⟩
  have hThree :=
    restartedTail_localWidth_dvd P hStart hsk hkc
  rw [hu] at hThree
  have hThreeU :
      (3 : ℤ) ^ (P.terminalCriticalStart - k) ∣ u :=
    MonotoneSuffixHenselChain.threePow_dvd_cancel_twoPow hThree
  rcases hThreeU with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  rw [hu, hq]
  ring

/--
actual terminal tail の canonical normalized quotient。
有効範囲外では `0` とするが、bridge で使うのは corridor 内だけである。
-/
noncomputable def terminalCarryTailQuotient
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart)
    (k : ℕ) : ℤ :=
  if hk :
      P.criticalizationStart ≤ k ∧
        k ≤ P.terminalCriticalStart then
    Classical.choose
      (exists_terminalCarryTailQuotient
        P hStart hk.1 hk.2)
  else
    0

/-- canonical quotient の defining factorization。 -/
theorem terminalCarryTailQuotient_spec
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart)
    {k : ℕ}
    (hsk : P.criticalizationStart ≤ k)
    (hkc : k ≤ P.terminalCriticalStart) :
    restartedClosedTailZ P k P.terminalCriticalStart =
      (2 : ℤ) ^ carryCheckpoint P P.terminalCriticalStart k *
      (3 : ℤ) ^ (P.terminalCriticalStart - k) *
        terminalCarryTailQuotient P hStart k := by
  have hk :
      P.criticalizationStart ≤ k ∧
        k ≤ P.terminalCriticalStart :=
    ⟨hsk, hkc⟩
  unfold terminalCarryTailQuotient
  rw [dite_eq_left hk]
  exact
    Classical.choose_spec
      (exists_terminalCarryTailQuotient
        P hStart hsk hkc)

/-- corridor 内の canonical quotient は非負。 -/
theorem terminalCarryTailQuotient_nonneg
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart)
    {k : ℕ}
    (hsk : P.criticalizationStart ≤ k)
    (hkc : k ≤ P.terminalCriticalStart) :
    0 ≤ terminalCarryTailQuotient P hStart k := by
  let n := P.terminalCriticalStart - k
  have hIdx : k + n = P.terminalCriticalStart := by
    dsimp [n]
    omega
  have hTailCast :=
    profileClosedTailNat_cast_eq_restartedClosedTailZ P k n
  rw [hIdx] at hTailCast
  have hTailNonneg :
      0 ≤ restartedClosedTailZ P k P.terminalCriticalStart := by
    rw [← hTailCast]
    exact Int.natCast_nonneg _
  have hSpec :=
    terminalCarryTailQuotient_spec P hStart hsk hkc
  let F : ℤ :=
    (2 : ℤ) ^ carryCheckpoint P P.terminalCriticalStart k *
      (3 : ℤ) ^ (P.terminalCriticalStart - k)
  have hSpec' :
      restartedClosedTailZ P k P.terminalCriticalStart =
        F * terminalCarryTailQuotient P hStart k := by
    simpa [F, mul_assoc] using hSpec
  have hFPos : 0 < F := by
    dsimp [F]
    positivity
  rw [hSpec'] at hTailNonneg
  by_contra hNot
  have hQNeg : terminalCarryTailQuotient P hStart k < 0 := by
    omega
  have hProdNeg :
      F * terminalCarryTailQuotient P hStart k < 0 :=
    mul_neg_of_pos_of_neg hFPos hQNeg
  linarith

/-- right endpoint の empty tail quotient は exact に `0`。 -/
theorem terminalCarryTailQuotient_terminal
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart) :
    terminalCarryTailQuotient
      P hStart P.terminalCriticalStart = 0 := by
  have hSpec :=
    terminalCarryTailQuotient_spec
      P hStart
      P.criticalizationStart_le_terminalCriticalStart
      le_rfl
  have hZero :
      (2 : ℤ) ^
          carryCheckpoint P P.terminalCriticalStart P.terminalCriticalStart *
        terminalCarryTailQuotient P hStart P.terminalCriticalStart = 0 := by
    simpa [restartedClosedTailZ] using hSpec.symm
  have hPowNe :
      (2 : ℤ) ^
          carryCheckpoint P P.terminalCriticalStart P.terminalCriticalStart ≠ 0 := by
    positivity
  exact (mul_eq_zero.mp hZero).resolve_left hPowNe

/--
隣接 canonical quotient は actual carry gap を係数に持つ exact Hensel recurrence を満たす。
-/
theorem terminalCarryTailQuotient_recurrence
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart)
    {k : ℕ}
    (hsk : P.criticalizationStart ≤ k)
    (hkc : k < P.terminalCriticalStart) :
    3 * terminalCarryTailQuotient P hStart k =
      (2 : ℤ) ^ carryRunGap P P.terminalCriticalStart k *
          terminalCarryTailQuotient P hStart (k + 1) +
        (2 : ℤ) ^ P.h k - 1 := by
  let c := P.terminalCriticalStart
  let qk := terminalCarryTailQuotient P hStart k
  let qNext := terminalCarryTailQuotient P hStart (k + 1)
  let pk := carryCheckpoint P c k
  let e := carryRunGap P c k
  let r := c - (k + 1)
  have hcM : c ≤ P.m := P.terminalCriticalStart_spec.1
  have hNextSk : P.criticalizationStart ≤ k + 1 := by omega
  have hNextC : k + 1 ≤ c := by omega
  have hSpecK :=
    terminalCarryTailQuotient_spec P hStart hsk (Nat.le_of_lt hkc)
  have hSpecNext :=
    terminalCarryTailQuotient_spec P hStart hNextSk hNextC
  have hTail :=
    restartedClosedTailZ_left_rec P hkc
  have hMass :=
    profileRightmostColumnMass_cast_eq_pow_carryCheckpoint_mul P
      hkc hcM
  have hCheckpoint :=
    carryCheckpoint_add_carryRunGap_eq_succ P hkc hcM
  have hExp : c - k = r + 1 := by
    dsimp [c, r]
    omega
  change
    3 * qk =
      (2 : ℤ) ^ e * qNext + (2 : ℤ) ^ P.h k - 1
  change
    restartedClosedTailZ P k c =
      (2 : ℤ) ^ pk *
        (3 : ℤ) ^ (c - k) * qk
      at hSpecK
  change
    restartedClosedTailZ P (k + 1) c =
      (2 : ℤ) ^ carryCheckpoint P c (k + 1) *
        (3 : ℤ) ^ (c - (k + 1)) * qNext
      at hSpecNext
  change
    restartedClosedTailZ P k c =
      (3 : ℤ) ^ (c - (k + 1)) *
          (profileRightmostColumnMass P.h k : ℤ) +
        restartedClosedTailZ P (k + 1) c
      at hTail
  change
    (profileRightmostColumnMass P.h k : ℤ) =
      (2 : ℤ) ^ pk * ((2 : ℤ) ^ P.h k - 1)
      at hMass
  change pk + e = carryCheckpoint P c (k + 1) at hCheckpoint
  rw [hSpecK, hSpecNext, hMass] at hTail
  rw [hExp, pow_succ] at hTail
  rw [← hCheckpoint, pow_add] at hTail
  have hCommonNe :
      (2 : ℤ) ^ pk * (3 : ℤ) ^ r ≠ 0 := by
    positivity
  have hFactored :
      ((2 : ℤ) ^ pk * (3 : ℤ) ^ r) * (3 * qk) =
        ((2 : ℤ) ^ pk * (3 : ℤ) ^ r) *
          ((2 : ℤ) ^ e * qNext + (2 : ℤ) ^ P.h k - 1) := by
    dsimp [r] at hTail ⊢
    ring_nf at hTail ⊢
    nlinarith [hTail]
  exact mul_left_cancel₀ hCommonNe hFactored

/-- canonical integer quotient を existing Nat Hensel interface へ渡すための値。 -/
noncomputable def terminalCarryTailQuotientNat
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart)
    (k : ℕ) : ℕ :=
  Int.toNat (terminalCarryTailQuotient P hStart k)

/-- corridor 内では Nat 化しても値を失わない。 -/
theorem terminalCarryTailQuotientNat_cast
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart)
    {k : ℕ}
    (hsk : P.criticalizationStart ≤ k)
    (hkc : k ≤ P.terminalCriticalStart) :
    (terminalCarryTailQuotientNat P hStart k : ℤ) =
      terminalCarryTailQuotient P hStart k := by
  unfold terminalCarryTailQuotientNat
  rw [Int.toNat_of_nonneg
    (terminalCarryTailQuotient_nonneg P hStart hsk hkc)]

namespace AttachedTwoCornerPacket

/-- attached straight suffix の開始 cut。 -/
def straightHenselStart
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P) : ℕ :=
  A.normalForm.previous + 1

/-- previous corner の直後から terminal critical start までの幅。 -/
def straightHenselWidth
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P) : ℕ :=
  P.terminalCriticalStart - A.straightHenselStart

/-- straight suffix start は right endpoint より strict に左。 -/
theorem straightHenselStart_lt_terminalCriticalStart
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P) :
    A.straightHenselStart < P.terminalCriticalStart := by
  unfold straightHenselStart
  exact A.previous_succ_lt_terminalCriticalStart

/-- attached straight suffix の幅は positive。 -/
theorem straightHenselWidth_pos
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P) :
    0 < A.straightHenselWidth := by
  unfold straightHenselWidth
  have hLt := A.straightHenselStart_lt_terminalCriticalStart
  omega

/-- start + width は exact に terminal critical start。 -/
theorem straightHenselStart_add_width
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P) :
    A.straightHenselStart + A.straightHenselWidth =
      P.terminalCriticalStart := by
  unfold straightHenselWidth
  have hLe : A.straightHenselStart ≤ P.terminalCriticalStart :=
    Nat.le_of_lt A.straightHenselStart_lt_terminalCriticalStart
  exact Nat.add_sub_of_le hLe

/--
previous より右の attached suffix では terminal step を含めて係数 `2` の recurrence に直せる。
最後の step では next quotient が `0` なので terminal carry gap の大きさは消える。
-/
theorem straight_tailQuotient_recurrence
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    (hStart : 0 < P.criticalizationStart)
    {k : ℕ}
    (hPrev : A.normalForm.previous < k)
    (hkc : k < P.terminalCriticalStart) :
    3 * terminalCarryTailQuotient P hStart k =
      2 * terminalCarryTailQuotient P hStart (k + 1) +
        (2 : ℤ) ^ P.h k - 1 := by
  have hsk : P.criticalizationStart ≤ k := by
    exact le_trans A.criticalization_le_previous (Nat.le_of_lt hPrev)
  have hRec :=
    terminalCarryTailQuotient_recurrence P hStart hsk hkc
  by_cases hLast : k + 1 = P.terminalCriticalStart
  · have hQNext := terminalCarryTailQuotient_terminal P hStart
    rw [hLast, hQNext] at hRec ⊢
    simp only [mul_zero, zero_add] at hRec ⊢
    exact hRec
  · have hSuccLt : k + 1 < P.terminalCriticalStart := by omega
    have hTerm : k < A.normalForm.terminal := by
      rw [A.terminal_eq]
      omega
    have hGap := A.internal_carryRunGap_eq_one hPrev hTerm
    rw [hGap] at hRec
    norm_num at hRec
    exact hRec

/-- previous exposed corner の arbitrary state interface を actual quotient から構成する。 -/
noncomputable def toAttachedCornerHenselState
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    (hStart : 0 < P.criticalizationStart) :
    AttachedCornerHenselState P A := by
  let a := A.normalForm.previous
  let x := terminalCarryTailQuotientNat P hStart a
  let xNext := terminalCarryTailQuotientNat P hStart (a + 1)
  refine
    { x := x
      xNext := xNext
      step := ?_ }
  have haC : a < P.terminalCriticalStart :=
    A.previous_mem_arithmeticCorridor.2
  have haSk : P.criticalizationStart ≤ a :=
    A.criticalization_le_previous
  have ha1Sk : P.criticalizationStart ≤ a + 1 := by omega
  have ha1C : a + 1 ≤ P.terminalCriticalStart := by omega
  have hRec :=
    terminalCarryTailQuotient_recurrence P hStart haSk haC
  have hCast0 :=
    terminalCarryTailQuotientNat_cast P hStart haSk (Nat.le_of_lt haC)
  have hCast1 :=
    terminalCarryTailQuotientNat_cast P hStart ha1Sk ha1C
  have hStepZ :
      3 * terminalCarryTailQuotient P hStart a + 1 =
        (2 : ℤ) ^ carryRunGap P P.terminalCriticalStart a *
            terminalCarryTailQuotient P hStart (a + 1) +
          (2 : ℤ) ^ P.h a := by
    linarith [hRec]
  change
    NormalizedHenselStep
      (P.h a)
      (carryRunGap P P.terminalCriticalStart a)
      x xNext
  unfold NormalizedHenselStep
  dsimp [x, xNext]
  rw [← hCast0, ← hCast1] at hStepZ
  exact_mod_cast hStepZ

/--
attached actual object から free-base pure Hensel chain を構成する。
この定義が attached geometry と後段 pure repeat arithmetic の正式な bridge。
-/
noncomputable def toFreeBaseMonotoneHenselChain
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    (hStart : 0 < P.criticalizationStart) :
    FreeBaseMonotoneHenselChain where
  width := A.straightHenselWidth
  width_pos := A.straightHenselWidth_pos
  delta := fun i => P.h (A.straightHenselStart + i)
  q := fun i =>
    terminalCarryTailQuotient
      P hStart (A.straightHenselStart + i)
  delta_pos := by
    intro i hi
    have hEnd := A.straightHenselStart_add_width
    have hkC : A.straightHenselStart + i < P.terminalCriticalStart := by
      omega
    have hkTerminal :
        A.straightHenselStart + i ≤ A.normalForm.terminal := by
      rw [A.terminal_eq]
      omega
    exact
      A.samePositiveCorridor
        (A.straightHenselStart + i)
        (by
          unfold straightHenselStart
          omega)
        hkTerminal
  delta_step := by
    intro i hi
    have hEnd := A.straightHenselStart_add_width
    let k := A.straightHenselStart + i
    have hPrev : A.normalForm.previous < k := by
      dsimp [k]
      unfold straightHenselStart
      omega
    have hkC : k + 1 < P.terminalCriticalStart := by
      dsimp [k]
      omega
    have hStep := A.internal_depth_succ_eq_self_or_add_one hPrev hkC
    dsimp [k] at hStep
    simpa [Nat.add_assoc] using hStep
  q_terminal := by
    have hEnd := A.straightHenselStart_add_width
    rw [hEnd]
    exact terminalCarryTailQuotient_terminal P hStart
  recurrence := by
    intro i hi
    have hEnd := A.straightHenselStart_add_width
    let k := A.straightHenselStart + i
    have hPrev : A.normalForm.previous < k := by
      dsimp [k]
      unfold straightHenselStart
      omega
    have hkC : k < P.terminalCriticalStart := by
      dsimp [k]
      omega
    have hRec := A.straight_tailQuotient_recurrence hStart hPrev hkC
    dsimp [k] at hRec
    simpa [Nat.add_assoc] using hRec

end AttachedTwoCornerPacket

end MultiCorner
end CSTMicro
end Collatz2
