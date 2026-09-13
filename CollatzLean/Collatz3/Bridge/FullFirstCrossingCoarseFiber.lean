import CollatzLean.Collatz3.Bridge.FullFirstCrossingActual
import CollatzLean.Collatz3.Arithmetic.ModTwoPow
import Mathlib.Tactic.Ring

/-!
# Collatz3 Bridge: 全 terminal overshoot をまとめる coarse actual fiber

fixed partition `P` に対して overshoot `s` ごとの odd-endpoint modulus は
`2^(H+s+1)` で変化する。しかし `s` をすべてまとめると、start 全体は

`2^H`,  H = criticalTwoDepth m

を法とする一本の合同類になる。

この coarse classification により、無限個の overshoot 層を解析的に足さずに
full first-crossing の exact block counting ができる。
-/

namespace Collatz3
namespace Bridge

/-- full first-crossing start を分類する coarse modulus `2^H`。 -/
def fullCrossingStartModulus (m : ℕ) : ℕ :=
  Arithmetic.twoPowModulus (Critical.criticalTwoDepth m)

@[simp] theorem fullCrossingStartModulus_eq (m : ℕ) :
    fullCrossingStartModulus m = 2 ^ Critical.criticalTwoDepth m := by
  rfl

@[simp] theorem fullCrossingStartModulus_pos (m : ℕ) :
    0 < fullCrossingStartModulus m := by
  unfold fullCrossingStartModulus
  exact Arithmetic.twoPowModulus_pos _

/-- 従来の odd-endpoint modulus は full coarse modulus のちょうど2倍。 -/
theorem criticalStartModulus_eq_two_mul_fullCrossingStartModulus
    (m : ℕ) :
    criticalStartModulus m = 2 * fullCrossingStartModulus m := by
  unfold criticalStartModulus fullCrossingStartModulus Arithmetic.twoPowModulus
  rw [pow_succ]
  ring

/-- nonempty word の affine translation は正。 -/
theorem affineConst_pos_of_nonempty
    {w : Word}
    (hne : w ≠ []) :
    0 < Word.affineConst w := by
  cases w with
  | nil => contradiction
  | cons e tail =>
      rw [Word.affineConst_cons]
      have hThree := Arithmetic.threePow_pos (Word.oddSteps tail)
      omega

/-- 正自然数は `2^s * odd` に分解できる。 -/
theorem exists_twoPow_mul_odd
    (z : ℕ)
    (hz : 0 < z) :
    ∃ s y : ℕ, z = 2 ^ s * y ∧ Odd y := by
  induction z using Nat.strong_induction_on with
  | h z ih =>
      obtain ⟨q, hEven | hOdd⟩ := z.even_or_odd'
      · have hqPos : 0 < q := by omega
        have hqLt : q < z := by
          rw [hEven]
          omega
        rcases ih q hqLt hqPos with ⟨s, y, hqy, hy⟩
        refine ⟨s + 1, y, ?_, hy⟩
        rw [hEven, hqy, pow_succ]
        ring
      · exact ⟨0, z, by simp, ⟨q, hOdd⟩⟩

/--
partition `P` の coarse start class。
minimal critical affine data `(m,H,B)` に対して

`3^m x + B = 0 (mod 2^H)`

を解く。
-/
def fullCrossingStartClass
    {m : ℕ}
    (hm : 0 < m)
    (P : RestrictedCriticalPartition m) :
    ZMod (fullCrossingStartModulus m) := by
  let W := criticalWordOfPartition m hm P
  exact
    Arithmetic.solveThreePow
      m
      (Critical.criticalTwoDepth m)
      (-((Word.affineConst W.1 : ℕ) :
        ZMod (fullCrossingStartModulus m)))

/-- coarse class は defining congruence を満たす。 -/
theorem fullCrossingStartClass_spec
    {m : ℕ}
    (hm : 0 < m)
    (P : RestrictedCriticalPartition m) :
    (((3 ^ m : ℕ) : ZMod (fullCrossingStartModulus m)) *
        fullCrossingStartClass hm P) +
      ((Word.affineConst (criticalWordOfPartition m hm P).1 : ℕ) :
        ZMod (fullCrossingStartModulus m)) = 0 := by
  unfold fullCrossingStartClass
  change
    (((3 ^ m : ℕ) :
        ZMod (Arithmetic.twoPowModulus (Critical.criticalTwoDepth m))) *
      Arithmetic.solveThreePow
        m
        (Critical.criticalTwoDepth m)
        (-((Word.affineConst (criticalWordOfPartition m hm P).1 : ℕ) :
          ZMod (Arithmetic.twoPowModulus (Critical.criticalTwoDepth m))))) +
      ((Word.affineConst (criticalWordOfPartition m hm P).1 : ℕ) :
        ZMod (Arithmetic.twoPowModulus (Critical.criticalTwoDepth m))) = 0
  rw [Arithmetic.threePow_mul_solveThreePow]
  exact neg_add_cancel _

/-- coarse class の最小非負代表。 -/
def fullCrossingStartResidue
    {m : ℕ}
    (hm : 0 < m)
    (P : RestrictedCriticalPartition m) : ℕ :=
  (fullCrossingStartClass hm P).val

/-- coarse residue は modulus 未満。 -/
theorem fullCrossingStartResidue_lt
    {m : ℕ}
    (hm : 0 < m)
    (P : RestrictedCriticalPartition m) :
    fullCrossingStartResidue hm P < fullCrossingStartModulus m := by
  let : NeZero (fullCrossingStartModulus m) :=
    ⟨Nat.ne_of_gt (fullCrossingStartModulus_pos m)⟩
  exact ZMod.val_lt (fullCrossingStartClass hm P)

/-- residue を ZMod に戻すと coarse class。 -/
theorem fullCrossingStartResidue_cast
    {m : ℕ}
    (hm : 0 < m)
    (P : RestrictedCriticalPartition m) :
    ((fullCrossingStartResidue hm P : ℕ) :
      ZMod (fullCrossingStartModulus m)) =
      fullCrossingStartClass hm P := by
  let : NeZero (fullCrossingStartModulus m) :=
    ⟨Nat.ne_of_gt (fullCrossingStartModulus_pos m)⟩
  exact ZMod.natCast_zmod_val (fullCrossingStartClass hm P)

/--
`fullWordOfPartitionExtra` の subtype coercion を外した形で、
full word の odd-step 数が幅 `m` に一致することを読む補助補題。

既存の `oddSteps_fullWordFromPartitionExtra` は raw word
`fullWordFromPartitionExtra` に対する補題なので、後続の `rw` では
この橋を使う。
-/
@[simp] theorem oddSteps_fullWordOfPartitionExtra_value
    {m : ℕ}
    (hm : 0 < m)
    (P : RestrictedCriticalPartition m)
    (s : ℕ) :
    Word.oddSteps (fullWordOfPartitionExtra hm P s).1 = m := by
  change Word.oddSteps (fullWordFromPartitionExtra P s) = m
  exact oddSteps_fullWordFromPartitionExtra (m := m) P s

/--
`fullWordOfPartitionExtra` の subtype coercion を外した形で、
full word の two-step 深さを読む補助補題。

raw word 側の既存補題を `change` で受けることで、coercion のために
直接の `rw` が失敗することを避ける。
-/
@[simp] theorem twoSteps_fullWordOfPartitionExtra_value
    {m : ℕ}
    (hm : 0 < m)
    (P : RestrictedCriticalPartition m)
    (s : ℕ) :
    Word.twoSteps (fullWordOfPartitionExtra hm P s).1 =
      Critical.criticalTwoDepth m + s := by
  change Word.twoSteps (fullWordFromPartitionExtra P s) =
    Critical.criticalTwoDepth m + s
  simpa only [Critical.criticalTwoDepth_eq] using
    (twoSteps_fullWordFromPartitionExtra hm P s)

/--
generated full word の actual run start は coarse class に属する。
-/
theorem run_start_cast_eq_fullCrossingStartClass
    {m : ℕ}
    (hm : 0 < m)
    (P : RestrictedCriticalPartition m)
    (s : ℕ)
    {x y : ℕ}
    (hRun : Runs (fullWordOfPartitionExtra hm P s).1 x y) :
    ((x : ℕ) : ZMod (fullCrossingStartModulus m)) =
      fullCrossingStartClass hm P := by
  let W := fullWordOfPartitionExtra hm P s
  let B := Word.affineConst (criticalWordOfPartition m hm P).1
  have hMain0 := (Word.endpointEquation_iff W.1 x y).1 hRun.endpointEquation
  have hMain :
      2 ^ (Critical.criticalTwoDepth m + s) * y =
        3 ^ m * x + B := by
    dsimp [W] at hMain0
    rw [twoSteps_fullWordOfPartitionExtra_value hm P s,
        oddSteps_fullWordOfPartitionExtra_value hm P s] at hMain0
    simpa [B,
      affineConst_fullWordOfPartitionExtra_eq_critical hm P s]
      using hMain0
  let : NeZero (fullCrossingStartModulus m) :=
    ⟨Nat.ne_of_gt (fullCrossingStartModulus_pos m)⟩
  have hCast := congrArg
    (fun n : ℕ => (n : ZMod (fullCrossingStartModulus m))) hMain
  have hZero :
      (((3 ^ m : ℕ) : ZMod (fullCrossingStartModulus m)) *
          ((x : ℕ) : ZMod (fullCrossingStartModulus m))) +
        ((B : ℕ) : ZMod (fullCrossingStartModulus m)) = 0 := by
    have hPow :
        2 ^ (Critical.criticalTwoDepth m + s) =
          fullCrossingStartModulus m * 2 ^ s := by
      unfold fullCrossingStartModulus Arithmetic.twoPowModulus
      rw [pow_add]
    rw [hPow] at hCast
    have hLeftZero :
        (((fullCrossingStartModulus m * 2 ^ s * y : ℕ)) :
          ZMod (fullCrossingStartModulus m)) = 0 := by
      rw [Nat.cast_mul, Nat.cast_mul,
          ZMod.natCast_self]
      simp
    have hRightZero :
        (((3 ^ m * x + B : ℕ)) :
          ZMod (fullCrossingStartModulus m)) = 0 := by
      exact hCast.symm.trans hLeftZero
    simpa only [Nat.cast_add, Nat.cast_mul] using hRightZero
  have hxEq :
      (((3 ^ m : ℕ) : ZMod (fullCrossingStartModulus m)) *
        ((x : ℕ) : ZMod (fullCrossingStartModulus m))) =
      -((B : ℕ) : ZMod (fullCrossingStartModulus m)) := by
    exact (eq_neg_iff_add_eq_zero).2 hZero
  unfold fullCrossingStartClass
  change
    ((x : ℕ) :
        ZMod (Arithmetic.twoPowModulus (Critical.criticalTwoDepth m))) =
      Arithmetic.solveThreePow
        m
        (Critical.criticalTwoDepth m)
        (-((B : ℕ) :
          ZMod (Arithmetic.twoPowModulus (Critical.criticalTwoDepth m))))
  exact
    Arithmetic.solveThreePow_unique
      m
      (Critical.criticalTwoDepth m)
      (-((B : ℕ) :
        ZMod (Arithmetic.twoPowModulus (Critical.criticalTwoDepth m))))
      ((x : ℕ) :
        ZMod (Arithmetic.twoPowModulus (Critical.criticalTwoDepth m)))
      hxEq

/-- generated full run の start residue は exact に coarse representative。 -/
theorem run_start_mod_eq_fullCrossingStartResidue
    {m : ℕ}
    (hm : 0 < m)
    (P : RestrictedCriticalPartition m)
    (s : ℕ)
    {x y : ℕ}
    (hRun : Runs (fullWordOfPartitionExtra hm P s).1 x y) :
    x % fullCrossingStartModulus m = fullCrossingStartResidue hm P := by
  let : NeZero (fullCrossingStartModulus m) :=
    ⟨Nat.ne_of_gt (fullCrossingStartModulus_pos m)⟩
  have hCast := run_start_cast_eq_fullCrossingStartClass hm P s hRun
  have hVal := congrArg ZMod.val hCast
  simpa [fullCrossingStartResidue, ZMod.val_natCast] using hVal

/--
coarse residue の任意の lift は、ある overshoot `s` を選ぶことで actual full run になる。
-/
theorem exists_fullRun_of_coarseLift
    {m : ℕ}
    (hm : 0 < m)
    (P : RestrictedCriticalPartition m)
    (q : ℕ) :
    ∃ s y : ℕ,
      Runs (fullWordOfPartitionExtra hm P s).1
        (fullCrossingStartResidue hm P + fullCrossingStartModulus m * q)
        y := by
  let R := fullCrossingStartResidue hm P
  let M := fullCrossingStartModulus m
  let W0 := criticalWordOfPartition m hm P
  let B := Word.affineConst W0.1
  have hBPos : 0 < B := by
    exact affineConst_pos_of_nonempty (criticalWord_nonempty hm W0)
  let : NeZero M := ⟨Nat.ne_of_gt (by simp only [fullCrossingStartModulus_eq,
                     Critical.criticalTwoDepth_eq, Order.lt_two_iff, zero_le, pow_succ_pos, M])⟩
  have hCastZero :
      (((3 ^ m * R + B : ℕ) : ZMod M)) = 0 := by
    calc
      ((3 ^ m * R + B : ℕ) : ZMod M)
          = (((3 ^ m : ℕ) : ZMod M) * ((R : ℕ) : ZMod M)) +
              ((B : ℕ) : ZMod M) := by push_cast; rfl
      _ = (((3 ^ m : ℕ) : ZMod M) * fullCrossingStartClass hm P) +
              ((B : ℕ) : ZMod M) := by
            rw [fullCrossingStartResidue_cast hm P]
      _ = 0 := by
            simpa [M, B, W0] using fullCrossingStartClass_spec hm P
  have hModZero : (3 ^ m * R + B) % M = 0 := by
    have hVal := congrArg ZMod.val hCastZero
    rw [ZMod.val_natCast] at hVal
    simpa using hVal
  have hDivR : M ∣ 3 ^ m * R + B := by
    refine ⟨(3 ^ m * R + B) / M, ?_⟩
    have hDecomp := Nat.mod_add_div (3 ^ m * R + B) M
    rw [hModZero, Nat.zero_add] at hDecomp
    exact hDecomp.symm
  rcases hDivR with ⟨z0, hz0⟩
  have hz0Pos : 0 < z0 := by
    by_contra hz
    have hz0Zero : z0 = 0 := by omega
    rw [hz0Zero, Nat.mul_zero] at hz0
    have : 0 < 3 ^ m * R + B := Nat.add_pos_right _ hBPos
    omega
  let z := z0 + 3 ^ m * q
  have hzPos : 0 < z := by
    dsimp [z]
    omega
  rcases exists_twoPow_mul_odd z hzPos with ⟨s, y, hzy, hy⟩
  refine ⟨s, y, ?_⟩
  apply Runs.of_valid_endpointEquation_odd
    (valid_fullWordFromPartitionExtra P s)
    ?_
    hy
  apply (Word.endpointEquation_iff
    (fullWordOfPartitionExtra hm P s).1
    (R + M * q) y).2
  have hMX :
      M * z = 3 ^ m * (R + M * q) + B := by
    dsimp [z]
    calc
      M * (z0 + 3 ^ m * q)
          = M * z0 + M * (3 ^ m * q) := by ring
      _ = (3 ^ m * R + B) + M * (3 ^ m * q) := by
            rw [← hz0]
      _ = 3 ^ m * (R + M * q) + B := by ring
  calc
    2 ^ Word.twoSteps (fullWordOfPartitionExtra hm P s).1 * y
        = 2 ^ (Critical.criticalTwoDepth m + s) * y := by
            rw [twoSteps_fullWordOfPartitionExtra_value hm P s]
    _ = M * (2 ^ s * y) := by
            dsimp [M]
            rw [fullCrossingStartModulus_eq,
                Critical.criticalTwoDepth_eq,
                pow_add]
            ring
    _ = M * z := by rw [← hzy]
    _ = 3 ^ m * (R + M * q) + B := hMX
    _ =
        3 ^ Word.oddSteps (fullWordOfPartitionExtra hm P s).1 *
            (R + M * q) +
          Word.affineConst (fullWordOfPartitionExtra hm P s).1 := by
            rw [oddSteps_fullWordOfPartitionExtra_value hm P s]
            rw [affineConst_fullWordOfPartitionExtra_eq_critical hm P s]

/-- 幅 `m` の full actual first-crossing start。 -/
def IsFullActualCriticalStart
    (m x : ℕ) : Prop :=
  ∃ W : Critical.FullFirstCrossingWord m,
    ∃ y : ℕ,
      Runs W.1 x y

/--
full actual starts は partition ごとの coarse arithmetic progression と exact に一致する。
-/
theorem isFullActualCriticalStart_iff_exists_partition_coarseLift
    {m x : ℕ}
    (hm : 0 < m) :
    IsFullActualCriticalStart m x ↔
      ∃ P : RestrictedCriticalPartition m,
        ∃ q : ℕ,
          x = fullCrossingStartResidue hm P +
            fullCrossingStartModulus m * q := by
  constructor
  · rintro ⟨W, y, hRun⟩
    let code := fullFirstCrossingWordEquivPartitionExtra m hm W
    let P : RestrictedCriticalPartition m := code.1
    let s : ℕ := code.2
    have hWord : fullWordOfPartitionExtra hm P s = W := by
      dsimp [P, s, code]
      exact (fullFirstCrossingWordEquivPartitionExtra m hm).symm_apply_apply W
    have hRun' : Runs (fullWordOfPartitionExtra hm P s).1 x y := by
      rw [hWord]
      exact hRun
    have hMod := run_start_mod_eq_fullCrossingStartResidue hm P s hRun'
    refine ⟨P, x / fullCrossingStartModulus m, ?_⟩
    have hDecomp := Nat.mod_add_div x (fullCrossingStartModulus m)
    rw [hMod] at hDecomp
    exact hDecomp.symm
  · rintro ⟨P, q, hx⟩
    rcases exists_fullRun_of_coarseLift hm P q with ⟨s, y, hRun⟩
    refine ⟨fullWordOfPartitionExtra hm P s, y, ?_⟩
    rw [hx]
    exact hRun

/-- 異なる partitions は異なる coarse residues を持つ。 -/
theorem fullCrossingStartResidue_injective
    {m : ℕ}
    (hm : 0 < m) :
    Function.Injective
      (fullCrossingStartResidue (m := m) hm) := by
  intro P Q hResidue
  rcases exists_fullRun_of_coarseLift hm P 0 with ⟨s, y, hP⟩
  rcases exists_fullRun_of_coarseLift hm Q 0 with ⟨t, z, hQ⟩
  have hQ' :
      Runs (fullWordOfPartitionExtra hm Q t).1
        (fullCrossingStartResidue hm P) z := by
    simpa [hResidue] using hQ
  have hP' :
      Runs (fullWordOfPartitionExtra hm P s).1
        (fullCrossingStartResidue hm P) y := by
    simpa using hP
  have hSteps :
      Word.oddSteps (fullWordOfPartitionExtra hm P s).1 =
        Word.oddSteps (fullWordOfPartitionExtra hm Q t).1 := by
    rw [oddSteps_fullWordOfPartitionExtra_value hm P s,
        oddSteps_fullWordOfPartitionExtra_value hm Q t]
  have hWords :=
    Runs.word_end_eq_of_common_start_same_oddSteps hP' hQ' hSteps
  have hSubtype :
      fullWordOfPartitionExtra hm P s =
        fullWordOfPartitionExtra hm Q t := by
    apply Subtype.ext
    exact hWords.1
  have hCode := congrArg
    (fun W : Critical.FullFirstCrossingWord m =>
      fullFirstCrossingWordEquivPartitionExtra m hm W) hSubtype
  have hPCode :
      fullFirstCrossingWordEquivPartitionExtra m hm
          (fullWordOfPartitionExtra hm P s) = (P, s) := by
    change
      fullFirstCrossingWordEquivPartitionExtra m hm
          ((fullFirstCrossingWordEquivPartitionExtra m hm).symm (P, s)) =
        (P, s)
    exact (fullFirstCrossingWordEquivPartitionExtra m hm).apply_symm_apply (P, s)
  have hQCode :
      fullFirstCrossingWordEquivPartitionExtra m hm
          (fullWordOfPartitionExtra hm Q t) = (Q, t) := by
    change
      fullFirstCrossingWordEquivPartitionExtra m hm
          ((fullFirstCrossingWordEquivPartitionExtra m hm).symm (Q, t)) =
        (Q, t)
    exact (fullFirstCrossingWordEquivPartitionExtra m hm).apply_symm_apply (Q, t)
  rw [hPCode, hQCode] at hCode
  exact congrArg Prod.fst hCode

/--
coarse progression 上で start が一致すれば base partition も一致する。
-/
theorem coarseStart_eq_implies_partition_eq
    {m : ℕ}
    (hm : 0 < m)
    {P Q : RestrictedCriticalPartition m}
    {k l : ℕ}
    (hStart :
      fullCrossingStartResidue hm P + fullCrossingStartModulus m * k =
        fullCrossingStartResidue hm Q + fullCrossingStartModulus m * l) :
    P = Q := by
  rcases exists_fullRun_of_coarseLift hm P k with ⟨s, y, hP⟩
  rcases exists_fullRun_of_coarseLift hm Q l with ⟨t, z, hQ⟩
  have hQ' :
      Runs (fullWordOfPartitionExtra hm Q t).1
        (fullCrossingStartResidue hm P + fullCrossingStartModulus m * k) z := by
    rw [hStart]
    exact hQ
  have hSteps :
      Word.oddSteps (fullWordOfPartitionExtra hm P s).1 =
        Word.oddSteps (fullWordOfPartitionExtra hm Q t).1 := by
    rw [oddSteps_fullWordOfPartitionExtra_value hm P s,
        oddSteps_fullWordOfPartitionExtra_value hm Q t]
  have hWords :=
    Runs.word_end_eq_of_common_start_same_oddSteps hP hQ' hSteps
  have hSubtype :
      fullWordOfPartitionExtra hm P s =
        fullWordOfPartitionExtra hm Q t := by
    apply Subtype.ext
    exact hWords.1
  have hCode := congrArg
    (fun W : Critical.FullFirstCrossingWord m =>
      fullFirstCrossingWordEquivPartitionExtra m hm W) hSubtype
  have hPCode :
      fullFirstCrossingWordEquivPartitionExtra m hm
          (fullWordOfPartitionExtra hm P s) = (P, s) := by
    change
      fullFirstCrossingWordEquivPartitionExtra m hm
          ((fullFirstCrossingWordEquivPartitionExtra m hm).symm (P, s)) =
        (P, s)
    exact (fullFirstCrossingWordEquivPartitionExtra m hm).apply_symm_apply (P, s)
  have hQCode :
      fullFirstCrossingWordEquivPartitionExtra m hm
          (fullWordOfPartitionExtra hm Q t) = (Q, t) := by
    change
      fullFirstCrossingWordEquivPartitionExtra m hm
          ((fullFirstCrossingWordEquivPartitionExtra m hm).symm (Q, t)) =
        (Q, t)
    exact (fullFirstCrossingWordEquivPartitionExtra m hm).apply_symm_apply (Q, t)
  rw [hPCode, hQCode] at hCode
  exact congrArg Prod.fst hCode

/-- `B` 未満の full actual critical starts。 -/
abbrev FullActualCriticalStartBelow (m B : ℕ) :=
  {x : ℕ // x < B ∧ IsFullActualCriticalStart m x}

/-- bounded full-start type は有限。 -/
theorem fullActualCriticalStartBelow_finite
    (m B : ℕ) :
    Finite (FullActualCriticalStartBelow m B) := by
  exact
    Finite.of_injective
      (fun x : FullActualCriticalStartBelow m B =>
        (⟨x.1, x.2.1⟩ : Fin B))
      (by
        intro a b h
        apply Subtype.ext
        exact congrArg Fin.val h)

/-- bounded full-start count。 -/
noncomputable def fullActualCriticalStartCount
    (m B : ℕ) : ℕ :=
  Nat.card (FullActualCriticalStartBelow m B)

/-- partition × `Fin q` から最初の `q` coarse blocks の start を作る。 -/
def fullBlockCodeToStart
    {m : ℕ}
    (hm : 0 < m)
    (q : ℕ) :
    (RestrictedCriticalPartition m × Fin q) →
      FullActualCriticalStartBelow m (fullCrossingStartModulus m * q) :=
  fun code => by
    let P := code.1
    let k := code.2
    refine ⟨fullCrossingStartResidue hm P +
      fullCrossingStartModulus m * k.1, ?_, ?_⟩
    · have hR := fullCrossingStartResidue_lt hm P
      have hkSucc : k.1 + 1 ≤ q := Nat.succ_le_iff.mpr k.2
      calc
        fullCrossingStartResidue hm P + fullCrossingStartModulus m * k.1
            < fullCrossingStartModulus m + fullCrossingStartModulus m * k.1 :=
          Nat.add_lt_add_right hR _
        _ = fullCrossingStartModulus m * (k.1 + 1) := by ring
        _ ≤ fullCrossingStartModulus m * q :=
          Nat.mul_le_mul_left _ hkSucc
    · exact
        (isFullActualCriticalStart_iff_exists_partition_coarseLift hm).2
          ⟨P, k.1, rfl⟩

/-- full block encoding は単射。 -/
theorem fullBlockCodeToStart_injective
    {m : ℕ}
    (hm : 0 < m)
    (q : ℕ) :
    Function.Injective (fullBlockCodeToStart hm q) := by
  intro a b h
  rcases a with ⟨P, k⟩
  rcases b with ⟨Q, l⟩
  have hStart :
      fullCrossingStartResidue hm P + fullCrossingStartModulus m * k.1 =
        fullCrossingStartResidue hm Q + fullCrossingStartModulus m * l.1 :=
    congrArg Subtype.val h
  have hPQ : P = Q := coarseStart_eq_implies_partition_eq hm hStart
  subst Q
  apply Prod.ext
  · rfl
  · apply Fin.ext
    have hMul :
        fullCrossingStartModulus m * k.1 =
          fullCrossingStartModulus m * l.1 :=
      Nat.add_left_cancel hStart
    exact Nat.mul_left_cancel (fullCrossingStartModulus_pos m) hMul

/-- full block encoding は全射。 -/
theorem fullBlockCodeToStart_surjective
    {m : ℕ}
    (hm : 0 < m)
    (q : ℕ) :
    Function.Surjective (fullBlockCodeToStart hm q) := by
  intro x
  rcases
      (isFullActualCriticalStart_iff_exists_partition_coarseLift hm).1 x.2.2
      with ⟨P, k, hx⟩
  have hk : k < q := by
    by_contra hNot
    have hqk : q ≤ k := Nat.le_of_not_gt hNot
    have hMul :
        fullCrossingStartModulus m * q ≤
          fullCrossingStartModulus m * k :=
      Nat.mul_le_mul_left _ hqk
    have hTail :
        fullCrossingStartModulus m * k ≤
          fullCrossingStartResidue hm P + fullCrossingStartModulus m * k := by
      omega
    have hBound : fullCrossingStartModulus m * q ≤ x.1 := by
      rw [hx]
      exact le_trans hMul hTail
    omega
  refine ⟨(P, ⟨k, hk⟩), ?_⟩
  apply Subtype.ext
  exact hx.symm

/-- 最初の `q` coarse blocks と `partition × Fin q` の exact equivalence。 -/
noncomputable def fullBlockCodeEquivStartBelow
    {m : ℕ}
    (hm : 0 < m)
    (q : ℕ) :
    (RestrictedCriticalPartition m × Fin q) ≃
      FullActualCriticalStartBelow m (fullCrossingStartModulus m * q) :=
  Equiv.ofBijective
    (fullBlockCodeToStart hm q)
    ⟨fullBlockCodeToStart_injective hm q,
      fullBlockCodeToStart_surjective hm q⟩

/-- full `q` blocksでは count は exact に `N_m * q`。 -/
theorem fullActualCriticalStartCount_block_eq
    {m : ℕ}
    (hm : 0 < m)
    (q : ℕ) :
    fullActualCriticalStartCount m (fullCrossingStartModulus m * q) =
      criticalPartitionCount m * q := by
  unfold fullActualCriticalStartCount
  calc
    Nat.card (FullActualCriticalStartBelow m (fullCrossingStartModulus m * q))
        = Nat.card (RestrictedCriticalPartition m × Fin q) :=
      (Nat.card_congr (fullBlockCodeEquivStartBelow hm q)).symm
    _ = Nat.card (RestrictedCriticalPartition m) * Nat.card (Fin q) :=
      Nat.card_prod _ _
    _ = criticalPartitionCount m * q := by
      simp [criticalPartitionCount]

end Bridge
end Collatz3
