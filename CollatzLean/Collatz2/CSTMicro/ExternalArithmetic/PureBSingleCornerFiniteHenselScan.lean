import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBSingleCornerEntranceXiFinite

set_option linter.style.nativeDecide false
set_option linter.style.emptyLine false
set_option exponentiation.threshold 4096

/-!
# Pure B single-corner: bounded Hensel suffix scanner

`card = 1` の actual branch では既に

* `m <= 2270`,
* `b < 116`,
* `width = c-b <= 213`

まで落ちている。

このファイルでは `(m,b,c)` を毎回 closed form から再計算しない。
固定 `(b,c)` について corner 終端 `c` の affine numerator を一度だけ作り、
その後の critical suffix を

  3^m R + A = 2^(beta_m+1) q

という exact Hensel state で前向きに更新する。

`beta_(m+1)-beta_m` は 1 または 2 なので、次の representative lift に必要な
新しい bit は高々 3 bit。従って各 suffix step では mod 4 / mod 8 の
`3^(-m-1)` だけで一意に lift できる。

safety は rank 130 まで

  q < R

だけを直接検査する。rank 130 以降では `beta >= 206` なので Hensel lift は
representative の下位 205 bit を変えない。そこで長い suffix scan を打ち切り、

  R mod 2^205 > rhinGapK * 2271^15

という frozen residue certificate に切り替える。actual card-one representative は
既存 Rhin bound で右辺以下なので、後続 bridge ではこの residue certificate が
そのまま contradiction になる。

これにより native 側の Hensel update 数は、全 suffix を 2270 まで走らせる
約 3000 万 step から、rank 130 までの約 20 万 step へ落ちる。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-! ## 1. executable critical state -/

/--
proof-oriented `beattyIndex` / `criticalPrefixPhiNat` を native loop から分離する
scalar critical state。
-/
structure SingleCornerCriticalState where
  m : ℕ
  beta : ℕ
  psi : ℕ
  three : ℕ
deriving Inhabited

/-- 初期 critical state。 -/
def singleCornerCriticalInitial : SingleCornerCriticalState := {
  m := 0
  beta := 0
  psi := 0
  three := 1
}

/-- Beatty increment の executable branch。 -/
def SingleCornerCriticalState.nextBeta
    (S : SingleCornerCriticalState) : ℕ :=
  if S.three * 3 ≤ 2 ^ (S.beta + 2) then
    S.beta + 1
  else
    S.beta + 2

/-- critical state を一 odd rank 進める。 -/
def SingleCornerCriticalState.next
    (S : SingleCornerCriticalState) : SingleCornerCriticalState := {
  m := S.m + 1
  beta := S.nextBeta
  psi := 3 * S.psi + 2 ^ S.beta
  three := 3 * S.three
}

/-- rank `n` の executable state。 -/
def singleCornerCriticalStateAt : ℕ → SingleCornerCriticalState
  | 0 => singleCornerCriticalInitial
  | n + 1 => (singleCornerCriticalStateAt n).next

@[simp] theorem singleCornerCriticalStateAt_m
    (n : ℕ) :
    (singleCornerCriticalStateAt n).m = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [singleCornerCriticalStateAt, SingleCornerCriticalState.next, ih]

/-- `criticalPrefixPhiNat` の one-step recurrence。 -/
theorem criticalPrefixPhiNat_succ_hensel
    (n : ℕ) :
    criticalPrefixPhiNat (n + 1) =
      3 * criticalPrefixPhiNat n + 2 ^ beattyIndex n := by
  classical
  unfold criticalPrefixPhiNat
  rw [Finset.sum_range_succ]
  have hPrefix :
      Finset.sum (Finset.range n)
          (fun k =>
            2 ^ beattyIndex k * 3 ^ (n + 1 - (k + 1))) =
        3 *
          Finset.sum (Finset.range n)
            (fun k =>
              2 ^ beattyIndex k * 3 ^ (n - (k + 1))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hkLt : k < n := Finset.mem_range.mp hk
    have hExp :
        n + 1 - (k + 1) = (n - (k + 1)) + 1 := by
      omega
    rw [hExp, pow_succ]
    ring
  rw [hPrefix]
  have hLast : n + 1 - (n + 1) = 0 := by omega
  rw [hLast, pow_zero, mul_one]

/-- executable critical state の semantic invariant。 -/
def SingleCornerCriticalState.Correct
    (S : SingleCornerCriticalState) : Prop :=
  S.beta = beattyIndex S.m ∧
  S.psi = criticalPrefixPhiNat S.m ∧
  S.three = 3 ^ S.m

private theorem singleCornerCriticalInitial_correct :
    singleCornerCriticalInitial.Correct := by
  constructor
  · simp [singleCornerCriticalInitial]
  · constructor
    · simp [singleCornerCriticalInitial, criticalPrefixPhiNat]
    · simp [singleCornerCriticalInitial]

/-- correct state では executable Beatty update が exact。 -/
theorem SingleCornerCriticalState.nextBeta_eq
    {S : SingleCornerCriticalState}
    (hS : S.Correct) :
    S.nextBeta = beattyIndex (S.m + 1) := by
  have hBeta : S.beta = beattyIndex S.m := hS.1
  have hThree : S.three = 3 ^ S.m := hS.2.2
  have hStrict0 := beattyIndex_lt_succ S.m
  have hStrict : S.beta < beattyIndex (S.m + 1) := by
    simpa [hBeta] using hStrict0
  have hLower : S.beta + 1 ≤ beattyIndex (S.m + 1) := by
    omega

  have hUpper0 := beattyIndex_succ_le_add_two S.m
  have hUpper : beattyIndex (S.m + 1) ≤ S.beta + 2 := by
    simpa [hBeta] using hUpper0

  by_cases hOne : S.three * 3 ≤ 2 ^ (S.beta + 2)
  · have hOne' : 3 ^ (S.m + 1) ≤ 2 ^ (S.beta + 2) := by
      rw [pow_succ, ← hThree]
      exact hOne
    have hAtOne : beattyIndex (S.m + 1) ≤ S.beta + 1 := by
      apply beattyIndex_le_of_upper
      simpa [Nat.add_assoc] using hOne'
    have hEq : beattyIndex (S.m + 1) = S.beta + 1 := by omega
    simp [SingleCornerCriticalState.nextBeta, hOne, hEq]
  · have hOne' : ¬ 3 ^ (S.m + 1) ≤ 2 ^ (S.beta + 2) := by
      simpa [pow_succ, hThree] using hOne
    have hNe : beattyIndex (S.m + 1) ≠ S.beta + 1 := by
      intro hEq
      have hU := beattyIndex_upper (S.m + 1)
      rw [hEq] at hU
      apply hOne'
      simpa [Nat.add_assoc] using hU
    have hEq : beattyIndex (S.m + 1) = S.beta + 2 := by omega
    simp [SingleCornerCriticalState.nextBeta, hOne, hEq]

/-- semantic invariant は一 step 保存される。 -/
theorem SingleCornerCriticalState.next_correct
    {S : SingleCornerCriticalState}
    (hS : S.Correct) :
    S.next.Correct := by
  refine ⟨S.nextBeta_eq hS, ?_, ?_⟩
  · change 3 * S.psi + 2 ^ S.beta = criticalPrefixPhiNat (S.m + 1)
    rw [criticalPrefixPhiNat_succ_hensel, hS.1, hS.2.1]
  · change 3 * S.three = 3 ^ (S.m + 1)
    rw [hS.2.2, pow_succ]
    ring

/-- `stateAt` は proof-oriented critical data と exact に一致する。 -/
theorem singleCornerCriticalStateAt_correct
    (n : ℕ) :
    (singleCornerCriticalStateAt n).Correct := by
  induction n with
  | zero => exact singleCornerCriticalInitial_correct
  | succ n ih => exact SingleCornerCriticalState.next_correct ih

/-! ## 2. Hensel state -/

/--
critical suffix を走らせる exact state。

`A` も保持して soundness invariant を局所化する。native 側で safety 判定に使うのは
`q < R` だけ。
-/
structure SingleCornerHenselState where
  m : ℕ
  beta : ℕ
  three : ℕ
  A : ℕ
  R : ℕ
  q : ℕ
deriving Inhabited

namespace SingleCornerHenselState

/-- current modulus `2^(beta+1)`。 -/
def modulus (S : SingleCornerHenselState) : ℕ :=
  2 ^ (S.beta + 1)

/-- return-gap form の safety test。 -/
def Safe (S : SingleCornerHenselState) : Prop :=
  S.q < S.R

/-- executable safety。 -/
def safeBool (S : SingleCornerHenselState) : Bool :=
  decide (S.q < S.R)

/-- semantic invariant。 -/
def Correct (S : SingleCornerHenselState) : Prop :=
  S.beta = beattyIndex S.m ∧
  S.three = 3 ^ S.m ∧
  S.three * S.R + S.A = S.modulus * S.q ∧
  S.R < S.modulus

/--
corner endpoint `c` の affine numerator から canonical Hensel state を初期化する。
大きな inverse は `(b,c)` ごとにこの一回だけ。
-/
def init
    (C : SingleCornerCriticalState)
    (A : ℕ) : SingleCornerHenselState :=
  let H := C.beta + 1
  let modulus := 2 ^ H
  let R :=
    ((-(A : ZMod modulus)) * invThreePow H C.m).val
  let q := (C.three * R + A) / modulus
  {
    m := C.m
    beta := C.beta
    three := C.three
    A := A
    R := R
    q := q
  }

/-- next Beatty value。 -/
def nextBeta (S : SingleCornerHenselState) : ℕ :=
  if S.three * 3 ≤ 2 ^ (S.beta + 2) then
    S.beta + 1
  else
    S.beta + 2

/-- 新規に必要な lift bit 数は `delta+1`。 -/
def liftBits (S : SingleCornerHenselState) : ℕ :=
  S.nextBeta - S.beta + 1

/-- current modulus の半分 `2^beta`。 -/
def halfModulus (S : SingleCornerHenselState) : ℕ :=
  2 ^ S.beta

/-- current representative の top bit。 -/
def topBit (S : SingleCornerHenselState) : ℕ :=
  if S.halfModulus ≤ S.R then 1 else 0

/-- top bit を除いた low representative。 -/
def lowR (S : SingleCornerHenselState) : ℕ :=
  if S.halfModulus ≤ S.R then
    S.R - S.halfModulus
  else
    S.R

/-- 次の `3^(m+1)`。 -/
def nextThree (S : SingleCornerHenselState) : ℕ :=
  3 * S.three

/--
low representative に落とした時の scaled quotient numerator。
correct state では常に nonnegative。
-/
def liftBase (S : SingleCornerHenselState) : ℕ :=
  6 * S.q + 1 - S.topBit * S.nextThree

/-- lift denominator `2^(delta+1)`。correct state では 4 または 8。 -/
def liftDen (S : SingleCornerHenselState) : ℕ :=
  2 ^ S.liftBits

/--
mod 4 / mod 8 の小さい inverse だけで lift digit を決める。
-/
def liftDigit (S : SingleCornerHenselState) : ℕ :=
  ((-(S.liftBase : ZMod (2 ^ S.liftBits))) *
      invThreePow S.liftBits (S.m + 1)).val

/-- critical suffix を一 odd rank 進める exact Hensel update。 -/
def next (S : SingleCornerHenselState) : SingleCornerHenselState :=
  let beta' := S.nextBeta
  let half := S.halfModulus
  let three' := S.nextThree
  let t := S.liftDigit
  let den := S.liftDen
  let base := S.liftBase
  {
    m := S.m + 1
    beta := beta'
    three := three'
    A := 3 * S.A + half
    R := S.lowR + t * half
    q := (base + t * three') / den
  }

/-- n step iterate。 -/
def iterate : ℕ → SingleCornerHenselState → SingleCornerHenselState
  | 0, S => S
  | n + 1, S => iterate n S.next

/-- current state から `fuel` 個の endpoint を全て safety check する。 -/
def scan : ℕ → SingleCornerHenselState → Bool
  | 0, _S => true
  | fuel + 1, S =>
      S.safeBool && scan fuel S.next

end SingleCornerHenselState

/-! ## 3. small arithmetic helpers for Hensel correctness -/

private theorem pow_two_mul_pow_two_add
    (a b : ℕ) :
    2 ^ a * 2 ^ b = 2 ^ (a + b) := by
  rw [← pow_add]

private theorem zmod_val_natCast_of_lt
    {n x : ℕ}
    (hx : x < n) :
    ((x : ZMod n)).val = x := by
  rw [ZMod.val_natCast]
  exact Nat.mod_eq_of_lt hx

/-- canonical congruence solution in a two-power modulus is unique。 -/
theorem twoPowerAffineRepresentative_unique
    {m H A R₁ q₁ R₂ q₂ : ℕ}
    (h₁ : 3 ^ m * R₁ + A = 2 ^ H * q₁)
    (h₂ : 3 ^ m * R₂ + A = 2 ^ H * q₂)
    (hR₁ : R₁ < 2 ^ H)
    (hR₂ : R₂ < 2 ^ H) :
    R₁ = R₂ := by
  letI : NeZero (2 ^ H) := ⟨by positivity⟩
  have hcast₁ := congrArg (fun n : ℕ => (n : ZMod (2 ^ H))) h₁
  have hcast₂ := congrArg (fun n : ℕ => (n : ZMod (2 ^ H))) h₂
  have hEqMul :
      (3 : ZMod (2 ^ H)) ^ m * (R₁ : ZMod (2 ^ H)) =
        (3 : ZMod (2 ^ H)) ^ m * (R₂ : ZMod (2 ^ H)) := by
    push_cast at hcast₁ hcast₂
    have hpow : ((2 : ZMod (2 ^ H)) ^ H) = 0 := by
      exact ZMod.natCast_pow_eq_zero_of_le 2 le_rfl
    rw [hpow, zero_mul] at hcast₁ hcast₂
    have hLeft :
        (3 : ZMod (2 ^ H)) ^ m * (R₁ : ZMod (2 ^ H)) =
          -(A : ZMod (2 ^ H)) :=
      eq_neg_of_add_eq_zero_left hcast₁
    have hRight :
        (3 : ZMod (2 ^ H)) ^ m * (R₂ : ZMod (2 ^ H)) =
          -(A : ZMod (2 ^ H)) :=
      eq_neg_of_add_eq_zero_left hcast₂
    exact hLeft.trans hRight.symm
  have hInv := threePow_mul_invThreePow H m
  have hEqCast :
      (R₁ : ZMod (2 ^ H)) = (R₂ : ZMod (2 ^ H)) := by
    calc
      (R₁ : ZMod (2 ^ H))
          = ((3 : ZMod (2 ^ H)) ^ m * invThreePow H m) *
              (R₁ : ZMod (2 ^ H)) := by rw [hInv]; simp
      _ = invThreePow H m *
            ((3 : ZMod (2 ^ H)) ^ m * (R₁ : ZMod (2 ^ H))) := by ring
      _ = invThreePow H m *
            ((3 : ZMod (2 ^ H)) ^ m * (R₂ : ZMod (2 ^ H))) := by rw [hEqMul]
      _ = ((3 : ZMod (2 ^ H)) ^ m * invThreePow H m) *
            (R₂ : ZMod (2 ^ H)) := by ring
      _ = (R₂ : ZMod (2 ^ H)) := by rw [hInv]; simp
  have hVal := congrArg ZMod.val hEqCast
  rw [zmod_val_natCast_of_lt hR₁, zmod_val_natCast_of_lt hR₂] at hVal
  exact hVal

/--
同じ affine realization の quotient は一意。

`3^m R + A = 2^H q` と
`3^m R + A = 2^H (R + δ)` が同時に成り立てば `q = R + δ`。
-/
theorem twoPowerAffineQuotient_eq_of_same_realization
    {m H A R q δ : ℕ}
    (hQ :
      3 ^ m * R + A = 2 ^ H * q)
    (hEndpoint :
      3 ^ m * R + A = 2 ^ H * (R + δ)) :
    q = R + δ := by
  have hPowPos : 0 < 2 ^ H := by
    positivity
  have hEqMul :
      2 ^ H * q = 2 ^ H * (R + δ) := by
    calc
      2 ^ H * q = 3 ^ m * R + A := hQ.symm
      _ = 2 ^ H * (R + δ) := hEndpoint
  exact Nat.mul_left_cancel hPowPos hEqMul

namespace SingleCornerHenselState

/-- correct state では executable nextBeta が proof-oriented Beatty index と一致。 -/
theorem nextBeta_eq
    {S : SingleCornerHenselState}
    (hS : S.Correct) :
    S.nextBeta = beattyIndex (S.m + 1) := by
  have hBeta : S.beta = beattyIndex S.m := hS.1
  have hThree : S.three = 3 ^ S.m := hS.2.1
  have hStrict0 := beattyIndex_lt_succ S.m
  have hStrict : S.beta < beattyIndex (S.m + 1) := by
    simpa [hBeta] using hStrict0
  have hLower : S.beta + 1 ≤ beattyIndex (S.m + 1) := by
    omega
  have hUpper0 := beattyIndex_succ_le_add_two S.m
  have hUpper : beattyIndex (S.m + 1) ≤ S.beta + 2 := by
    simpa [hBeta] using hUpper0
  by_cases hOne : S.three * 3 ≤ 2 ^ (S.beta + 2)
  · have hOne' : 3 ^ (S.m + 1) ≤ 2 ^ (S.beta + 2) := by
      rw [pow_succ, ← hThree]
      exact hOne
    have hAtOne : beattyIndex (S.m + 1) ≤ S.beta + 1 := by
      apply beattyIndex_le_of_upper
      simpa [Nat.add_assoc] using hOne'
    have hEq : beattyIndex (S.m + 1) = S.beta + 1 := by omega
    simp [SingleCornerHenselState.nextBeta, hOne, hEq]
  · have hOne' : ¬ 3 ^ (S.m + 1) ≤ 2 ^ (S.beta + 2) := by
      simpa [pow_succ, hThree] using hOne
    have hNe : beattyIndex (S.m + 1) ≠ S.beta + 1 := by
      intro hEq
      have hU := beattyIndex_upper (S.m + 1)
      rw [hEq] at hU
      apply hOne'
      simpa [Nat.add_assoc] using hU
    have hEq : beattyIndex (S.m + 1) = S.beta + 2 := by omega
    simp [SingleCornerHenselState.nextBeta, hOne, hEq]

/-- correct state の top bit は 0/1 で、`R = lowR + topBit*2^beta`。 -/
theorem R_eq_low_add_top
    {S : SingleCornerHenselState} :
    S.R = S.lowR + S.topBit * S.halfModulus := by
  unfold lowR topBit halfModulus
  by_cases hTop : 2 ^ S.beta ≤ S.R
  · simp only [hTop, ↓reduceIte, one_mul, Nat.sub_add_cancel]
  · simp only [hTop, ↓reduceIte, zero_mul, add_zero]

/-- low representative は `2^beta` 未満。 -/
theorem lowR_lt_half
    {S : SingleCornerHenselState}
    (hS : S.Correct) :
    S.lowR < S.halfModulus := by
  unfold lowR halfModulus
  by_cases hTop : 2 ^ S.beta ≤ S.R
  · simp [hTop]
    have hMod : S.R < 2 ^ (S.beta + 1) := by
      simpa [modulus] using hS.2.2.2
    rw [pow_succ] at hMod
    omega
  · simp [hTop]
    omega

/-- correct state では top-bit removal 後の lift base は本当に nonnegative。 -/
theorem nextThree_le_sixQ_of_top
    {S : SingleCornerHenselState}
    (hS : S.Correct)
    (hTop : S.halfModulus ≤ S.R) :
    S.nextThree ≤ 6 * S.q := by
  have hThreeR :
      S.three * S.R ≤ S.modulus * S.q := by
    have hEq := hS.2.2.1
    omega
  have hHalfPos : 0 < S.halfModulus := by
    simp [halfModulus]
  have hHalfThree :
      S.halfModulus * S.three ≤
        S.halfModulus * (2 * S.q) := by
    calc
      S.halfModulus * S.three
          = S.three * S.halfModulus := by ring
      _ ≤ S.three * S.R := Nat.mul_le_mul_left _ hTop
      _ ≤ S.modulus * S.q := hThreeR
      _ = S.halfModulus * (2 * S.q) := by
        unfold modulus halfModulus
        rw [pow_succ]
        ring
  have hThree : S.three ≤ 2 * S.q := by
    by_contra hnot
    have hgt : 2 * S.q < S.three := by
      omega
    have hmul :=
      Nat.mul_lt_mul_of_pos_left hgt hHalfPos
    exact (not_lt_of_ge hHalfThree) hmul
  have hMul := Nat.mul_le_mul_left 3 hThree
  calc
    S.nextThree = 3 * S.three := rfl
    _ ≤ 3 * (2 * S.q) := hMul
    _ = 6 * S.q := by ring

/-- liftBase の subtraction は exact。 -/
theorem liftBase_add_top_eq
    {S : SingleCornerHenselState}
    (hS : S.Correct) :
    S.liftBase + S.topBit * S.nextThree = 6 * S.q + 1 := by
  unfold liftBase topBit
  by_cases hTop : S.halfModulus ≤ S.R
  · have hLe := S.nextThree_le_sixQ_of_top hS hTop
    simp [hTop]
    omega
  · simp [hTop]

/-- lift digit は denominator 未満。 -/
theorem liftDigit_lt_den
    (S : SingleCornerHenselState) :
    S.liftDigit < S.liftDen := by
  unfold liftDigit
  haveI : NeZero S.liftDen := ⟨by simp [liftDen]⟩
  exact ZMod.val_lt _

/--
correct state では `nextThree` は次の三冪 `3^(m+1)` に一致する。
-/
theorem nextThree_eq_threePow_succ
    {S : SingleCornerHenselState}
    (hS : S.Correct) :
    S.nextThree = 3 ^ (S.m + 1) := by
  unfold nextThree
  rw [hS.2.1, pow_succ]
  ring

/--
`liftDigit` を lift modulus に戻すと、
`-liftBase` に `3^(m+1)` の逆元を掛けた residue になる。
-/
theorem liftDigit_cast_eq
    (S : SingleCornerHenselState) :
    (S.liftDigit : ZMod (2 ^ S.liftBits)) =
      (-(S.liftBase : ZMod (2 ^ S.liftBits))) *
        invThreePow S.liftBits (S.m + 1) := by
  letI : NeZero (2 ^ S.liftBits) := ⟨by positivity⟩
  unfold liftDigit
  exact ZMod.natCast_zmod_val
    ((-(S.liftBase : ZMod (2 ^ S.liftBits))) *
      invThreePow S.liftBits (S.m + 1))

/--
lift digit の定義により、lift modulus 上で

`liftBase + liftDigit * nextThree = 0`

が成立する。
-/
theorem liftBase_add_liftDigit_mul_nextThree_eq_zero_zmod
    {S : SingleCornerHenselState}
    (hS : S.Correct) :
    ((S.liftBase + S.liftDigit * S.nextThree : ℕ) :
        ZMod (2 ^ S.liftBits)) = 0 := by
  letI : NeZero (2 ^ S.liftBits) := ⟨by positivity⟩

  have hThreeNext :
      S.nextThree = 3 ^ (S.m + 1) :=
    nextThree_eq_threePow_succ hS

  have hT :
      (S.liftDigit : ZMod (2 ^ S.liftBits)) =
        (-(S.liftBase : ZMod (2 ^ S.liftBits))) *
          invThreePow S.liftBits (S.m + 1) :=
    liftDigit_cast_eq S

  have hInv :
      (3 : ZMod (2 ^ S.liftBits)) ^ (S.m + 1) *
          invThreePow S.liftBits (S.m + 1) = 1 :=
    threePow_mul_invThreePow S.liftBits (S.m + 1)

  have hInv' :
      invThreePow S.liftBits (S.m + 1) *
          (3 : ZMod (2 ^ S.liftBits)) ^ (S.m + 1) = 1 := by
    calc
      invThreePow S.liftBits (S.m + 1) *
          (3 : ZMod (2 ^ S.liftBits)) ^ (S.m + 1)
          =
        (3 : ZMod (2 ^ S.liftBits)) ^ (S.m + 1) *
          invThreePow S.liftBits (S.m + 1) := by
            exact mul_comm _ _
      _ = 1 := hInv

  push_cast
  rw [hT, hThreeNext]
  push_cast

  change
    (S.liftBase : ZMod (2 ^ S.liftBits)) +
      (-(S.liftBase : ZMod (2 ^ S.liftBits)) *
        invThreePow S.liftBits (S.m + 1)) *
        (3 : ZMod (2 ^ S.liftBits)) ^ (S.m + 1) = 0

  calc
    (S.liftBase : ZMod (2 ^ S.liftBits)) +
        (-(S.liftBase : ZMod (2 ^ S.liftBits)) *
          invThreePow S.liftBits (S.m + 1)) *
          (3 : ZMod (2 ^ S.liftBits)) ^ (S.m + 1)
        =
      (S.liftBase : ZMod (2 ^ S.liftBits)) +
        (-(S.liftBase : ZMod (2 ^ S.liftBits))) *
          (invThreePow S.liftBits (S.m + 1) *
            (3 : ZMod (2 ^ S.liftBits)) ^ (S.m + 1)) := by
          ring
    _ =
      (S.liftBase : ZMod (2 ^ S.liftBits)) +
        (-(S.liftBase : ZMod (2 ^ S.liftBits))) := by
          rw [hInv']
          simp
    _ = 0 := by
          ring

/--
lift digit は required small congruence を解く。
-/
theorem liftDigit_congruence
    {S : SingleCornerHenselState}
    (hS : S.Correct) :
    (S.liftBase + S.liftDigit * S.nextThree) % S.liftDen = 0 := by
  have hZero :
      ((S.liftBase + S.liftDigit * S.nextThree : ℕ) :
          ZMod (2 ^ S.liftBits)) = 0 :=
    liftBase_add_liftDigit_mul_nextThree_eq_zero_zmod hS

  have hVal := congrArg ZMod.val hZero
  rw [ZMod.val_natCast] at hVal
  simpa [liftDen] using hVal

/--
lift congruence が 0 なら、lift quotient による除算は余りなしで exact に戻る。
-/
theorem liftDen_mul_liftQuotient_eq
    {S : SingleCornerHenselState}
    (hS : S.Correct) :
    S.liftDen *
        ((S.liftBase + S.liftDigit * S.nextThree) / S.liftDen) =
      S.liftBase + S.liftDigit * S.nextThree := by
  have hCong := S.liftDigit_congruence hS
  have h :=
    Nat.mod_add_div
      (S.liftBase + S.liftDigit * S.nextThree)
      S.liftDen
  rw [hCong] at h
  simpa [Nat.mul_comm] using h

/--
current modulus は half modulus のちょうど2倍。
-/
theorem modulus_eq_two_mul_halfModulus
    (S : SingleCornerHenselState) :
    S.modulus = 2 * S.halfModulus := by
  unfold modulus halfModulus
  rw [pow_succ]
  ring

/--
旧 state の exact invariant と top-bit decomposition を組み合わせると、
low representative 側の次 affine numerator は
`halfModulus * liftBase` に一致する。
-/
theorem nextThree_mul_lowR_add_nextAffine_eq_half_mul_liftBase
    {S : SingleCornerHenselState}
    (hS : S.Correct) :
    S.nextThree * S.lowR +
        (3 * S.A + S.halfModulus) =
      S.halfModulus * S.liftBase := by
  have hRDecomp :
      S.R =
        S.lowR + S.topBit * S.halfModulus :=
    R_eq_low_add_top (S := S)

  have hBase :
      S.liftBase + S.topBit * S.nextThree =
        6 * S.q + 1 :=
    liftBase_add_top_eq hS

  have hModEq :
      S.modulus = 2 * S.halfModulus := by
    unfold modulus halfModulus
    rw [pow_succ]
    ring

  have hEq :
      S.three * S.R + S.A =
        S.modulus * S.q :=
    hS.2.2.1

  rw [hRDecomp, hModEq] at hEq

  have hEqZ :=
    congrArg (fun n : ℕ => (n : ℤ)) hEq

  have hBaseZ :=
    congrArg (fun n : ℕ => (n : ℤ)) hBase

  push_cast at hEqZ hBaseZ

  have hNextThreeZ :
      (S.nextThree : ℤ) =
        3 * (S.three : ℤ) := by
    unfold nextThree
    push_cast
    ring

  have hScaledZ :
      (S.nextThree : ℤ) * (S.lowR : ℤ) +
          (3 * (S.A : ℤ) + (S.halfModulus : ℤ)) =
        (S.halfModulus : ℤ) * (S.liftBase : ℤ) := by
    rw [hNextThreeZ]
    rw [hNextThreeZ] at hBaseZ
    linear_combination
      3 * hEqZ - (S.halfModulus : ℤ) * hBaseZ

  exact_mod_cast hScaledZ

/--
`nextBeta` は current beta にその増分を足した形に exact に書ける。
-/
theorem nextBeta_eq_beta_add_diff
    (S : SingleCornerHenselState) :
    S.nextBeta =
      S.beta + (S.nextBeta - S.beta) := by
  have hLe :
      S.beta ≤ S.nextBeta := by
    unfold nextBeta
    split <;> omega
  omega

/--
次の modulus `2^(nextBeta+1)` は、
current half modulus と lift denominator の積に一致する。
-/
theorem nextModulus_eq_half_mul_liftDen
    (S : SingleCornerHenselState) :
    2 ^ (S.nextBeta + 1) =
      S.halfModulus * S.liftDen := by
  have hBetaDiff :
      S.nextBeta =
        S.beta + (S.nextBeta - S.beta) :=
    nextBeta_eq_beta_add_diff S
  unfold halfModulus liftDen liftBits
  rw [hBetaDiff]
  have hExp :
      S.beta + (S.nextBeta - S.beta) + 1 =
        S.beta + ((S.nextBeta - S.beta) + 1) := by
    omega
  rw [hExp, pow_add]
  simp

/--
一回の Hensel update は exact affine equation

`three * R + A = modulus * q`

を保存する。
-/
theorem next_affineInvariant
    {S : SingleCornerHenselState}
    (hS : S.Correct) :
    S.next.three * S.next.R + S.next.A =
      S.next.modulus * S.next.q := by
  have hDivEq :=
    S.liftDen_mul_liftQuotient_eq hS

  have hScaledBase :=
    S.nextThree_mul_lowR_add_nextAffine_eq_half_mul_liftBase hS

  have hNewMod :=
    nextModulus_eq_half_mul_liftDen S

  change
    S.nextThree *
          (S.lowR + S.liftDigit * S.halfModulus) +
        (3 * S.A + S.halfModulus) =
      2 ^ (S.nextBeta + 1) *
        ((S.liftBase + S.liftDigit * S.nextThree) /
          S.liftDen)

  rw [hNewMod, mul_assoc, hDivEq]

  calc
    S.nextThree *
          (S.lowR + S.liftDigit * S.halfModulus) +
        (3 * S.A + S.halfModulus)
        =
      (S.nextThree * S.lowR +
          (3 * S.A + S.halfModulus)) +
        S.nextThree * (S.liftDigit * S.halfModulus) := by
          ring
    _ =
      S.halfModulus * S.liftBase +
        S.nextThree * (S.liftDigit * S.halfModulus) := by
          rw [hScaledBase]
    _ =
      S.halfModulus *
        (S.liftBase + S.liftDigit * S.nextThree) := by
          ring

/--
一回 lift した新 representative は、次 modulus の canonical range 内に残る。
-/
theorem next_R_lt_modulus
    {S : SingleCornerHenselState}
    (hS : S.Correct) :
    S.next.R < S.next.modulus := by
  have hNewMod :=
    nextModulus_eq_half_mul_liftDen S

  change
    S.lowR + S.liftDigit * S.halfModulus <
      2 ^ (S.nextBeta + 1)

  rw [hNewMod]

  have hLow :
      S.lowR < S.halfModulus :=
    S.lowR_lt_half hS

  have hDigitLt :
      S.liftDigit < S.liftDen :=
    S.liftDigit_lt_den

  have hLt :
      S.lowR + S.liftDigit * S.halfModulus <
        S.halfModulus +
          S.liftDigit * S.halfModulus :=
    Nat.add_lt_add_right hLow _

  have hStep :
      S.halfModulus +
          S.liftDigit * S.halfModulus =
        (S.liftDigit + 1) * S.halfModulus := by
    ring

  have hDigit :
      S.liftDigit + 1 ≤ S.liftDen := by
    omega

  have hLe :
      (S.liftDigit + 1) * S.halfModulus ≤
        S.liftDen * S.halfModulus :=
    Nat.mul_le_mul_right S.halfModulus hDigit

  calc
    S.lowR + S.liftDigit * S.halfModulus
        <
      S.halfModulus +
        S.liftDigit * S.halfModulus := hLt
    _ = (S.liftDigit + 1) * S.halfModulus := hStep
    _ ≤ S.liftDen * S.halfModulus := hLe
    _ = S.halfModulus * S.liftDen := by
      ring

/--
一回の Hensel update は exact state invariant をすべて保存する。

具体的には、次の Beatty index、三冪、exact affine equation、
canonical representative range の4条件が同時に保たれる。
-/
theorem next_correct
    {S : SingleCornerHenselState}
    (hS : S.Correct) :
    S.next.Correct := by
  refine ⟨?_, ?_, ?_, ?_⟩

  · have hBetaNext :
        S.nextBeta = beattyIndex (S.m + 1) :=
      S.nextBeta_eq hS
    simpa [next] using hBetaNext

  · have hThreeNext :
        S.nextThree = 3 ^ (S.m + 1) :=
      S.nextThree_eq_threePow_succ hS
    simpa [next] using hThreeNext

  · exact next_affineInvariant hS

  · exact S.next_R_lt_modulus hS

/-- init state は exact canonical congruence state。 -/
theorem init_correct
    {C : SingleCornerCriticalState}
    (hC : C.Correct)
    (A : ℕ) :
    (init C A).Correct := by
  let H := C.beta + 1
  let modulus := 2 ^ H
  let R := ((-(A : ZMod modulus)) * invThreePow H C.m).val
  let numerator := C.three * R + A
  have hModPos : 0 < modulus := by simp [modulus]
  haveI : NeZero modulus := ⟨Nat.ne_of_gt hModPos⟩
  have hRlt : R < modulus := by
    dsimp [R]
    exact ZMod.val_lt _
  have hRcast :
      (R : ZMod modulus) =
        (-(A : ZMod modulus)) * invThreePow H C.m := by
    dsimp [R]
    simp
  have hInv := threePow_mul_invThreePow H C.m
  have hZero :
      (numerator : ZMod modulus) = 0 := by
    dsimp [numerator]
    push_cast
    rw [hC.2.2, hRcast]
    push_cast
    calc
      (3 : ZMod modulus) ^ C.m *
            (-(A : ZMod modulus) * invThreePow H C.m) +
          (A : ZMod modulus)
          =
        -(A : ZMod modulus) *
            ((3 : ZMod modulus) ^ C.m * invThreePow H C.m) +
          (A : ZMod modulus) := by ring
      _ = 0 := by rw [hInv]; ring
  have hModZero : numerator % modulus = 0 := by
    have hVal := congrArg ZMod.val hZero
    rw [ZMod.val_natCast] at hVal
    simpa using hVal
  have hEq :
      modulus * (numerator / modulus) = numerator := by
    have h := Nat.mod_add_div numerator modulus
    rw [hModZero] at h
    simpa [Nat.mul_comm] using h
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [init, H] using hC.1
  · simpa [init] using hC.2.2
  · change C.three * R + A = modulus * (numerator / modulus)
    rw [hEq]
  · exact hRlt

/-- iterate 後の odd rank。 -/
@[simp] theorem iterate_m
    (n : ℕ)
    (S : SingleCornerHenselState) :
    (iterate n S).m = S.m + n := by
  induction n generalizing S with
  | zero => simp [iterate]
  | succ n ih =>
      simp [iterate, ih, next]
      omega

/--
correct state から始めれば、任意回数の Hensel iterate 後も
exact state invariant は保存される。
-/
theorem iterate_correct
    (n : ℕ)
    {S : SingleCornerHenselState}
    (hS : S.Correct) :
    (iterate n S).Correct := by
  induction n generalizing S with
  | zero =>
      simpa [iterate] using hS
  | succ n ih =>
      change (iterate n S.next).Correct
      exact ih (S := S.next) (S.next_correct hS)

/--
executable safety test が true なら semantic safety が成立する。
-/
theorem safe_of_safeBool_eq_true
    {S : SingleCornerHenselState}
    (h : S.safeBool = true) :
    S.Safe := by
  change S.q < S.R
  unfold safeBool at h
  exact of_decide_eq_true h

/-- scan が true なら任意 checked offset の state は safe。 -/
theorem scan_sound :
    ∀ fuel : ℕ,
      ∀ S : SingleCornerHenselState,
        scan fuel S = true →
        ∀ j : ℕ, j < fuel →
          (iterate j S).Safe := by
  intro fuel
  induction fuel with
  | zero =>
      intro S _h j hj
      omega
  | succ fuel ih =>
      intro S hScan j hj
      have hSplit :
          S.safeBool = true ∧ scan fuel S.next = true := by
        simpa [scan] using hScan
      rcases hSplit with ⟨hHead, hTail⟩
      cases j with
      | zero =>
          exact safe_of_safeBool_eq_true hHead
      | succ j =>
          have hj' : j < fuel := by omega
          have hSafe := ih S.next hTail j hj'
          simpa [iterate] using hSafe


/-! ## 3.5 205-bit frozen tail certificate -/

/--
finite card-one box `m ≤ 2270` で actual representative を比較する共通上界。

native scanner はこの値そのものを用いて、rank 130 以降の
205-bit representative residue が actual 側の取り得る範囲より上にあることだけを検査する。
-/
def frozen205RepresentativeBound : ℕ :=
  rhinGapK * 2271 ^ 15

/-- representative の下位 205 bit。 -/
def frozen205Residue (S : SingleCornerHenselState) : ℕ :=
  S.R % (2 ^ 205)

/-- frozen residue が finite actual bound を越えているかの executable 判定。 -/
def frozen205Bool (S : SingleCornerHenselState) : Bool :=
  decide (frozen205RepresentativeBound < S.frozen205Residue)

/--
rank 130 までだけ safety を直接検査し、終端では 205-bit frozen residue を検査する。

`fuel = 130 - c` として使う。`c ≥ 130` なら `fuel = 0` なので
長い suffix scan は一切行わず residue check だけになる。
-/
def scanToFreeze205 : ℕ → SingleCornerHenselState → Bool
  | 0, S => S.frozen205Bool
  | fuel + 1, S =>
      S.safeBool && scanToFreeze205 fuel S.next

/-- finite actual bound は 205-bit modulus より小さい。 -/
theorem frozen205RepresentativeBound_lt_pow205 :
    frozen205RepresentativeBound < 2 ^ 205 := by
  native_decide

/-- executable `nextBeta` は current beta を下げない。 -/
theorem beta_le_next_beta
    (S : SingleCornerHenselState) :
    S.beta ≤ S.next.beta := by
  change S.beta ≤ S.nextBeta
  unfold nextBeta
  split <;> omega

/--
`e ≤ beta` なら、一回の Hensel lift は representative の下位 `e` bit を変えない。

205-bit freeze はこの一般 filtration invariance の specialization。
-/
theorem residue_next_eq_of_le_beta
    {S : SingleCornerHenselState}
    {e : ℕ}
    (hBeta : e ≤ S.beta) :
    S.next.R % (2 ^ e) = S.R % (2 ^ e) := by
  have hHalfZero :
      (S.halfModulus : ZMod (2 ^ e)) = 0 := by
    unfold halfModulus
    push_cast
    exact ZMod.natCast_pow_eq_zero_of_le 2 hBeta

  have hCast :
      (S.next.R : ZMod (2 ^ e)) =
        (S.R : ZMod (2 ^ e)) := by
    change
      ((S.lowR + S.liftDigit * S.halfModulus : ℕ) :
          ZMod (2 ^ e)) =
        (S.R : ZMod (2 ^ e))
    rw [R_eq_low_add_top (S := S)]
    push_cast
    rw [hHalfZero]
    ring

  have hVal := congrArg ZMod.val hCast
  rw [ZMod.val_natCast, ZMod.val_natCast] at hVal
  exact hVal

/--
一度 `e ≤ beta` に入れば、その後の任意 iterate で下位 `e` bit は固定される。
-/
theorem iterate_residue_eq_of_le_beta
    (n : ℕ)
    {S : SingleCornerHenselState}
    {e : ℕ}
    (hBeta : e ≤ S.beta) :
    (iterate n S).R % (2 ^ e) = S.R % (2 ^ e) := by
  induction n generalizing S with
  | zero =>
      rfl
  | succ n ih =>
      change
        (iterate n S.next).R % (2 ^ e) =
          S.R % (2 ^ e)
      have hBetaNext : e ≤ S.next.beta :=
        le_trans hBeta (S.beta_le_next_beta)
      calc
        (iterate n S.next).R % (2 ^ e)
            = S.next.R % (2 ^ e) :=
          ih (S := S.next) hBetaNext
        _ = S.R % (2 ^ e) :=
          residue_next_eq_of_le_beta hBeta

/--
`beta ≥ 205` なら、一回の Hensel lift は representative の下位 205 bit を変えない。
-/
theorem frozen205Residue_next_eq
    {S : SingleCornerHenselState}
    (hBeta : 205 ≤ S.beta) :
    S.next.frozen205Residue = S.frozen205Residue := by
  simpa [frozen205Residue] using
    (residue_next_eq_of_le_beta (S := S) (e := 205) hBeta)

/--
一度 `beta ≥ 205` に入れば、その後の任意 iterate で 205-bit residue は固定される。
-/
theorem iterate_frozen205Residue_eq
    (n : ℕ)
    {S : SingleCornerHenselState}
    (hBeta : 205 ≤ S.beta) :
    (iterate n S).frozen205Residue = S.frozen205Residue := by
  simpa [frozen205Residue] using
    (iterate_residue_eq_of_le_beta (n := n) (S := S) (e := 205) hBeta)

/-- iterate の加法則。freeze point から残り tail を切り出すために使う。 -/
theorem iterate_add
    (a b : ℕ)
    (S : SingleCornerHenselState) :
    iterate (a + b) S =
      iterate b (iterate a S) := by
  induction a generalizing S with
  | zero =>
      simp [iterate]
  | succ a ih =>
      rw [Nat.succ_add]
      change
        iterate (a + b) S.next =
          iterate b (iterate a S.next)
      exact ih (S := S.next)

/--
correct state で rank が 130 以上なら beta は 205 以上。
実際には `beta_130 = 206` なので 1 bit の余裕がある。
-/
theorem beta_ge_205_of_correct_m_ge_130
    {S : SingleCornerHenselState}
    (hS : S.Correct)
    (hm : 130 ≤ S.m) :
    205 ≤ S.beta := by
  have hMono :
      beattyIndex 130 ≤ beattyIndex S.m := by
    rcases lt_or_eq_of_le hm with hlt | hEq
    · exact Nat.le_of_lt (beattyIndex_strictMono hlt)
    · exact le_of_eq (congrArg beattyIndex hEq)
  rw [beattyIndex_130_eq_206] at hMono
  rw [hS.1]
  omega

/--
frozen scanner が true なら、

* freeze point より前の全 state は safe。
* freeze point の 205-bit residue は finite actual bound より大きい。

という二つの certificate を同時に得る。
-/
theorem scanToFreeze205_sound :
    ∀ fuel : ℕ,
      ∀ S : SingleCornerHenselState,
        scanToFreeze205 fuel S = true →
          (∀ j : ℕ, j < fuel → (iterate j S).Safe) ∧
          frozen205RepresentativeBound <
            (iterate fuel S).frozen205Residue := by
  intro fuel
  induction fuel with
  | zero =>
      intro S hScan
      constructor
      · intro j hj
        omega
      · change frozen205RepresentativeBound < S.frozen205Residue
        unfold scanToFreeze205 frozen205Bool at hScan
        exact of_decide_eq_true hScan
  | succ fuel ih =>
      intro S hScan
      have hSplit :
          S.safeBool = true ∧
            scanToFreeze205 fuel S.next = true := by
        simpa [scanToFreeze205] using hScan
      rcases hSplit with ⟨hHead, hTail⟩
      have hTailSound := ih S.next hTail
      rcases hTailSound with ⟨hSafeTail, hResidue⟩
      constructor
      · intro j hj
        cases j with
        | zero =>
            exact safe_of_safeBool_eq_true hHead
        | succ j =>
            have hj' : j < fuel := by
              omega
            have hSafe := hSafeTail j hj'
            simpa [iterate] using hSafe
      · simpa [iterate] using hResidue

end SingleCornerHenselState

/-! ## 4. bounded candidate scanner -/

/-- straight run の elementary `2/3` geometric accumulator。 -/
def singleCornerTwoThreeSum : ℕ → ℕ
  | 0 => 0
  | n + 1 => 3 * singleCornerTwoThreeSum n + 2 ^ n

/--
straight interval endpoint `c=b+n` での closed affine numerator。
subtraction を避け、geometric part は recurrence で executable に保持する。
-/
def singleCornerInitialAffine
    (B : SingleCornerCriticalState)
    (n : ℕ) : ℕ :=
  3 ^ n * B.psi +
    2 ^ (B.beta - 1) * singleCornerTwoThreeSum n

/-- actual single-corner entrance に必要な Beatty jump-2 test。 -/
def singleCornerHenselEntranceBool
    (b : ℕ) : Bool :=
  if b = 0 then
    false
  else
    decide
      ((singleCornerCriticalStateAt b).beta =
        (singleCornerCriticalStateAt (b - 1)).beta + 2)

/--
fixed `(b,n)` candidate は rank 130 までだけ直接 safety scan する。

rank 130 以降では representative の下位 205 bit が freeze するため、
終端 state では frozen residue が finite actual bound を越えることだけを検査する。
-/
def singleCornerHenselCandidateCheck
    (b n : ℕ) : Bool :=
  if b = 0 ∨ 116 ≤ b ∨ n = 0 ∨ 214 ≤ n then
    true
  else if singleCornerHenselEntranceBool b then
    let c := b + n
    let B := singleCornerCriticalStateAt b
    let C := singleCornerCriticalStateAt c
    let A := singleCornerInitialAffine B n
    let S0 := SingleCornerHenselState.init C A
    SingleCornerHenselState.scanToFreeze205 (130 - c) S0
  else
    true

/-- simple bounded Nat forall。 -/
def singleCornerAllNat
    (start fuel : ℕ)
    (f : ℕ → Bool) : Bool :=
  match fuel with
  | 0 => true
  | r + 1 =>
      f start && singleCornerAllNat (start + 1) r f

/-- fixed b の widths `1..213`。 -/
def singleCornerHenselCheckB
    (b : ℕ) : Bool :=
  if singleCornerHenselEntranceBool b then
    singleCornerAllNat 1 213 (fun n => singleCornerHenselCandidateCheck b n)
  else
    true

/-- consecutive b range。 -/
def singleCornerHenselCheckBRange
    (start fuel : ℕ) : Bool :=
  singleCornerAllNat start fuel singleCornerHenselCheckB

/-- bounded forall の soundness。 -/
theorem singleCornerAllNat_sound :
    ∀ start fuel : ℕ,
      ∀ f : ℕ → Bool,
        singleCornerAllNat start fuel f = true →
        ∀ k : ℕ,
          start ≤ k →
          k < start + fuel →
          f k = true := by
  intro start fuel
  induction fuel generalizing start with
  | zero =>
      intro f _h k _h1 h2
      omega
  | succ fuel ih =>
      intro f hAll k hsk hk
      have hSplit :
          f start = true ∧
            singleCornerAllNat (start + 1) fuel f = true := by
        simpa [singleCornerAllNat] using hAll
      rcases hSplit with ⟨hHead, hTail⟩
      by_cases hEq : k = start
      · subst k
        exact hHead
      · exact ih (start + 1) f hTail k (by omega) (by omega)

/-! ## 5. frozen native chunks -/

/-- `1 <= b <= 15`。 -/
theorem singleCornerHenselCheck_b001_015 :
    singleCornerHenselCheckBRange 1 15 = true := by
  native_decide

/-- `16 <= b <= 30`。 -/
theorem singleCornerHenselCheck_b016_030 :
    singleCornerHenselCheckBRange 16 15 = true := by
  native_decide

/-- `31 <= b <= 45`。 -/
theorem singleCornerHenselCheck_b031_045 :
    singleCornerHenselCheckBRange 31 15 = true := by
  native_decide

/-- `46 <= b <= 60`。 -/
theorem singleCornerHenselCheck_b046_060 :
    singleCornerHenselCheckBRange 46 15 = true := by
  native_decide

/-- `61 <= b <= 75`。 -/
theorem singleCornerHenselCheck_b061_075 :
    singleCornerHenselCheckBRange 61 15 = true := by
  native_decide

/-- `76 <= b <= 90`。 -/
theorem singleCornerHenselCheck_b076_090 :
    singleCornerHenselCheckBRange 76 15 = true := by
  native_decide

/-- `91 <= b <= 105`。 -/
theorem singleCornerHenselCheck_b091_105 :
    singleCornerHenselCheckBRange 91 15 = true := by
  native_decide

/-- `106 <= b <= 115`。 -/
theorem singleCornerHenselCheck_b106_115 :
    singleCornerHenselCheckBRange 106 10 = true := by
  native_decide

/-- 任意 `0<b<116` の b-check を frozen chunks から読む。 -/
theorem singleCornerHenselCheckB_of_pos_lt_116
    {b : ℕ}
    (hbPos : 0 < b)
    (hbLt : b < 116) :
    singleCornerHenselCheckB b = true := by
  by_cases h15 : b ≤ 15
  · exact singleCornerAllNat_sound 1 15 _
      singleCornerHenselCheck_b001_015 b (by omega) (by omega)
  by_cases h30 : b ≤ 30
  · exact singleCornerAllNat_sound 16 15 _
      singleCornerHenselCheck_b016_030 b (by omega) (by omega)
  by_cases h45 : b ≤ 45
  · exact singleCornerAllNat_sound 31 15 _
      singleCornerHenselCheck_b031_045 b (by omega) (by omega)
  by_cases h60 : b ≤ 60
  · exact singleCornerAllNat_sound 46 15 _
      singleCornerHenselCheck_b046_060 b (by omega) (by omega)
  by_cases h75 : b ≤ 75
  · exact singleCornerAllNat_sound 61 15 _
      singleCornerHenselCheck_b061_075 b (by omega) (by omega)
  by_cases h90 : b ≤ 90
  · exact singleCornerAllNat_sound 76 15 _
      singleCornerHenselCheck_b076_090 b (by omega) (by omega)
  by_cases h105 : b ≤ 105
  · exact singleCornerAllNat_sound 91 15 _
      singleCornerHenselCheck_b091_105 b (by omega) (by omega)
  · exact singleCornerAllNat_sound 106 10 _
      singleCornerHenselCheck_b106_115 b (by omega) (by omega)

/--
actual bounds に入る一 candidate の suffix check を取り出す public arithmetic theorem。
-/
theorem singleCornerHenselCandidateCheck_of_bounds
    {b n : ℕ}
    (hbPos : 0 < b)
    (hbLt : b < 116)
    (hnPos : 0 < n)
    (hnLe : n ≤ 213)
    (hEntrance :
      (singleCornerCriticalStateAt b).beta =
        (singleCornerCriticalStateAt (b - 1)).beta + 2) :
    singleCornerHenselCandidateCheck b n = true := by
  have hB := singleCornerHenselCheckB_of_pos_lt_116 hbPos hbLt
  have hEntranceBool : singleCornerHenselEntranceBool b = true := by
    simp [singleCornerHenselEntranceBool, Nat.ne_of_gt hbPos, hEntrance]
  unfold singleCornerHenselCheckB at hB
  rw [if_pos hEntranceBool] at hB
  have hN :=
    singleCornerAllNat_sound 1 213
      (fun n => singleCornerHenselCandidateCheck b n)
      hB n (by omega) (by omega)
  exact hN


/--
actual finite bounds に入る candidate では、native certificate を
「rank 130 までの短い scan + 205-bit frozen residue」の形で直接取り出せる。
-/
theorem singleCornerHenselCandidateFreezeCheck_of_bounds
    {b n : ℕ}
    (hbPos : 0 < b)
    (hbLt : b < 116)
    (hnPos : 0 < n)
    (hnLe : n ≤ 213)
    (hEntrance :
      (singleCornerCriticalStateAt b).beta =
        (singleCornerCriticalStateAt (b - 1)).beta + 2) :
    SingleCornerHenselState.scanToFreeze205 (130 - (b + n))
      (SingleCornerHenselState.init
        (singleCornerCriticalStateAt (b + n))
        (singleCornerInitialAffine
          (singleCornerCriticalStateAt b) n)) = true := by
  have hCandidate :=
    singleCornerHenselCandidateCheck_of_bounds
      hbPos hbLt hnPos hnLe hEntrance
  have hEntranceBool :
      singleCornerHenselEntranceBool b = true := by
    simp [
      singleCornerHenselEntranceBool,
      Nat.ne_of_gt hbPos,
      hEntrance
    ]
  have hGuard :
      ¬ (b = 0 ∨ 116 ≤ b ∨ n = 0 ∨ 214 ≤ n) := by
    omega
  simpa [
    singleCornerHenselCandidateCheck,
    hGuard,
    hEntranceBool
  ] using hCandidate

end ExternalArithmetic
end CSTMicro
end Collatz2
