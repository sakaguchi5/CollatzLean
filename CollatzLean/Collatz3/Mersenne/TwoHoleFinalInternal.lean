import CollatzLean.Collatz3.Mersenne.TwoHoleFiniteInternal
import CollatzLean.Collatz3.Mersenne.TwoAdicArithmetic
import CollatzLean.Collatz3.Arithmetic.ThreeOrderModTwoPow
import CollatzLean.Collatz3.Binary.SparseComplement
import CollatzLean.Collatz3.Binary.BlockPeriod
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option exponentiation.threshold 394
/-!
# Collatz3 Mersenne: A2 最終 interface 前の無条件算術

A2 の外部入力を A1 と同じ「明示的 bound + bounded finite sieve」型へ移す前に、
Collatz 固有の elementary 部分を内部 theorem として固定する。

このファイルでは外部の Chim / Gouillon / Stephan 型定理を仮定しない。

* source-even resonance `(a,b)=(1,2)` では M₄ class と `mod 2^394` を合わせ、
  `2^392 ∣ k` を無条件に得る。
* split regular branch では exact second-cut identity と、source hole `a` と
  `v₂(k)+2` / `v₂(k-1)+2` の三分岐を固定する。
* target-two `n=1` では canonical binary word を直接構成し、period 1 の
  break 数が高々 6 であることを内部証明する。
-/

namespace Collatz3
namespace Mersenne

open Arithmetic

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-! ## source-even: `2^392 ∣ k` -/

/--
source-even resonance の M₄ class は、深さに巨大な 2-adic divisibility を強制する。

`k≥7` と `(a,b)=(1,2)` の exact equation から

* `k` は 4 の倍数、
* `r=3`,
* `n≥394`, `L+3≥394`,
* `3^k ≡ 1 (mod 2^394)`

を得る。`ord_(2^394)(3)=2^392` より `2^392 ∣ k`。
-/
theorem SourceTwoHoleEquation.evenLowResonance_twoPow392_dvd_depth
    {k n r L : ℕ}
    (hk7 : 7 ≤ k)
    (hEq : SourceTwoHoleEquation k n r L 1 2) :
    2 ^ 392 ∣ k := by
  have hClass :=
    hEq.evenLowResonance_m4_classification (by omega : 6 ≤ k)
  rcases hClass with ⟨hK, hN, hR, hT⟩
  have hn394 : 394 ≤ n := by
    have hle := Nat.mod_le n 486
    omega
  have hL391 : 391 ≤ L := by
    have hle := Nat.mod_le L 486
    omega
  have hr3le : 3 ≤ r := by
    have hle := Nat.mod_le r 486
    omega
  have hKdecomp := Nat.mod_add_div (k - 6) 972
  rw [hK] at hKdecomp
  have hkForm :
      k = 972 * ((k - 6) / 972 + 1) := by
    omega
  have hk4 : k % 4 = 0 := by
    rw [hkForm]
    simp [Nat.mul_mod]
  have hr3 : r = 3 := by
    by_contra hne
    have hr4 : 4 ≤ r := by omega
    have hMod := hEq.to_mod 16
    unfold SourceTwoHoleModEquation at hMod
    have hThreePeriod : (3 : ZMod 16) ^ 4 = 1 := by decide
    have hThree : (3 : ZMod 16) ^ k = 1 := by
      rw [pow_eq_pow_mod_of_pow_eq_one (3 : ZMod 16) (e := k) hThreePeriod]
      simp [hk4]
    have hNZero : (2 : ZMod 16) ^ n = 0 := by
      simpa using ZMod.natCast_pow_eq_zero_of_le 2 (by omega : 4 ≤ n)
    have hLZero : (2 : ZMod 16) ^ L = 0 := by
      simpa using ZMod.natCast_pow_eq_zero_of_le 2 (by omega : 4 ≤ L)
    have hRZero : (2 : ZMod 16) ^ r = 0 := by
      simpa using ZMod.natCast_pow_eq_zero_of_le 2 hr4
    rw [hThree, hNZero, hLZero, hRZero] at hMod
    norm_num at hMod
    exact (by decide : (-7 : ZMod 16) ≠ 1) hMod
  subst r
  let M : ℕ := 2 ^ 394
  have hMod := hEq.to_mod M
  unfold SourceTwoHoleModEquation at hMod
  have hNZero : (2 : ZMod M) ^ n = 0 := by
    dsimp [M]
    simpa using ZMod.natCast_pow_eq_zero_of_le 2 hn394
  have hTopZero : (2 : ZMod M) ^ (L + 3) = 0 := by
    dsimp [M]
    simpa using
      ZMod.natCast_pow_eq_zero_of_le 2 (by omega : 394 ≤ L + 3)
  have hEightLZero :
      (8 : ZMod M) * (2 : ZMod M) ^ L = 0 := by
    have h := hTopZero
    rw [show L + 3 = 3 + L by omega, pow_add] at h
    norm_num at h
    simpa using h
  rw [hNZero] at hMod
  norm_num at hMod
  have hCore :
      (7 : ZMod M) * ((3 : ZMod M) ^ k - 1) = 0 := by
    linear_combination -hMod - hEightLZero
  have hSevenUnit : IsUnit (7 : ZMod M) := by
    dsimp [M]
    exact
      (ZMod.isUnit_iff_coprime 7 (2 ^ 394)).2
        (by norm_num)
  have hSevenEq :
      (7 : ZMod M) * (3 : ZMod M) ^ k =
        (7 : ZMod M) * 1 := by
    linear_combination hCore
  have hPowEq : (3 : ZMod M) ^ k = 1 :=
    hSevenUnit.mul_left_cancel hSevenEq
  have hCong : 3 ^ k ≡ 1 [MOD 2 ^ 394] := by
    dsimp [M] at hPowEq
    simpa [← ZMod.natCast_eq_natCast_iff] using hPowEq
  have hDvd :=
    Arithmetic.twoPow_dvd_exponent_of_threePow_modEq_one
      (r := 394) (m := k) (by norm_num) hCong
  norm_num at hDvd ⊢
  exact hDvd

/-! ## split regular: second cut -/

/--
二つの正整数の 2-adic valuation が異なるとき、和の valuation は小さい方に等しい。

後段の second-cut で同じ議論を二度書かないための局所補題。
-/
private theorem padicValNat_add_eq_left_of_lt
    {x y : ℕ}
    (hx : x ≠ 0)
    (hy : y ≠ 0)
    (hxy : padicValNat 2 x < padicValNat 2 y) :
    padicValNat 2 (x + y) = padicValNat 2 x := by
  have hSum0 : x + y ≠ 0 := by omega
  have hxDvd : 2 ^ padicValNat 2 x ∣ x :=
    pow_padicValNat_dvd
  have hyDvd : 2 ^ padicValNat 2 x ∣ y :=
    (padicValNat_dvd_iff_le hy).2 (by omega)
  have hSumDvd : 2 ^ padicValNat 2 x ∣ x + y :=
    Nat.dvd_add hxDvd hyDvd
  have hLower :
      padicValNat 2 x ≤ padicValNat 2 (x + y) :=
    (padicValNat_dvd_iff_le hSum0).1 hSumDvd
  apply Nat.le_antisymm ?_ hLower
  by_contra hNot
  have hStrict :
      padicValNat 2 x < padicValNat 2 (x + y) := by
    omega
  have hSuccSum :
      2 ^ (padicValNat 2 x + 1) ∣ x + y :=
    (padicValNat_dvd_iff_le hSum0).2 (by omega)
  have hSuccY :
      2 ^ (padicValNat 2 x + 1) ∣ y :=
    (padicValNat_dvd_iff_le hy).2 (by omega)
  have hSuccX :
      2 ^ (padicValNat 2 x + 1) ∣ x :=
    (Nat.dvd_add_iff_left hSuccY).2 hSuccSum
  exact (pow_succ_padicValNat_not_dvd hx) hSuccX

/-- 右項の valuation が小さい場合の対称版。 -/
private theorem padicValNat_add_eq_right_of_lt
    {x y : ℕ}
    (hx : x ≠ 0)
    (hy : y ≠ 0)
    (hyx : padicValNat 2 y < padicValNat 2 x) :
    padicValNat 2 (x + y) = padicValNat 2 y := by
  simpa [Nat.add_comm] using
    (padicValNat_add_eq_left_of_lt
      (x := y) (y := x) hy hx hyx)

/-- `3^k` は奇数。 -/
private theorem odd_threePow (k : ℕ) : Odd (3 ^ k) := by
  rcases Arithmetic.SignedTwoThreeUnit.threePow_eq_two_mul_add_one k with
    ⟨q, hq⟩
  exact ⟨q, hq⟩

/--
even regular split (`r=1`) の exact second cut。

補正項

`C = (3^k-1) + 2^a 3^k`

の二項はそれぞれ valuation `v₂(k)+2` と `a` を持つ。したがって両者が異なる枝では
`v₂(C)=min(a,v₂(k)+2)`。等しい場合だけ higher cancellation が残る。

同時に元の split equation を source-top / target-top の exact identity に展開する。
-/
theorem SplitTwoHoleEquation.regularEven_secondCut
    {k n L a b : ℕ}
    (hk7 : 7 ≤ k)
    (hkEven : k % 2 = 0)
    (hEq : SplitTwoHoleEquation k n 1 L a b) :
    ((2 : ℤ) ^ n * (3 : ℤ) ^ k +
        2 * (2 : ℤ) ^ b =
      2 * (2 : ℤ) ^ L +
        (((3 : ℤ) ^ k - 1) +
          (2 : ℤ) ^ a * (3 : ℤ) ^ k)) ∧
    ((a < 2 + padicValNat 2 k ∧
        padicValNat 2
          ((3 ^ k - 1) + 2 ^ a * 3 ^ k) = a) ∨
      a = 2 + padicValNat 2 k ∨
      (2 + padicValNat 2 k < a ∧
        padicValNat 2
          ((3 ^ k - 1) + 2 ^ a * 3 ^ k) =
            2 + padicValNat 2 k)) := by
  have hk : 0 < k := by omega
  have hkEven' : Even k := (Nat.even_iff).2 hkEven
  have hIdentity :
      (2 : ℤ) ^ n * (3 : ℤ) ^ k +
          2 * (2 : ℤ) ^ b =
        2 * (2 : ℤ) ^ L +
          (((3 : ℤ) ^ k - 1) +
            (2 : ℤ) ^ a * (3 : ℤ) ^ k) := by
    unfold SplitTwoHoleEquation at hEq
    norm_num at hEq
    linear_combination hEq
  refine ⟨hIdentity, ?_⟩
  let X : ℕ := 3 ^ k - 1
  let Y : ℕ := 2 ^ a * 3 ^ k
  have hX0 : X ≠ 0 := by
    dsimp [X]
    have hThree : 1 < 3 ^ k :=
      one_lt_pow₀ (by norm_num : (1 : ℕ) < 3) (Nat.ne_of_gt hk)
    omega
  have hY0 : Y ≠ 0 := by
    dsimp [Y]
    positivity
  have hXVal : padicValNat 2 X = 2 + padicValNat 2 k := by
    dsimp [X]
    exact padicValNat_threePow_sub_one hk hkEven'
  have hYVal : padicValNat 2 Y = a := by
    dsimp [Y]
    exact padicValNat_twoPow_mul_odd a (3 ^ k) (odd_threePow k)
  rcases lt_trichotomy a (2 + padicValNat 2 k) with hlt | heq | hgt
  · left
    refine ⟨hlt, ?_⟩
    have hVal :=
      padicValNat_add_eq_right_of_lt hX0 hY0 (by
        rw [hXVal, hYVal]
        exact hlt)
    calc
      padicValNat 2 ((3 ^ k - 1) + 2 ^ a * 3 ^ k) =
          padicValNat 2 Y := by
            change padicValNat 2 (X + Y) = padicValNat 2 Y
            exact hVal
      _ = a := hYVal
  · exact Or.inr (Or.inl heq)
  · right
    right
    refine ⟨hgt, ?_⟩
    have hVal :=
      padicValNat_add_eq_left_of_lt hX0 hY0 (by
        rw [hXVal, hYVal]
        exact hgt)
    calc
      padicValNat 2 ((3 ^ k - 1) + 2 ^ a * 3 ^ k) =
          padicValNat 2 X := by
            change padicValNat 2 (X + Y) = padicValNat 2 X
            exact hVal
      _ = 2 + padicValNat 2 k := hXVal

/--
odd regular split (`r=2`) の exact second cut。

`k` odd なら `k-1` は正の even 数で、

`C = 3(3^(k-1)-1) + 2^a 3^k`

の二項の valuation は `v₂(k-1)+2` と `a`。even branch と同じ三分岐になる。
-/
theorem SplitTwoHoleEquation.regularOdd_secondCut
    {k n L a b : ℕ}
    (hk7 : 7 ≤ k)
    (hkOdd : k % 2 = 1)
    (hEq : SplitTwoHoleEquation k n 2 L a b) :
    ((2 : ℤ) ^ n * (3 : ℤ) ^ k +
        4 * (2 : ℤ) ^ b =
      4 * (2 : ℤ) ^ L +
        (3 * ((3 : ℤ) ^ (k - 1) - 1) +
          (2 : ℤ) ^ a * (3 : ℤ) ^ k)) ∧
    ((a < 2 + padicValNat 2 (k - 1) ∧
        padicValNat 2
          (3 * (3 ^ (k - 1) - 1) + 2 ^ a * 3 ^ k) = a) ∨
      a = 2 + padicValNat 2 (k - 1) ∨
      (2 + padicValNat 2 (k - 1) < a ∧
        padicValNat 2
          (3 * (3 ^ (k - 1) - 1) + 2 ^ a * 3 ^ k) =
            2 + padicValNat 2 (k - 1))) := by
  have hk : 0 < k := by omega
  have hkm1 : 0 < k - 1 := by omega
  have hkm1Even : Even (k - 1) := by
    refine ⟨k / 2, ?_⟩
    have hDecomp := Nat.mod_add_div k 2
    rw [hkOdd] at hDecomp
    omega
  have hThreeK :
      (3 : ℤ) ^ k = 3 * (3 : ℤ) ^ (k - 1) := by
    rw [show k = (k - 1) + 1 by omega, pow_succ]
    ring_nf
    simp
  have hIdentity :
      (2 : ℤ) ^ n * (3 : ℤ) ^ k +
          4 * (2 : ℤ) ^ b =
        4 * (2 : ℤ) ^ L +
          (3 * ((3 : ℤ) ^ (k - 1) - 1) +
            (2 : ℤ) ^ a * (3 : ℤ) ^ k) := by
    unfold SplitTwoHoleEquation at hEq
    norm_num at hEq
    rw [hThreeK] at hEq ⊢
    linear_combination hEq
  refine ⟨hIdentity, ?_⟩
  let X : ℕ := 3 * (3 ^ (k - 1) - 1)
  let Y : ℕ := 2 ^ a * 3 ^ k
  have hBase0 : 3 ^ (k - 1) - 1 ≠ 0 := by
    have hThree : 1 < 3 ^ (k - 1) :=
      one_lt_pow₀ (by norm_num : (1 : ℕ) < 3) (Nat.ne_of_gt hkm1)
    omega
  have hX0 : X ≠ 0 := by
    dsimp [X]
    positivity
  have hY0 : Y ≠ 0 := by
    dsimp [Y]
    positivity
  have hBaseVal :
      padicValNat 2 (3 ^ (k - 1) - 1) =
        2 + padicValNat 2 (k - 1) :=
    padicValNat_threePow_sub_one hkm1 hkm1Even
  have hXVal :
      padicValNat 2 X = 2 + padicValNat 2 (k - 1) := by
    dsimp [X]
    rw [padicValNat.mul (by norm_num : (3 : ℕ) ≠ 0) hBase0]
    rw [padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ (3 : ℕ))]
    rw [hBaseVal]
    omega
  have hYVal : padicValNat 2 Y = a := by
    dsimp [Y]
    exact padicValNat_twoPow_mul_odd a (3 ^ k) (odd_threePow k)
  rcases lt_trichotomy a (2 + padicValNat 2 (k - 1)) with hlt | heq | hgt
  · left
    refine ⟨hlt, ?_⟩
    have hVal :=
      padicValNat_add_eq_right_of_lt hX0 hY0 (by
        rw [hXVal, hYVal]
        exact hlt)
    calc
      padicValNat 2
          (3 * (3 ^ (k - 1) - 1) + 2 ^ a * 3 ^ k) =
          padicValNat 2 Y := by
            change padicValNat 2 (X + Y) = padicValNat 2 Y
            exact hVal
      _ = a := hYVal
  · exact Or.inr (Or.inl heq)
  · right
    right
    refine ⟨hgt, ?_⟩
    have hVal :=
      padicValNat_add_eq_left_of_lt hX0 hY0 (by
        rw [hXVal, hYVal]
        exact hgt)
    calc
      padicValNat 2
          (3 * (3 ^ (k - 1) - 1) + 2 ^ a * 3 ^ k) =
          padicValNat 2 X := by
            change padicValNat 2 (X + Y) = padicValNat 2 X
            exact hVal
      _ = 2 + padicValNat 2 (k - 1) := hXVal

/-! ## target `n=1`: period-break ≤ 6 -/

end Mersenne

namespace Binary

/-- period 1 の break を先頭から一段展開する。 -/
private theorem periodBreakCount_one_cons_cons
    (b c : Bool) (bits : List Bool) :
    periodBreakCount 1 (b :: c :: bits) =
      (if b = c then 0 else 1) + periodBreakCount 1 (c :: bits) := by
  simp [periodBreakCount, mismatchCount]

/--
先頭が zero のときに1だけ境界 charge を足すと、period-1 break は
zero の総数の2倍以下になる。
-/
private def frontZeroCharge : List Bool → ℕ
  | false :: _ => 1
  | _ => 0

private theorem periodBreakCount_one_add_frontZero_le
    (bits : List Bool) :
    periodBreakCount 1 bits + frontZeroCharge bits ≤
      2 * zeroCount bits := by
  induction bits with
  | nil => simp [periodBreakCount, frontZeroCharge]
  | cons b bs ih =>
      cases bs with
      | nil =>
          cases b <;> simp [periodBreakCount, frontZeroCharge, zeroCount]
      | cons c cs =>
          cases b <;> cases c <;>
            simp [periodBreakCount_one_cons_cons, frontZeroCharge, zeroCount] at ih ⊢ <;>
            omega

/-- zero が `z` 個なら period 1 break は高々 `2z`。 -/
theorem periodBreakCount_one_le_two_mul_zeroCount
    (bits : List Bool) :
    periodBreakCount 1 bits ≤ 2 * zeroCount bits := by
  have h := periodBreakCount_one_add_frontZero_le bits
  omega

/-- false の正 run の後に true word が続くと境界 break は1だけ増える。 -/
private theorem periodBreakCount_one_falseRun_true
    (m : ℕ) (tail : List Bool) :
    periodBreakCount 1
        (List.replicate (m + 1) false ++ true :: tail) =
      periodBreakCount 1 (true :: tail) + 1 := by
  induction m with
  | zero =>
      simp [periodBreakCount_one_cons_cons,Nat.add_comm]
  | succ m ih =>
      rw [List.replicate_succ, List.replicate_succ]
      simp only [List.cons_append]
      rw [periodBreakCount_one_cons_cons]
      simp only [↓reduceIte, zero_add]
      exact ih

/--
`1`, zero-run, `1` という prefix を付けても period-1 break は高々2増える。
-/
theorem periodBreakCount_one_prefix_gap_le
    (m : ℕ) (tail : List Bool) :
    periodBreakCount 1
        (true :: (List.replicate m false ++ true :: tail)) ≤
      periodBreakCount 1 (true :: tail) + 2 := by
  cases m with
  | zero =>
      simp [periodBreakCount_one_cons_cons]
  | succ m =>
      have hRun := periodBreakCount_one_falseRun_true m tail
      have hRun' :
          periodBreakCount 1
              (false :: (List.replicate m false ++ true :: tail)) =
            periodBreakCount 1 (true :: tail) + 1 := by
        simpa [List.replicate_succ] using hRun
      rw [List.replicate_succ]
      simp only [List.cons_append]
      rw [periodBreakCount_one_cons_cons]
      simp only [Bool.true_eq_false, ↓reduceIte, ge_iff_le]
      rw [hRun']
      omega

/-- replicate の最後に同じ bit を一つ取り出す。 -/
private theorem replicate_succ_eq_append
    (b : Bool) (m : ℕ) :
    List.replicate (m + 1) b = List.replicate m b ++ [b] := by
  induction m with
  | zero => simp
  | succ m ih =>
      calc
        List.replicate (Nat.succ m + 1) b =
            b :: List.replicate (m + 1) b := by
              rw [show Nat.succ m + 1 = (m + 1) + 1 by omega,
                  List.replicate_succ]
        _ = b :: (List.replicate m b ++ [b]) := by rw [ih]
        _ = (b :: List.replicate m b) ++ [b] := by rfl
        _ = List.replicate (Nat.succ m) b ++ [b] := by
              rw [List.replicate_succ]

/-- complement は append と可換。 -/
private theorem complementBits_append
    (u v : List Bool) :
    complementBits (u ++ v) = complementBits u ++ complementBits v := by
  induction u with
  | nil => simp
  | cons b u ih => simp [complementBits, ih]

@[simp] private theorem complementBits_replicate_false
    (m : ℕ) :
    complementBits (List.replicate m false) = List.replicate m true := by
  induction m with
  | zero => simp
  | succ m ih => simp [List.replicate_succ, ih]

@[simp] private theorem complementBits_replicate_true
    (m : ℕ) :
    complementBits (List.replicate m true) = List.replicate m false := by
  induction m with
  | zero => simp
  | succ m ih => simp [List.replicate_succ, ih]

/-- complement の zero-count は元の one-count。 -/
private theorem zeroCount_complementBits
    (bits : List Bool) :
    zeroCount (complementBits bits) = oneCount bits := by
  induction bits with
  | nil => simp [complementBits, oneCount]
  | cons b bs ih =>
      cases b <;> simp [complementBits, Nat.add_comm, oneCount, ih]

/-- one-count は append に関して加法的。 -/
private theorem oneCount_append
    (u v : List Bool) :
    oneCount (u ++ v) = oneCount u + oneCount v := by
  induction u with
  | nil => simp
  | cons b u ih =>
      cases b <;> simp [oneCount, ih, Nat.add_comm, Nat.add_left_comm]

@[simp] private theorem oneCount_replicate_false
    (m : ℕ) : oneCount (List.replicate m false) = 0 := by
  induction m with
  | zero => simp
  | succ m ih => simp [List.replicate_succ, ih]

/-- target 側の二つの欠損位置だけを1にした sparse word。 -/
def targetTwoMissingBits (L a b : ℕ) : List Bool :=
  List.replicate a false ++ [true] ++
    List.replicate (b - a - 1) false ++ [true] ++
      List.replicate (L - b - 1) false

/-- Mersenne all-ones word から上の二点を反転した target word。 -/
def targetTwoCanonicalBits (L a b : ℕ) : List Bool :=
  complementBits (targetTwoMissingBits L a b)

/-- sparse missing word の長さ。 -/
theorem targetTwoMissingBits_length
    {L a b : ℕ}
    (hab : a < b)
    (hbDeep : b + 1 < L) :
    (targetTwoMissingBits L a b).length = L := by
  simp [targetTwoMissingBits]
  omega

/-- sparse missing word の値は `2^a+2^b`。 -/
theorem targetTwoMissingBits_value
    {L a b : ℕ}
    (hab : a < b) :
    valueLSB (targetTwoMissingBits L a b) = 2 ^ a + 2 ^ b := by
  have hExp : a + 1 + (b - a - 1) = b := by omega
  have hPow : 2 ^ a * 2 ^ (b - a - 1) * 2 = 2 ^ b := by
    rw [← pow_add, ← pow_succ]
    congr 1
    omega
  unfold targetTwoMissingBits
  simp [valueLSB_append, valueLSB_replicate_false]
  ring_nf
  rw [hPow]

/-- sparse missing word には1がちょうど二つ。 -/
private theorem targetTwoMissingBits_oneCount
    {L a b : ℕ} :
    oneCount (targetTwoMissingBits L a b) = 2 := by
  simp [targetTwoMissingBits, oneCount_append, oneCount]

/-- target word は明示的に「all ones から二点だけ zero」の形。 -/
private theorem targetTwoCanonicalBits_eq_runs
    {L a b : ℕ} :
    targetTwoCanonicalBits L a b =
      List.replicate a true ++ [false] ++
        List.replicate (b - a - 1) true ++ [false] ++
          List.replicate (L - b - 1) true := by
  unfold targetTwoCanonicalBits targetTwoMissingBits
  simp [complementBits_append]

/-- target word の zero はちょうど二つ。 -/
theorem targetTwoCanonicalBits_zeroCount
    {L a b : ℕ} :
    zeroCount (targetTwoCanonicalBits L a b) = 2 := by
  unfold targetTwoCanonicalBits
  rw [zeroCount_complementBits]
  exact targetTwoMissingBits_oneCount

/-- target word の長さは `L`。 -/
private theorem targetTwoCanonicalBits_length
    {L a b : ℕ}
    (hab : a < b)
    (hbDeep : b + 1 < L) :
    (targetTwoCanonicalBits L a b).length = L := by
  unfold targetTwoCanonicalBits
  rw [complementBits_length]
  exact targetTwoMissingBits_length hab hbDeep

/-- target word の値は `2^L-1-2^a-2^b`。 -/
theorem targetTwoCanonicalBits_value
    {L a b : ℕ}
    (hab : a < b)
    (hbDeep : b + 1 < L) :
    valueLSB (targetTwoCanonicalBits L a b) =
      2 ^ L - 1 - 2 ^ a - 2 ^ b := by
  have hComp :=
    valueLSB_add_complementBits_add_one (targetTwoMissingBits L a b)
  have hLen := targetTwoMissingBits_length hab hbDeep
  have hVal := targetTwoMissingBits_value hab (L:=L)
  rw [hLen, hVal] at hComp
  unfold targetTwoCanonicalBits
  omega

/-- `a>0` なので target canonical word は true から始まる。 -/
theorem targetTwoCanonicalBits_starts_true
    {L a b : ℕ}
    (ha0 : 0 < a) :
    ∃ tail : List Bool,
      targetTwoCanonicalBits L a b = true :: tail := by
  obtain ⟨m, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha0)
  rw [targetTwoCanonicalBits_eq_runs]
  simp [List.replicate_succ]

/-- `b+1<L` なので target canonical word は true で終わる。 -/
private theorem targetTwoCanonicalBits_ends_true
    {L a b : ℕ}
    (hbDeep : b + 1 < L) :
    ∃ head : List Bool,
      targetTwoCanonicalBits L a b = head ++ [true] := by
  have hd : 0 < L - b - 1 := by omega
  obtain ⟨m, hm⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
  rw [targetTwoCanonicalBits_eq_runs, hm,
      replicate_succ_eq_append]
  refine ⟨
    List.replicate a true ++ [false] ++
      List.replicate (b - a - 1) true ++ [false] ++
        List.replicate m true,
    ?_⟩
  simp [List.append_assoc]

/-- LSB の1と exit zero-run を target word の前に付けた `3^k` 候補語。 -/
def targetTwoSourceOneBits
    (r L a b : ℕ) : List Bool :=
  true :: (List.replicate (r - 1) false ++
    targetTwoCanonicalBits L a b)

/-- prefix gap の値は `1+2^r*tail`。 -/
theorem valueLSB_targetTwoSourceOneBits
    {r L a b : ℕ}
    (hr : 0 < r) :
    valueLSB (targetTwoSourceOneBits r L a b) =
      1 + 2 ^ r * valueLSB (targetTwoCanonicalBits L a b) := by
  unfold targetTwoSourceOneBits
  simp only [valueLSB, bitValue_true, valueLSB_append, valueLSB_replicate_false,
   List.length_replicate, zero_add,Nat.add_left_cancel_iff]
  have hPow : 2 * 2 ^ (r - 1) = 2 ^ r := by
    rw [show r = (r - 1) + 1 by omega, pow_succ]
    ring_nf
    simp
  rw [← mul_assoc, hPow]

/-- source-one candidate word の長さ。 -/
theorem targetTwoSourceOneBits_length
    {r L a b : ℕ}
    (hr : 0 < r)
    (hab : a < b)
    (hbDeep : b + 1 < L) :
    (targetTwoSourceOneBits r L a b).length = r + L := by
  unfold targetTwoSourceOneBits
  simp [targetTwoCanonicalBits_length hab hbDeep]
  omega

/-- source-one candidate word も true で終わる。 -/
theorem targetTwoSourceOneBits_ends_true
    {r L a b : ℕ}
    (hbDeep : b + 1 < L) :
    ∃ head : List Bool,
      targetTwoSourceOneBits r L a b = head ++ [true] := by
  rcases targetTwoCanonicalBits_ends_true
      (L := L) (a := a) (b := b) hbDeep with ⟨u, hu⟩
  refine ⟨true :: (List.replicate (r - 1) false ++ u), ?_⟩
  unfold targetTwoSourceOneBits
  rw [hu]
  simp [List.append_assoc]

end Binary

namespace Mersenne

/--
interior target-two `n=1` は period 1 の break 数が高々6。

二つの target hole は target factor 内で高々4 break を作るだけで、
LSB の1と exit zero-run を付ける操作が増やす break は高々2である。
-/
theorem TargetTwoHoleEquation.source_one_periodBreakAtMostSix
    {k r L a b : ℕ}
    (hr : 0 < r)
    (ha0 : 0 < a)
    (hab : a < b)
    (hbDeep : b + 1 < L)
    (hEq : TargetTwoHoleEquation k 1 r L a b) :
    Binary.HasPeriodBreakAtMost (3 ^ k) 1 6 := by
  let targetBits : List Bool :=
    Binary.targetTwoCanonicalBits L a b
  let bits : List Bool :=
    Binary.targetTwoSourceOneBits r L a b
  have hTargetSum :
      Binary.valueLSB targetBits + 1 + 2 ^ a + 2 ^ b = 2 ^ L := by
    have hMissing :=
      Binary.valueLSB_add_complementBits_add_one
        (Binary.targetTwoMissingBits L a b)
    have hLen := Binary.targetTwoMissingBits_length hab hbDeep
    have hVal := Binary.targetTwoMissingBits_value hab (L:=L)
    rw [hLen, hVal] at hMissing
    dsimp [targetBits, Binary.targetTwoCanonicalBits]
    omega
  have hTargetInt :
      (2 : ℤ) ^ L - 1 - (2 : ℤ) ^ a - (2 : ℤ) ^ b =
        (Binary.valueLSB targetBits : ℤ) := by
    have hCast :
        (Binary.valueLSB targetBits : ℤ) + 1 +
            (2 : ℤ) ^ a + (2 : ℤ) ^ b =
          (2 : ℤ) ^ L := by
      exact_mod_cast hTargetSum
    linarith
  have hEqInt := hEq
  unfold TargetTwoHoleEquation at hEqInt
  norm_num at hEqInt
  rw [hTargetInt] at hEqInt
  have hNat :
      3 ^ k = 2 ^ r * Binary.valueLSB targetBits + 1 := by
    exact_mod_cast hEqInt
  have hBitsVal : Binary.valueLSB bits = 3 ^ k := by
    dsimp [bits]
    rw [Binary.valueLSB_targetTwoSourceOneBits hr]
    dsimp [targetBits] at hNat ⊢
    omega
  have hTargetZero : Binary.zeroCount targetBits = 2 := by
    dsimp [targetBits]
    exact Binary.targetTwoCanonicalBits_zeroCount
  have hTargetBreak : Binary.periodBreakCount 1 targetBits ≤ 4 := by
    have h := Binary.periodBreakCount_one_le_two_mul_zeroCount targetBits
    rw [hTargetZero] at h
    omega
  rcases Binary.targetTwoCanonicalBits_starts_true
      (L := L) (b := b) ha0 with ⟨tail, hStart⟩
  have hBreak : Binary.periodBreakCount 1 bits ≤ 6 := by
    dsimp [bits, Binary.targetTwoSourceOneBits]
    rw [hStart]
    have hPrefix :=
      Binary.periodBreakCount_one_prefix_gap_le (r - 1) tail
    have hTargetBreak' :
        Binary.periodBreakCount 1 (true :: tail) ≤ 4 := by
      dsimp [targetBits] at hTargetBreak
      rw [hStart] at hTargetBreak
      exact hTargetBreak
    omega
  have hEnd :=
    Binary.targetTwoSourceOneBits_ends_true
      (r := r) (L := L) (a := a) (b := b) hbDeep
  have hBitLength : Binary.HasBitLength (3 ^ k) bits.length := by
    rcases hEnd with ⟨u, hu⟩
    have hCanonical := Binary.hasBitLength_valueLSB_append_true u
    rw [← hu] at hCanonical
    have hCanonical' :
        Binary.HasBitLength (Binary.valueLSB bits) bits.length := by
      simpa [bits] using hCanonical
    rw [hBitsVal] at hCanonical'
    exact hCanonical'
  refine ⟨bits, bits.length, ?_, hBitLength, hBreak⟩
  exact ⟨rfl, hBitsVal⟩

end Mersenne
end Collatz3
