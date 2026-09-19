import CollatzLean.Collatz3.Mersenne.TargetOneHoleGeometric
import CollatzLean.Collatz3.Mersenne.SmallHoleExitDepth
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

import Mathlib.Tactic.Positivity

/-!
# Collatz3 Mersenne: target-two-hole の Mersenne phase rigidity

`TargetTwoHoleEquation`

`3^k (2^n-1) = 2^r (2^L-1-2^a-2^b) + 1`

を `2^n-1` で見る。`n>=4`, `r in {1,2}` では residue equation

`2^A + 1 = 2^r + 2^B + 2^C  (mod 2^n-1)`

が二種類の phase しか許さない。

* wrapped phase:
  `L = 0`, `a+r+1 = 0`, `b+r+1 = 0` modulo `n`。
* split phase:
  `L = 1` modulo `n` で、二つの hole phase は `{0,r}`。

`n=1,2,3` は後段で finite exceptional branch として扱う。
-/

namespace Collatz3
namespace Mersenne

/-- positive exponent の 2 冪は `2*z` の形。 -/
private theorem twoPow_eq_two_mul_of_pos
    {e : ℕ}
    (he : 0 < e) :
    ∃ z : ℕ, 2 ^ e = 2 * z := by
  obtain ⟨d, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt he)
  refine ⟨2 ^ d, ?_⟩
  rw [pow_succ]
  ring

/-- 二つの 2 冪の和が一つの 2 冪なら、二指数は等しい。 -/
private theorem twoPow_add_twoPow_eq_twoPow
    {a b c : ℕ}
    (h : 2 ^ a + 2 ^ b = 2 ^ c) :
    a = b ∧ c = a + 1 := by
  have core :
      ∀ {a b c : ℕ},
        a ≤ b →
        2 ^ a + 2 ^ b = 2 ^ c →
        a = b ∧ c = a + 1 := by
    intro a b c hab hEq
    rcases eq_or_lt_of_le hab with hAB | hAB
    · subst b
      constructor
      · rfl
      · apply Nat.pow_right_injective
          (by norm_num : 2 ≤ (2 : ℕ))
        calc
          2 ^ c = 2 ^ a + 2 ^ a := hEq.symm
          _ = 2 ^ (a + 1) := by
            rw [pow_succ]
            ring
    · exfalso
      have hPowLt : 2 ^ a < 2 ^ b :=
        (Nat.pow_lt_pow_iff_right
          (by norm_num : 1 < (2 : ℕ))).2 hAB
      have hPowAPos : 0 < 2 ^ a :=
        Nat.pow_pos (by norm_num)
      have hLower : 2 ^ b < 2 ^ c := by
        rw [← hEq]
        exact Nat.lt_add_of_pos_left hPowAPos
      have hUpper : 2 ^ c < 2 ^ (b + 1) := by
        rw [← hEq, pow_succ]
        have hAdd :
            2 ^ a + 2 ^ b <
              2 ^ b + 2 ^ b :=
          Nat.add_lt_add_right hPowLt (2 ^ b)
        simpa [mul_two] using hAdd
      have hbc : b < c :=
        (Nat.pow_lt_pow_iff_right
          (by norm_num : 1 < (2 : ℕ))).1 hLower
      have hcb : c < b + 1 :=
        (Nat.pow_lt_pow_iff_right
          (by norm_num : 1 < (2 : ℕ))).1 hUpper
      omega
  rcases le_total a b with hab | hba
  · exact core hab h
  · have h' : 2 ^ b + 2 ^ a = 2 ^ c := by
      simpa [Nat.add_comm] using h
    rcases core hba h' with ⟨hBA, hc⟩
    constructor
    · exact hBA.symm
    · omega

/-- modulus をまたがない residue equality は split phase だけを許す。 -/
private theorem targetTwo_exact_phase_unique
    {r A B C : ℕ}
    (hr : r = 1 ∨ r = 2)
    (hEq : 2 ^ A + 1 = 2 ^ r + 2 ^ B + 2 ^ C) :
    A = r + 1 ∧
      ((B = 0 ∧ C = r) ∨ (B = r ∧ C = 0)) := by
  have hrPos : 0 < r := by
    rcases hr with rfl | rfl <;> omega
  have hApos : 0 < A := by
    by_contra hNot
    have hA0 : A = 0 := by
      omega
    rw [hA0] at hEq
    norm_num at hEq
    have hR2 : 2 ≤ 2 ^ r := by
      calc
        2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ r :=
          Nat.pow_le_pow_right
            (by norm_num : 0 < (2 : ℕ))
            (by omega)
    have hBPosPow : 0 < 2 ^ B := by
      exact Nat.pow_pos (by norm_num)
    have hCPosPow : 0 < 2 ^ C := by
      exact Nat.pow_pos (by norm_num)
    have hB1 : 1 ≤ 2 ^ B := by
      omega
    have hC1 : 1 ≤ 2 ^ C := by
      omega
    omega
  by_cases hB0 : B = 0
  · by_cases hC0 : C = 0
    · rcases twoPow_eq_two_mul_of_pos hApos with ⟨x, hx⟩
      rcases twoPow_eq_two_mul_of_pos hrPos with ⟨y, hy⟩
      rw [hB0, hC0] at hEq
      norm_num at hEq
      rw [hx, hy] at hEq
      omega
    · have hCpos : 0 < C := Nat.pos_of_ne_zero hC0
      rw [hB0] at hEq
      norm_num at hEq
      have hSum : 2 ^ r + 2 ^ C = 2 ^ A := by omega
      rcases twoPow_add_twoPow_eq_twoPow hSum with ⟨hrC, hA⟩
      exact ⟨by omega, Or.inl ⟨hB0, by omega⟩⟩
  · by_cases hC0 : C = 0
    · have hBpos : 0 < B := Nat.pos_of_ne_zero hB0
      rw [hC0] at hEq
      norm_num at hEq
      have hSum : 2 ^ r + 2 ^ B = 2 ^ A := by omega
      rcases twoPow_add_twoPow_eq_twoPow hSum with ⟨hrB, hA⟩
      exact ⟨by omega, Or.inr ⟨by omega, hC0⟩⟩
    · have hBpos : 0 < B := Nat.pos_of_ne_zero hB0
      have hCpos : 0 < C := Nat.pos_of_ne_zero hC0
      rcases twoPow_eq_two_mul_of_pos hApos with ⟨xA, hxA⟩
      rcases twoPow_eq_two_mul_of_pos hrPos with ⟨xR, hxR⟩
      rcases twoPow_eq_two_mul_of_pos hBpos with ⟨xB, hxB⟩
      rcases twoPow_eq_two_mul_of_pos hCpos with ⟨xC, hxC⟩
      rw [hxA, hxR, hxB, hxC] at hEq
      omega

/-- modulus を一度またぐ residue equality は wrapped phase だけを許す。 -/
private theorem targetTwo_wrapped_phase_unique
    {n r A B C : ℕ}
    (hn4 : 4 ≤ n)
    (hr : r = 1 ∨ r = 2)
    (hB : B < n)
    (hC : C < n)
    (hEq : 2 ^ r + 2 ^ B + 2 ^ C = 2 ^ n + 2 ^ A) :
    A = r ∧ B = n - 1 ∧ C = n - 1 := by
  have hrLe : r ≤ 2 := by
    rcases hr with rfl | rfl <;> omega
  have hrPred : r ≤ n - 2 := by omega
  have hBPred : B ≤ n - 1 := by omega
  have hCPred : C ≤ n - 1 := by omega
  let X : ℕ := 2 ^ (n - 2)
  have hXPos : 0 < X := by
    dsimp [X]
    positivity
  have hPowPred : 2 ^ (n - 1) = 2 * X := by
    dsimp [X]
    rw [show n - 1 = (n - 2) + 1 by omega, pow_succ]
    ring
  have hPowN : 2 ^ n = 4 * X := by
    dsimp [X]
    rw [show n = (n - 2) + 2 by omega, pow_add]
    norm_num
    ring
  have hAtLeast : B = n - 1 ∨ C = n - 1 := by
    by_contra hNot
    have hBne : B ≠ n - 1 := by
      intro h
      exact hNot (Or.inl h)
    have hCne : C ≠ n - 1 := by
      intro h
      exact hNot (Or.inr h)
    have hBsmall : B ≤ n - 2 := by omega
    have hCsmall : C ≤ n - 2 := by omega
    have hRpow : 2 ^ r ≤ X := by
      dsimp [X]
      exact Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hrPred
    have hBpow : 2 ^ B ≤ X := by
      dsimp [X]
      exact Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hBsmall
    have hCpow : 2 ^ C ≤ X := by
      dsimp [X]
      exact Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hCsmall
    rw [hPowN] at hEq
    have hApow : 0 < 2 ^ A := by positivity
    omega
  have hBtop : B = n - 1 := by
    rcases hAtLeast with hBtop | hCtop
    · exact hBtop
    · by_contra hBne
      have hBsmall : B ≤ n - 2 := by omega
      have hRpow : 2 ^ r ≤ X := by
        dsimp [X]
        exact Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hrPred
      have hBpow : 2 ^ B ≤ X := by
        dsimp [X]
        exact Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hBsmall
      rw [hCtop, hPowPred, hPowN] at hEq
      have hApow : 0 < 2 ^ A := by positivity
      omega
  have hCtop : C = n - 1 := by
    by_contra hCne
    have hCsmall : C ≤ n - 2 := by omega
    have hRpow : 2 ^ r ≤ X := by
      dsimp [X]
      exact Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hrPred
    have hCpow : 2 ^ C ≤ X := by
      dsimp [X]
      exact Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hCsmall
    rw [hBtop, hPowPred, hPowN] at hEq
    have hApow : 0 < 2 ^ A := by positivity
    omega
  have hPowEq : 2 ^ r = 2 ^ A := by
    rw [hBtop, hCtop, hPowPred, hPowN] at hEq
    omega
  have hrA : r = A :=
    Nat.pow_right_injective (by norm_num : 2 ≤ (2 : ℕ)) hPowEq
  exact ⟨hrA.symm, hBtop, hCtop⟩

/--
`n>=4` の Mersenne residue equation の完全分類。

右辺が modulus 未満なら split、modulus を一度またげば wrapped になる。
-/
private theorem targetTwo_mersenne_residue_unique
    {n r A B C : ℕ}
    (hn4 : 4 ≤ n)
    (hr : r = 1 ∨ r = 2)
    (hA : A < n)
    (hB : B < n)
    (hC : C < n)
    (hEq :
      (2 : ZMod (2 ^ n - 1)) ^ A + 1 =
        (2 : ZMod (2 ^ n - 1)) ^ r +
          (2 : ZMod (2 ^ n - 1)) ^ B +
          (2 : ZMod (2 ^ n - 1)) ^ C) :
    (A = r ∧ B = n - 1 ∧ C = n - 1) ∨
      (A = r + 1 ∧
        ((B = 0 ∧ C = r) ∨ (B = r ∧ C = 0))) := by
  let M : ℕ := 2 ^ n - 1
  let X : ℕ := 2 ^ (n - 2)
  have hXPos : 0 < X := by
    dsimp [X]
    positivity
  have hXTwo : 2 ≤ X := by
    dsimp [X]
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n - 2) :=
        Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) (by omega)
  have hPowPred : 2 ^ (n - 1) = 2 * X := by
    dsimp [X]
    rw [show n - 1 = (n - 2) + 1 by omega, pow_succ]
    ring
  have hPowN : 2 ^ n = 4 * X := by
    dsimp [X]
    rw [show n = (n - 2) + 2 by omega, pow_add]
    norm_num
    ring
  have hM : M = 4 * X - 1 := by
    dsimp [M]
    rw [hPowN]
  have hMPos : 0 < M := by
    rw [hM]
    omega
  have hrLe : r ≤ 2 := by
    rcases hr with rfl | rfl <;> omega
  have hrPred : r ≤ n - 2 := by omega
  have hApred : A ≤ n - 1 := by omega
  have hBpred : B ≤ n - 1 := by omega
  have hCpred : C ≤ n - 1 := by omega
  have hApow : 2 ^ A ≤ 2 * X := by
    rw [← hPowPred]
    exact Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hApred
  have hBpow : 2 ^ B ≤ 2 * X := by
    rw [← hPowPred]
    exact Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hBpred
  have hCpow : 2 ^ C ≤ 2 * X := by
    rw [← hPowPred]
    exact Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hCpred
  have hRpow : 2 ^ r ≤ X := by
    dsimp [X]
    exact Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hrPred
  have hLeftLt : 2 ^ A + 1 < M := by
    rw [hM]
    omega
  have hRightLtTwo :
      2 ^ r + 2 ^ B + 2 ^ C < 2 * M := by
    rw [hM]
    omega
  have hCong :
      2 ^ A + 1 ≡ 2 ^ r + 2 ^ B + 2 ^ C [MOD M] := by
    simpa [M, ← ZMod.natCast_eq_natCast_iff] using hEq
  change
      (2 ^ A + 1) % M =
        (2 ^ r + 2 ^ B + 2 ^ C) % M at hCong
  rw [Nat.mod_eq_of_lt hLeftLt] at hCong
  by_cases hRightLt : 2 ^ r + 2 ^ B + 2 ^ C < M
  · rw [Nat.mod_eq_of_lt hRightLt] at hCong
    exact Or.inr (targetTwo_exact_phase_unique hr hCong)
  · have hMle : M ≤ 2 ^ r + 2 ^ B + 2 ^ C := by omega
    rw [Nat.mod_eq_sub_mod hMle] at hCong
    have hSubLt :
        2 ^ r + 2 ^ B + 2 ^ C - M < M := by
      omega
    rw [Nat.mod_eq_of_lt hSubLt] at hCong
    have hWrapEq :
        2 ^ r + 2 ^ B + 2 ^ C = 2 ^ n + 2 ^ A := by
      dsimp [M] at hCong
      omega
    exact Or.inl
      (targetTwo_wrapped_phase_unique hn4 hr hB hC hWrapEq)

/--
`n>=4`, `r=1 or 2` の target-two-hole は三つの divisibility phase に exact に分かれる。

* wrapped:
  `n|L`, `n|(a+r+1)`, `n|(b+r+1)`。
* split-forward:
  `n|(L-1)`, `n|(a+r)`, `n|b`。
* split-reverse:
  `n|(L-1)`, `n|(b+r)`, `n|a`。
-/
theorem TargetTwoHoleEquation.mersenne_phase_dichotomy
    {k n r L a b : ℕ}
    (hn4 : 4 ≤ n)
    (hr : r = 1 ∨ r = 2)
    (ha0 : 0 < a)
    (hab : a < b)
    (hbL : b < L)
    (hEq : TargetTwoHoleEquation k n r L a b) :
    (n ∣ L ∧ n ∣ a + r + 1 ∧ n ∣ b + r + 1) ∨
      (n ∣ L - 1 ∧ n ∣ a + r ∧ n ∣ b) ∨
      (n ∣ L - 1 ∧ n ∣ b + r ∧ n ∣ a) := by
  let M : ℕ := 2 ^ n - 1
  have hPeriod : (2 : ZMod M) ^ n = 1 := by
    simpa [M] using twoPow_period_mersenne n
  have hMod := hEq.to_mod M
  unfold TargetTwoHoleModEquation at hMod
  have hMod0 :
      (0 : ZMod M) =
        (2 : ZMod M) ^ r *
          ((2 : ZMod M) ^ L - 1 -
            (2 : ZMod M) ^ a - (2 : ZMod M) ^ b) + 1 := by
    simpa [hPeriod] using hMod
  have hCore :
      (2 : ZMod M) ^ (L + r) + 1 =
        (2 : ZMod M) ^ r +
          (2 : ZMod M) ^ (a + r) +
          (2 : ZMod M) ^ (b + r) := by
    rw [pow_add, pow_add, pow_add]
    linear_combination -hMod0
  let A : ℕ := (L + r) % n
  let B : ℕ := (a + r) % n
  let C : ℕ := (b + r) % n
  have hAred :=
    pow_eq_pow_mod_of_pow_eq_one
      (2 : ZMod M) (p := n) (e := L + r) hPeriod
  have hBred :=
    pow_eq_pow_mod_of_pow_eq_one
      (2 : ZMod M) (p := n) (e := a + r) hPeriod
  have hCred :=
    pow_eq_pow_mod_of_pow_eq_one
      (2 : ZMod M) (p := n) (e := b + r) hPeriod
  rw [hAred, hBred, hCred] at hCore
  have hnPos : 0 < n := by omega
  have hAlt : A < n := by
    dsimp [A]
    exact Nat.mod_lt _ hnPos
  have hBlt : B < n := by
    dsimp [B]
    exact Nat.mod_lt _ hnPos
  have hClt : C < n := by
    dsimp [C]
    exact Nat.mod_lt _ hnPos
  have hUnique :=
    targetTwo_mersenne_residue_unique hn4 hr hAlt hBlt hClt
      (by simpa [A, B, C, M] using hCore)
  have hrlt : r < n := by
    rcases hr with rfl | rfl <;> omega
  have hr1lt : r + 1 < n := by
    rcases hr with rfl | rfl <;> omega
  rcases hUnique with hWrapped | hSplit
  · rcases hWrapped with ⟨hAeq, hBeq, hCeq⟩
    have hLRMod : L + r ≡ r [MOD n] := by
      change (L + r) % n = r % n
      simpa [A, Nat.mod_eq_of_lt hrlt] using hAeq
    have hLMod : L ≡ 0 [MOD n] := by
      apply Nat.ModEq.add_right_cancel' r
      simpa using hLRMod
    have hARMod : a + r ≡ n - 1 [MOD n] := by
      change (a + r) % n = (n - 1) % n
      have hnPredLt : n - 1 < n := by omega
      simpa [B, Nat.mod_eq_of_lt hnPredLt] using hBeq
    have hBRMod : b + r ≡ n - 1 [MOD n] := by
      change (b + r) % n = (n - 1) % n
      have hnPredLt : n - 1 < n := by omega
      simpa [C, Nat.mod_eq_of_lt hnPredLt] using hCeq
    have hARDvd : n ∣ a + r + 1 := by
      have hPlus := hARMod.add_right 1
      have hToN : a + r + 1 ≡ n [MOD n] := by
        simpa [Nat.add_assoc, Nat.sub_add_cancel (by omega : 1 ≤ n)] using hPlus
      exact Nat.modEq_zero_iff_dvd.mp
        (hToN.trans Nat.modulus_modEq_zero)
    have hBRDvd : n ∣ b + r + 1 := by
      have hPlus := hBRMod.add_right 1
      have hToN : b + r + 1 ≡ n [MOD n] := by
        simpa [Nat.add_assoc, Nat.sub_add_cancel (by omega : 1 ≤ n)] using hPlus
      exact Nat.modEq_zero_iff_dvd.mp
        (hToN.trans Nat.modulus_modEq_zero)
    exact Or.inl ⟨Nat.modEq_zero_iff_dvd.mp hLMod, hARDvd, hBRDvd⟩
  · rcases hSplit with ⟨hAeq, hBC⟩
    have hLRMod : L + r ≡ r + 1 [MOD n] := by
      change (L + r) % n = (r + 1) % n
      simpa [A, Nat.mod_eq_of_lt hr1lt] using hAeq
    have hLMod : L ≡ 1 [MOD n] := by
      apply Nat.ModEq.add_right_cancel' r
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hLRMod
    have hLDvd : n ∣ L - 1 := by
      have hLPos : 1 ≤ L := by omega
      exact (Nat.modEq_iff_dvd' hLPos).mp hLMod.symm
    rcases hBC with hForward | hReverse
    · rcases hForward with ⟨hBeq, hCeq⟩
      have hARDvd : n ∣ a + r := by
        apply Nat.dvd_iff_mod_eq_zero.mpr
        simpa [B] using hBeq
      have hBMod : b + r ≡ r [MOD n] := by
        change (b + r) % n = r % n
        simpa [C, Nat.mod_eq_of_lt hrlt] using hCeq
      have hBZero : b ≡ 0 [MOD n] := by
        apply Nat.ModEq.add_right_cancel' r
        simpa using hBMod
      exact Or.inr (Or.inl ⟨hLDvd, hARDvd, Nat.modEq_zero_iff_dvd.mp hBZero⟩)
    · rcases hReverse with ⟨hBeq, hCeq⟩
      have hBRDvd : n ∣ b + r := by
        apply Nat.dvd_iff_mod_eq_zero.mpr
        simpa [C] using hCeq
      have hAMod : a + r ≡ r [MOD n] := by
        change (a + r) % n = r % n
        simpa [B, Nat.mod_eq_of_lt hrlt] using hBeq
      have hAZero : a ≡ 0 [MOD n] := by
        apply Nat.ModEq.add_right_cancel' r
        simpa using hAMod
      exact Or.inr (Or.inr ⟨hLDvd, hBRDvd, Nat.modEq_zero_iff_dvd.mp hAZero⟩)

end Mersenne
end Collatz3
