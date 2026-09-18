import CollatzLean.Collatz3.Mersenne.NoHoleSourceOneProof
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Collatz3 Mersenne: 最後の no-hole Mersenne quotient residual の排除

`NoHoleProof` と `NoHoleSourceOneProof` の後に残った最後の residual

`3^k (2^n - 1) = 2^(L+1) - 1`

(`k ≥ 4` even, `n ≥ 3`, `L ≥ 3`) を elementary に排除する。

証明の骨格は次の通り。

1. `2` の `mod (2^n-1)` における multiplicative order が exact に `n` と示す。
   これにより `n ∣ L+1`。
2. `L+1 = n*t` と書き、元の equation を geometric sum

   `3^k = 1 + 2^n + 2^(2n) + ... + 2^((t-1)n)`

   にする。
3. `t` が even なら sum を二分割し、`2^(nu)+1` が `3^k` を割る。
   prime-power divisor と mod `3,9` だけで `nu=3`、従って `t=2,n=3,k=2` に落ち、
   `k≥4` と矛盾する。
4. `t` が odd なら `L` の oddness から `n` は even。
   geometric sum を mod 3 で見て `3 ∣ t`。
   `t=3u` と三分割すると

   `2^(2nu) + 2^(nu) + 1`

   が `3^k` を割る。`nu` は even なのでこの因子は `3 mod 9`。
   よって因子は exact に `3` だが、`n≥3,u>0` から明らかに `>3`。矛盾。

Zsigmondy / Baker / Catalan は使用しない。
-/

namespace Collatz3
namespace Mersenne

open Arithmetic
open scoped BigOperators

/-! ## Layer 0: Mersenne modulus と geometric sum の小補題 -/

/--
`ZMod n` 上の自然数 cast の等式を、通常の剰余の等式へ戻す。

小さい剰余値 `3`, `6` などを `ZMod.val` から直接取り出す代わりに使う。
-/
private theorem nat_mod_eq_of_zmod_natCast_eq
    {n a b : ℕ}
    (h : (a : ZMod n) = (b : ZMod n)) :
    a % n = b % n := by
  have hCong : a ≡ b [MOD n] :=
    (ZMod.natCast_eq_natCast_iff a b n).mp h
  exact hCong

/--
`n ≥ 2` なら `2` の `mod (2^n-1)` における multiplicative order は exact に `n`。

`2^n = 1 mod (2^n-1)` は自明であり、`0<m<n` では
`0 < 2^m-1 < 2^n-1` なので同じ合同は起こらない。
-/
private theorem orderOf_two_zmod_mersenne
    (n : ℕ)
    (hn : 2 ≤ n) :
    orderOf (2 : ZMod (2 ^ n - 1)) = n := by
  apply (orderOf_eq_iff (by omega : 0 < n)).2
  constructor
  · have hCong :
        2 ^ n ≡ 1 [MOD 2 ^ n - 1] := by
      have hEq : 2 ^ n = (2 ^ n - 1) + 1 := by
        have hPow : 0 < 2 ^ n := by positivity
        omega
      rw [hEq]
      exact Nat.add_modEq_left
    have hCast :
        ((2 ^ n : ℕ) : ZMod (2 ^ n - 1)) = 1 := by
      simpa using
        ((ZMod.natCast_eq_natCast_iff
          (2 ^ n) 1 (2 ^ n - 1)).2 hCong)
    simpa using hCast
  · intro m hm hmp hPow
    have hCast :
        ((2 ^ m : ℕ) : ZMod (2 ^ n - 1)) = 1 := by
      simpa using hPow
    have hCong :
        2 ^ m ≡ 1 [MOD 2 ^ n - 1] := by
      apply (ZMod.natCast_eq_natCast_iff
        (2 ^ m) 1 (2 ^ n - 1)).1
      simpa using hCast
    have hDvd : 2 ^ n - 1 ∣ 2 ^ m - 1 :=
      hCong.symm.dvd'
    have hPowM : 1 < 2 ^ m :=
      Nat.one_lt_pow (Nat.ne_of_gt hmp) (by norm_num : 1 < (2 : ℕ))
    have hSubPos : 0 < 2 ^ m - 1 := by omega
    have hLe : 2 ^ n - 1 ≤ 2 ^ m - 1 :=
      Nat.le_of_dvd hSubPos hDvd
    have hPowLt : 2 ^ m < 2 ^ n :=
      Nat.pow_lt_pow_of_lt (by norm_num : 1 < (2 : ℕ)) hm
    omega

/--
no-hole quotient residual では `n ∣ L+1`。

元の equation を `mod (2^n-1)` へ送ると `2^(L+1)=1`。
上の exact order を使うだけで exponent divisibility が得られる。
-/
private theorem noHole_mersenne_exponent_dvd
    {k n L : ℕ}
    (hn : 2 ≤ n)
    (hEq : NoHoleEquation k n 1 L) :
    n ∣ L + 1 := by
  let M : ℕ := 2 ^ n - 1
  have hOrder : orderOf (2 : ZMod M) = n := by
    dsimp [M]
    exact orderOf_two_zmod_mersenne n hn
  have hTwoN : (2 : ZMod M) ^ n = 1 := by
    rw [← hOrder]
    exact pow_orderOf_eq_one _
  have hMod := hEq.to_mod M
  unfold NoHoleModEquation at hMod
  rw [hTwoN] at hMod
  norm_num at hMod
  have hTarget : (2 : ZMod M) ^ (L + 1) = 1 := by
    rw [pow_succ]
    linear_combination -hMod
  have hDvd : orderOf (2 : ZMod M) ∣ L + 1 :=
    orderOf_dvd_iff_pow_eq_one.mpr hTarget
  rwa [hOrder] at hDvd

/--
`r=1` の no-hole equation を自然数上の Mersenne equality に読み替える。
-/
private theorem noHole_mersenne_nat_identity
    {k n L : ℕ}
    (hEq : NoHoleEquation k n 1 L) :
    3 ^ k * (2 ^ n - 1) = 2 ^ (L + 1) - 1 := by
  have hnPowPos : 0 < 2 ^ n := by positivity
  have hLPowPos : 0 < 2 ^ (L + 1) := by positivity
  have hnOne : 1 ≤ 2 ^ n := by omega
  have hLOne : 1 ≤ 2 ^ (L + 1) := by omega
  have hCastN :
      (((2 ^ n - 1 : ℕ) : ℤ)) = (2 : ℤ) ^ n - 1 := by
    rw [Nat.cast_sub hnOne]
    norm_num
  have hCastL :
      (((2 ^ (L + 1) - 1 : ℕ) : ℤ)) =
        (2 : ℤ) ^ (L + 1) - 1 := by
    rw [Nat.cast_sub hLOne]
    norm_num
  have hInt :
      (3 : ℤ) ^ k * ((2 : ℤ) ^ n - 1) =
        (2 : ℤ) ^ (L + 1) - 1 := by
    unfold NoHoleEquation at hEq
    rw [pow_succ]
    linear_combination hEq
  have hCastEq :
      (((3 ^ k * (2 ^ n - 1) : ℕ) : ℤ)) =
        (((2 ^ (L + 1) - 1 : ℕ) : ℤ)) := by
    push_cast
    rw [hCastN, hCastL]
    exact hInt
  exact_mod_cast hCastEq

/--
`L+1=n*t` のとき residual equation は exact geometric sum になる。
-/
private theorem noHole_geometricSum_eq_threePow
    {k n L t : ℕ}
    (hn : 2 ≤ n)
    (hNt : L + 1 = n * t)
    (hEq : NoHoleEquation k n 1 L) :
    (∑ i ∈ Finset.range t, (2 ^ n) ^ i) = 3 ^ k := by
  let x : ℕ := 2 ^ n
  have hx : 2 ≤ x := by
    dsimp [x]
    have h := Nat.pow_le_pow_of_le
      (by norm_num : 1 < (2 : ℕ)) hn
    norm_num at h ⊢
    omega
  have hMain := noHole_mersenne_nat_identity (k := k) (n := n) (L := L) hEq
  rw [hNt] at hMain
  have hMainX :
      3 ^ k * (x - 1) = x ^ t - 1 := by
    dsimp [x]
    simpa [pow_mul] using hMain
  have hxSub : 0 < x - 1 := by omega
  have hDiv : (x ^ t - 1) / (x - 1) = 3 ^ k := by
    rw [← hMainX]
    exact Nat.mul_div_left (3 ^ k) hxSub
  rw [Nat.geomSum_eq hx t, hDiv]

/-- geometric sum の二分割。 -/
private theorem geomSum_two_mul
    (x u : ℕ) :
    (∑ i ∈ Finset.range (u * 2), x ^ i) =
      (∑ i ∈ Finset.range u, x ^ i) * (x ^ u + 1) := by
  have hRange := Finset.sum_range_add (fun i : ℕ => x ^ i) u u
  have hShift :
      (∑ i ∈ Finset.range u, x ^ (u + i)) =
        x ^ u * (∑ i ∈ Finset.range u, x ^ i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [pow_add]
  rw [show u * 2 = u + u by omega, hRange, hShift]
  ring

/-- geometric sum の三分割。 -/
private theorem geomSum_three_mul
    (x u : ℕ) :
    (∑ i ∈ Finset.range (u * 3), x ^ i) =
      (∑ i ∈ Finset.range u, x ^ i) *
        (x ^ (u * 2) + x ^ u + 1) := by
  have hRange :=
    Finset.sum_range_add (fun i : ℕ => x ^ i) u (u * 2)
  have hShift :
      (∑ i ∈ Finset.range (u * 2), x ^ (u + i)) =
        x ^ u * (∑ i ∈ Finset.range (u * 2), x ^ i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [pow_add]
  have hTwo := geomSum_two_mul x u
  rw [show u * 3 = u + u * 2 by omega, hRange, hShift, hTwo]
  rw [pow_mul]
  ring

/--
`d ∣ 3^k` で `9 ∤ d` なら `d=1` または `d=3`。
-/
private theorem eq_one_or_three_of_dvd_threePow_of_not_nine_dvd
    {d k : ℕ}
    (hDvd : d ∣ 3 ^ k)
    (hNine : ¬ 9 ∣ d) :
    d = 1 ∨ d = 3 := by
  rcases (Nat.dvd_prime_pow (by decide : Nat.Prime 3)).mp hDvd with
    ⟨j, hj, rfl⟩
  by_cases hj0 : j = 0
  · subst j
    simp
  · by_cases hj1 : j = 1
    · subst j
      simp
    · have hjTwo : 2 ≤ j := by omega
      have hNineDvd : 9 ∣ 3 ^ j := by
        refine ⟨3 ^ (j - 2), ?_⟩
        rw [show j = 2 + (j - 2) by omega, pow_add]
        norm_num
      exact False.elim (hNine hNineDvd)

/--
`d ∣ 3^k` かつ `d ≡ 3 (mod 9)` なら `d=3`。
-/
private theorem eq_three_of_dvd_threePow_of_mod9_eq_three
    {d k : ℕ}
    (hDvd : d ∣ 3 ^ k)
    (hMod : d % 9 = 3) :
    d = 3 := by
  have hNine : ¬ 9 ∣ d := by
    intro h
    have hZero := Nat.mod_eq_zero_of_dvd h
    omega
  rcases eq_one_or_three_of_dvd_threePow_of_not_nine_dvd hDvd hNine with
    hOne | hThree
  · subst d
    norm_num at hMod
  · exact hThree

/-! ## Layer 1: even quotient length -/

/--
`E>0` かつ `2^E+1 ∣ 3^k` なら `E` は odd。

`2^E+1>1` なのでこの divisor は正の `3` 冪であり、したがって 3 の倍数。
`E` が even なら `2^E+1 ≡ 2 (mod 3)` となって矛盾する。
-/
private theorem exponent_odd_of_twoPow_add_one_dvd_threePow
    {E k : ℕ}
    (hEPos : 0 < E)
    (hDvd : 2 ^ E + 1 ∣ 3 ^ k) :
    E % 2 = 1 := by
  let D : ℕ := 2 ^ E + 1
  have hDgt : 1 < D := by
    dsimp [D]
    have hPow : 1 < 2 ^ E :=
      Nat.one_lt_pow (Nat.ne_of_gt hEPos) (by norm_num : 1 < (2 : ℕ))
    omega
  have hDvdD : D ∣ 3 ^ k := by
    simpa [D] using hDvd
  rcases (Nat.dvd_prime_pow (by decide : Nat.Prime 3)).mp hDvdD with
    ⟨j, hj, hDj⟩
  have hjPos : 0 < j := by
    by_contra hNot
    have hj0 : j = 0 := by omega
    rw [hj0] at hDj
    simp at hDj
    omega
  have hThreeDvdD : 3 ∣ D := by
    rw [hDj]
    exact dvd_pow_self 3 (Nat.ne_of_gt hjPos)
  rcases Nat.mod_two_eq_zero_or_one E with hEven | hOdd
  · have hPeriod : (2 : ZMod 3) ^ 2 = 1 := by decide
    have hPow : (2 : ZMod 3) ^ E = 1 := by
      rw [pow_eq_pow_mod_of_pow_eq_one (2 : ZMod 3) (e := E) hPeriod]
      simp [hEven]
    have hZero : (D : ZMod 3) = 0 :=
      (ZMod.natCast_eq_zero_iff D 3).2 hThreeDvdD
    dsimp [D] at hZero
    push_cast at hZero
    rw [hPow] at hZero
    exfalso
    exact (by decide : (1 + 1 : ZMod 3) ≠ 0) hZero
  · exact hOdd

/--
`D=2^E+1` が `3^k` を割り、`E≥3` なら、`E` は `3` の倍数。

oddness は mod 3、`3 ∤ E` の排除は mod 9 だけを使う。
-/
private theorem three_dvd_exponent_of_twoPow_add_one_dvd_threePow
    {E k : ℕ}
    (hE : 3 ≤ E)
    (hDvd : 2 ^ E + 1 ∣ 3 ^ k) :
    3 ∣ E := by
  let D : ℕ := 2 ^ E + 1
  have hDgt : 1 < D := by
    dsimp [D]
    have hPow : 1 < 2 ^ E :=
      Nat.one_lt_pow (by omega : E ≠ 0) (by norm_num : 1 < (2 : ℕ))
    omega
  have hDvdD : D ∣ 3 ^ k := by
    simpa [D] using hDvd
  have hEOdd : E % 2 = 1 :=
    exponent_odd_of_twoPow_add_one_dvd_threePow (by omega) hDvd
  let a : ℕ := E / 2
  have hEDecomp : E = 2 * a + 1 := by
    have h := Nat.mod_add_div E 2
    dsimp [a]
    omega
  have haModLt : a % 3 < 3 := Nat.mod_lt _ (by omega)
  have haCases : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
  rcases haCases with ha0 | ha1 | ha2
  · have hPeriod : (4 : ZMod 9) ^ 3 = 1 := by decide
    have hPow4 : (4 : ZMod 9) ^ a = 1 := by
      rw [pow_eq_pow_mod_of_pow_eq_one (4 : ZMod 9) (e := a) hPeriod]
      simp [ha0]
    have hCast : (D : ZMod 9) = 3 := by
      dsimp [D]
      rw [hEDecomp, pow_add, pow_one]
      norm_num [pow_mul, hPow4]
    have hNine : ¬ 9 ∣ D := by
      intro hNineDvd
      have hZero : (D : ZMod 9) = 0 :=
        (ZMod.natCast_eq_zero_iff D 9).2 hNineDvd
      rw [hCast] at hZero
      exact (by decide : (3 : ZMod 9) ≠ 0) hZero
    rcases eq_one_or_three_of_dvd_threePow_of_not_nine_dvd hDvdD hNine with
      hOne | hThree
    · omega
    · have hPow : 8 ≤ 2 ^ E := by
        have h := Nat.pow_le_pow_of_le
          (by norm_num : 1 < (2 : ℕ)) hE
        norm_num at h ⊢
        exact h
      dsimp [D] at hThree
      omega
  · have hDiv : 3 ∣ E := by
      rcases Nat.mod_add_div a 3 with h
      refine ⟨2 * (a / 3) + 1, ?_⟩
      dsimp [a] at *
      omega
    exact hDiv
  · have hPeriod : (4 : ZMod 9) ^ 3 = 1 := by decide
    have hPow4 : (4 : ZMod 9) ^ a = (4 : ZMod 9) ^ 2 := by
      rw [pow_eq_pow_mod_of_pow_eq_one (4 : ZMod 9) (e := a) hPeriod]
      rw [ha2]
    have hCast : (D : ZMod 9) = 6 := by
      dsimp [D]
      rw [hEDecomp, pow_add, pow_one]
      norm_num [pow_mul, hPow4]
      decide
    have hNine : ¬ 9 ∣ D := by
      intro h
      have hZero : (D : ZMod 9) = 0 :=
        (ZMod.natCast_eq_zero_iff D 9).2 h
      rw [hCast] at hZero
      exact (by decide : (6 : ZMod 9) ≠ 0) hZero
    rcases eq_one_or_three_of_dvd_threePow_of_not_nine_dvd hDvdD hNine with
      hOne | hThree
    · omega
    · rw [hThree] at hCast
      exfalso
      exact (by decide : (3 : ZMod 9) ≠ 6) hCast

/--
`E=3s`, `s` odd のとき

`C = 2^(2s)-2^s+1`

は `2^E+1` の因子で、さらに `C ≡ 3 mod 9`。
Nat subtractionを避けるため `z=2^s-1`, `C=2^s*z+1` と表現する。
-/
private theorem cubic_factor_mod9
    {E s : ℕ}
    (hE : E = 3 * s)
    (hsOdd : s % 2 = 1) :
    ∃ C : ℕ,
      C ∣ 2 ^ E + 1 ∧
      C % 9 = 3 ∧
      (C = 3 → s = 1) := by
  let y : ℕ := 2 ^ s
  let z : ℕ := y - 1
  let C : ℕ := y * z + 1
  have hyPos : 0 < y := by dsimp [y]; positivity
  have hyOne : 1 ≤ y := by omega
  have hyEq : y = z + 1 := by
    dsimp [z]
    omega
  have hFactor : 2 ^ E + 1 = (y + 1) * C := by
    rw [hE, show 3 * s = s * 3 by omega, pow_mul]
    change y ^ 3 + 1 = (y + 1) * C
    dsimp [C]
    rw [hyEq]
    ring
  have hCDvd : C ∣ 2 ^ E + 1 := by
    refine ⟨y + 1, ?_⟩
    rw [hFactor]
    ring
  let b : ℕ := s / 2
  have hsDecomp : s = 2 * b + 1 := by
    have h := Nat.mod_add_div s 2
    dsimp [b]
    omega
  have hPeriod : (4 : ZMod 9) ^ 3 = 1 := by decide
  have hbLt : b % 3 < 3 := Nat.mod_lt _ (by omega)
  have hbCases : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by omega
  have hCmod : C % 9 = 3 := by
    have hzCast : (z : ZMod 9) = (y : ZMod 9) - 1 := by
      dsimp [z]
      rw [Nat.cast_sub hyOne]
      norm_num
    have hCastY :
        (y : ZMod 9) = 2 * (4 : ZMod 9) ^ b := by
      dsimp [y]
      rw [hsDecomp, pow_add, pow_one, pow_mul]
      norm_num
      ring
    have hCastC : (C : ZMod 9) = 3 := by
      dsimp [C]
      push_cast
      rw [hzCast, hCastY]
      rcases hbCases with hb0 | hb1 | hb2
      · rw [pow_eq_pow_mod_of_pow_eq_one (4 : ZMod 9) (e := b) hPeriod]
        norm_num [hb0]
      · rw [pow_eq_pow_mod_of_pow_eq_one (4 : ZMod 9) (e := b) hPeriod]
        norm_num [hb1]
        decide
      · rw [pow_eq_pow_mod_of_pow_eq_one (4 : ZMod 9) (e := b) hPeriod]
        norm_num [hb2]
        decide
    have hModRaw : C % 9 = 3 % 9 :=
      nat_mod_eq_of_zmod_natCast_eq (by simpa using hCastC)
    norm_num at hModRaw ⊢
    exact hModRaw
  refine ⟨C, hCDvd, hCmod, ?_⟩
  intro hCthree
  have hzOne : z = 1 := by
    dsimp [C] at hCthree
    rw [hyEq] at hCthree
    nlinarith
  have hyTwo : y = 2 := by
    rw [hyEq, hzOne]
  dsimp [y] at hyTwo
  exact Nat.pow_right_injective (by norm_num : 2 ≤ (2 : ℕ))
    (by simpa using hyTwo)

/-! ## Layer 2: odd quotient length -/

/--
`n` even なら `x=2^n` を base とする geometric sum が `3^k` のとき、
その長さ `t` は 3 の倍数。
-/
private theorem three_dvd_geometric_length
    {k n t : ℕ}
    (hk : 0 < k)
    (hnEven : n % 2 = 0)
    (hSum : (∑ i ∈ Finset.range t, (2 ^ n) ^ i) = 3 ^ k) :
    3 ∣ t := by
  have hCast := congrArg (fun z : ℕ => (z : ZMod 3)) hSum
  push_cast at hCast
  have hTwoPeriod : (2 : ZMod 3) ^ 2 = 1 := by decide
  have hTwoN : (2 : ZMod 3) ^ n = 1 := by
    rw [pow_eq_pow_mod_of_pow_eq_one (2 : ZMod 3) (e := n) hTwoPeriod]
    simp [hnEven]
  have hThreeK : (3 : ZMod 3) ^ k = 0 := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    rw [pow_succ]
    have hThreeZero : (3 : ZMod 3) = 0 := by decide
    rw [hThreeZero, mul_zero]
  rw [hThreeK] at hCast
  simp only [hTwoN, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hCast
  exact (ZMod.natCast_eq_zero_iff t 3).1 hCast

/--
`E` even なら `2^(2E)+2^E+1 ≡ 3 mod 9`。
-/
private theorem quadratic_factor_mod9_of_even
    {E : ℕ}
    (hEven : E % 2 = 0) :
    (2 ^ (E * 2) + 2 ^ E + 1) % 9 = 3 := by
  let a : ℕ := E / 2
  have hE : E = 2 * a := by
    have h := Nat.mod_add_div E 2
    dsimp [a]
    omega
  have hPeriod : (4 : ZMod 9) ^ 3 = 1 := by decide
  have haLt : a % 3 < 3 := Nat.mod_lt _ (by omega)
  have haCases : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
  have hCast :
      ((2 ^ (E * 2) + 2 ^ E + 1 : ℕ) : ZMod 9) = 3 := by
    rw [hE]
    push_cast
    rw [show (2 : ZMod 9) ^ (2 * a) = (4 : ZMod 9) ^ a by
      rw [pow_mul]
      norm_num]
    rw [show (2 : ZMod 9) ^ ((2 * a) * 2) = ((4 : ZMod 9) ^ a) ^ 2 by
      rw [pow_mul, pow_mul]
      norm_num]
    rcases haCases with ha0 | ha1 | ha2
    · rw [pow_eq_pow_mod_of_pow_eq_one (4 : ZMod 9) (e := a) hPeriod]
      norm_num [ha0]
    · rw [pow_eq_pow_mod_of_pow_eq_one (4 : ZMod 9) (e := a) hPeriod]
      norm_num [ha1]
      decide
    · rw [pow_eq_pow_mod_of_pow_eq_one (4 : ZMod 9) (e := a) hPeriod]
      norm_num [ha2]
      decide
  have hModRaw :
      (2 ^ (E * 2) + 2 ^ E + 1) % 9 = 3 % 9 :=
    nat_mod_eq_of_zmod_natCast_eq (by simpa using hCast)
  norm_num at hModRaw ⊢
  exact hModRaw

/-! **## Layer 3: residual 本体** -/

/--
no-hole equation から、正の geometric length `t` と
対応する geometric sum 表現を取り出す。

この補題より下では `L` の divisibility を毎回展開しない。
-/
private theorem NoHoleEquation.exists_positive_geometric_length
    {k n L : ℕ}
    (hnTwo : 2 ≤ n)
    (hEq : NoHoleEquation k n 1 L) :
    ∃ t : ℕ,
      0 < t ∧
      L + 1 = n * t ∧
      (∑ i ∈ Finset.range t, (2 ^ n) ^ i) = 3 ^ k := by
  have hNDvd : n ∣ L + 1 :=
    noHole_mersenne_exponent_dvd hnTwo hEq
  rcases hNDvd with ⟨t, hNt⟩
  have htPos : 0 < t := by
    by_contra hNot
    have ht0 : t = 0 := Nat.eq_zero_of_not_pos hNot
    rw [ht0] at hNt
    simp at hNt
  have hSum :
      (∑ i ∈ Finset.range t, (2 ^ n) ^ i) = 3 ^ k :=
    noHole_geometricSum_eq_threePow hnTwo hNt hEq
  exact ⟨t, htPos, hNt, hSum⟩


/--
geometric length `t` が偶数なら、cubic factor の mod 9 制約から
必ず `n = 3`, `t = 2` まで縮退する。

ここではまだ `k ≥ 4` は使わない。
-/
private theorem even_geometric_length_shape
    {k n t : ℕ}
    (hn : 3 ≤ n)
    (htPos : 0 < t)
    (htEven : t % 2 = 0)
    (hSum :
      (∑ i ∈ Finset.range t, (2 ^ n) ^ i) = 3 ^ k) :
    n = 3 ∧ t = 2 := by
  let u : ℕ := t / 2
  have htDecomp : t = u * 2 := by
    have h := Nat.mod_add_div t 2
    dsimp [u]
    omega
  have huPos : 0 < u := by
    by_contra hNot
    have hu0 : u = 0 := Nat.eq_zero_of_not_pos hNot
    rw [hu0] at htDecomp
    simp at htDecomp
    omega
  let x : ℕ := 2 ^ n
  have hFact :
      (∑ i ∈ Finset.range t, x ^ i) =
        (∑ i ∈ Finset.range u, x ^ i) * (x ^ u + 1) := by
    rw [htDecomp]
    exact geomSum_two_mul x u
  have hDvd : x ^ u + 1 ∣ 3 ^ k := by
    refine ⟨(∑ i ∈ Finset.range u, x ^ i), ?_⟩
    rw [← hSum]
    simpa [x, Nat.mul_comm] using hFact
  let E : ℕ := n * u
  have hEThree : 3 ≤ E := by
    dsimp [E]
    have huOne : 1 ≤ u := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt huPos)
    calc
      3 ≤ n := hn
      _ = n * 1 := by simp
      _ ≤ n * u := Nat.mul_le_mul_left n huOne
  have hDvdE : 2 ^ E + 1 ∣ 3 ^ k := by
    dsimp [E, x] at hDvd ⊢
    simpa [pow_mul] using hDvd
  have hThreeE : 3 ∣ E :=
    three_dvd_exponent_of_twoPow_add_one_dvd_threePow
      hEThree hDvdE
  rcases hThreeE with ⟨s, hEs⟩
  have hsPos : 0 < s := by
    by_contra hNot
    have hs0 : s = 0 := Nat.eq_zero_of_not_pos hNot
    rw [hs0] at hEs
    simp at hEs
    omega
  have hEOdd : E % 2 = 1 :=
    exponent_odd_of_twoPow_add_one_dvd_threePow
      (by omega) hDvdE
  have hsOdd : s % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one s with hsEven | hsOdd
    · have hMod : E % 2 = 0 := by
        rw [hEs]
        omega
      omega
    · exact hsOdd
  rcases cubic_factor_mod9 hEs hsOdd with
    ⟨C, hCDvdD, hCmod, hCthreeToS⟩
  have hCDvd : C ∣ 3 ^ k :=
    hCDvdD.trans hDvdE
  have hCthree :
      C = 3 :=
    eq_three_of_dvd_threePow_of_mod9_eq_three
      hCDvd hCmod
  have hsOne : s = 1 :=
    hCthreeToS hCthree
  have hEeq : E = 3 := by
    simpa [hsOne] using hEs
  have hNu : n * u = 3 := by
    simpa [E] using hEeq
  have huOne : 1 ≤ u :=
    Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt huPos)
  have hnLeProd : n ≤ n * u := by
    simpa using Nat.mul_le_mul_left n huOne
  rw [hNu] at hnLeProd
  have hnEq : n = 3 := by
    omega
  have huEq : u = 1 := by
    have hNu' := hNu
    rw [hnEq] at hNu'
    omega
  have htTwo : t = 2 := by
    calc
      t = u * 2 := htDecomp
      _ = 1 * 2 := by rw [huEq]
      _ = 2 := by norm_num
  exact ⟨hnEq, htTwo⟩


/--
even geometric length の場合は `n=3, t=2` となるが、
その geometric sum は `3^k = 9` を強制する。

したがって `k ≥ 4` と両立しない。
-/
private theorem even_geometric_length_impossible
    {k n t : ℕ}
    (hkFour : 4 ≤ k)
    (hn : 3 ≤ n)
    (htPos : 0 < t)
    (htEven : t % 2 = 0)
    (hSum :
      (∑ i ∈ Finset.range t, (2 ^ n) ^ i) = 3 ^ k) :
    False := by
  rcases even_geometric_length_shape
      hn htPos htEven hSum with
    ⟨hnEq, htTwo⟩
  have hSumTwo :
      (∑ i ∈ Finset.range 2, (2 ^ 3) ^ i) = 3 ^ k := by
    simpa [hnEq, htTwo] using hSum
  norm_num at hSumTwo
  have hPow :
      3 ^ k = 3 ^ 2 := by
    norm_num
    exact hSumTwo.symm
  have hkTwo : k = 2 :=
    Nat.pow_right_injective
      (by norm_num : 2 ≤ (3 : ℕ))
      hPow
  omega


/--
geometric length `t` が奇数なら、`L` の parity から `n` は偶数。

さらに `3 ∣ t` を使って三分割した geometric factor

`C = x^(2u) + x^u + 1`

を取り出すと、mod 9 では `C ≡ 3`。
一方 `C ∣ 3^k` なので `C = 3` だが、
`E = n*u ≥ 3` から実際には `C > 3` となり矛盾する。
-/
private theorem odd_geometric_length_impossible
    {k n L t : ℕ}
    (hkPos : 0 < k)
    (hn : 3 ≤ n)
    (htPos : 0 < t)
    (htOdd : t % 2 = 1)
    (hNt : L + 1 = n * t)
    (hSum :
      (∑ i ∈ Finset.range t, (2 ^ n) ^ i) = 3 ^ k)
    (hEq : NoHoleEquation k n 1 L) :
    False := by
  have hResidues :=
    hEq.mod_two_residues hkPos
  have hLOdd := hResidues.2
  have hNTEven : (n * t) % 2 = 0 := by
    rw [← hNt, Nat.add_mod, hLOdd]
  have hnEven : n % 2 = 0 := by
    rcases Nat.mod_two_eq_zero_or_one n with hnEven | hnOdd
    · exact hnEven
    · rw [Nat.mul_mod, hnOdd, htOdd] at hNTEven
      norm_num at hNTEven
  have hThreeT : 3 ∣ t :=
    three_dvd_geometric_length hkPos hnEven hSum
  rcases hThreeT with ⟨u, hTu⟩
  have hTu' : t = u * 3 := by
    simpa [Nat.mul_comm] using hTu
  have huPos : 0 < u := by
    by_contra hNot
    have hu0 : u = 0 := Nat.eq_zero_of_not_pos hNot
    rw [hu0] at hTu'
    simp at hTu'
    omega
  let x : ℕ := 2 ^ n
  have hFact :
      (∑ i ∈ Finset.range t, x ^ i) =
        (∑ i ∈ Finset.range u, x ^ i) *
          (x ^ (u * 2) + x ^ u + 1) := by
    rw [hTu']
    exact geomSum_three_mul x u
  let C : ℕ :=
    x ^ (u * 2) + x ^ u + 1
  have hCDvd : C ∣ 3 ^ k := by
    refine ⟨(∑ i ∈ Finset.range u, x ^ i), ?_⟩
    rw [← hSum]
    simpa [C, x, Nat.mul_comm] using hFact
  let E : ℕ := n * u
  have hEEven : E % 2 = 0 := by
    dsimp [E]
    rw [Nat.mul_mod, hnEven]
    simp
  have hCexpr :
      C = 2 ^ (E * 2) + 2 ^ E + 1 := by
    dsimp [C, x, E]
    simp [pow_mul, Nat.mul_assoc]
  have hCmod0 :=
    quadratic_factor_mod9_of_even
      (E := E) hEEven
  have hCmod : C % 9 = 3 := by
    rw [hCexpr]
    exact hCmod0
  have hCthree : C = 3 :=
    eq_three_of_dvd_threePow_of_mod9_eq_three
      hCDvd hCmod
  have hEThree : 3 ≤ E := by
    dsimp [E]
    have huOne : 1 ≤ u :=
      Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt huPos)
    calc
      3 ≤ n := hn
      _ = n * 1 := by simp
      _ ≤ n * u := Nat.mul_le_mul_left n huOne
  have hPowLower : 8 ≤ 2 ^ E := by
    have h :=
      Nat.pow_le_pow_of_le
        (by norm_num : 1 < (2 : ℕ))
        hEThree
    norm_num at h ⊢
    exact h
  have hSmallLt : 3 < 2 ^ E + 1 := by
    omega
  have hSmallLe : 2 ^ E + 1 ≤ C := by
    rw [hCexpr]
    calc
      2 ^ E + 1
          ≤ 2 ^ (E * 2) + (2 ^ E + 1) :=
        Nat.le_add_left _ _
      _ = 2 ^ (E * 2) + 2 ^ E + 1 := by
        simp only [Nat.add_assoc]
  have hCLarge : 3 < C :=
    lt_of_lt_of_le hSmallLt hSmallLe
  omega


/--
最後の no-hole residual は elementary に排除できる。

Layer 3 本体では quotient `t` を構成し、その parity に応じて
既に分離した二つの枝へ渡すだけでよい。
-/
theorem noHoleEvenMersenneQuotientResidual :
    NoHoleEvenMersenneQuotientResidual := by
  intro k n L hkFour hkEven hn hL hEq
  have hkPos : 0 < k := by
    omega
  have hnTwo : 2 ≤ n := by
    omega
  rcases hEq.exists_positive_geometric_length
      hnTwo with
    ⟨t, htPos, hNt, hSum⟩
  rcases Nat.mod_two_eq_zero_or_one t with htEven | htOdd
  · exact
      even_geometric_length_impossible
        hkFour hn htPos htEven hSum
  · exact
      odd_geometric_length_impossible
        hkPos hn htPos htOdd hNt hSum hEq

/--
最後の residual が閉じたので no-hole 完全分類も無条件に成立する。
-/
theorem noHoleCompleteClassification :
    NoHoleCompleteClassification :=
  noHoleCompleteClassification_of_mersenneQuotientResidual
    noHoleEvenMersenneQuotientResidual

end Mersenne
end Collatz3
