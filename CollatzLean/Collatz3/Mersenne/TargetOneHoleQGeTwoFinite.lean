import CollatzLean.Collatz3.Mersenne.TargetOneHoleQGeTwoArithmetic
import Std.Data.HashSet.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option linter.style.nativeDecide false

/-!
# Collatz3 Mersenne: target-one `q≥2` の内部 M₄ finite sieve

A1 の残り B/D

* B: even, `r=1`, `q≥2`
* D: odd,  `r=2`, `q≥2`

について、`TargetOneHoleQGeTwoArithmetic` の内部 bound `k<2^101` の後を
既存 3-adic tail modulus

`M₄ = 561847684041`

だけで閉じる。

幾何和 equation に `2^n-1` を掛けると

`(2^n-1)3^k + 2^(nq) + (2^r-1) = 2^r 2^(nt)`

となる。`M₄` 上では 2 の period は 486 なので、有限 certificate では
`nq` と `nt` の位相をそれぞれ **独立な 486 通り全部**まで広げる。
これは `q<t` や `gcd(q,t)=1` を捨てた強い over-approximation である。

右辺から `2^(nq)` を移した差

`2^r 2^T - 2^Q`

を 486² 個だけ HashSet 化する。すると計算核は `(K,N)` だけになり、

* `K < 978` : 3 の tail 6 / period 972 representative,
* `N < 103` : `k<2^101` と exact 2-adic width lock から得る source width,

について membership を判定すればよい。

B/D とも survivor は 0。解析 bound と同様、この finite sieve 自体も
`gcd(q,t)=1` を仮定しない。
-/

namespace Collatz3
namespace Mersenne

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

open PowTailLoop

/-! ## M₄ 上の有限 phase difference -/

/-- `K,N,r` だけに依存する、幾何 equation の固定側 residue。 -/
private def qGeTwoM4Core
    (K N r : ℕ) : ZMod oneHoleThreeTailModulus :=
  (3 : ZMod oneHoleThreeTailModulus) ^ K *
      ((2 : ZMod oneHoleThreeTailModulus) ^ N - 1) +
    ((2 : ZMod oneHoleThreeTailModulus) ^ r - 1)

/-- 自由化した二つの 2-power phase の差。 -/
private def qGeTwoM4PhaseDiff
    (r Q T : ℕ) : ZMod oneHoleThreeTailModulus :=
  (2 : ZMod oneHoleThreeTailModulus) ^ r *
      (2 : ZMod oneHoleThreeTailModulus) ^ T -
    (2 : ZMod oneHoleThreeTailModulus) ^ Q

/-- 固定 `r` に対し 486² 個の phase difference を一度だけ列挙する。 -/
private def qGeTwoM4PhaseDiffList (r : ℕ) : List ℕ :=
  (List.range 486).flatMap fun Q =>
    (List.range 486).map fun T =>
      (qGeTwoM4PhaseDiff r Q T).val

/-- phase difference の reachable set。 -/
private def qGeTwoM4PhaseDiffSet (r : ℕ) : Std.HashSet ℕ :=
  Std.HashSet.ofList (qGeTwoM4PhaseDiffList r)

/-- 任意の有限 phase pair は reachable set に入る。 -/
private theorem qGeTwoM4PhaseDiffSet_contains
    (r : ℕ)
    (Q T : Fin 486) :
    (qGeTwoM4PhaseDiffSet r).contains
        (qGeTwoM4PhaseDiff r Q.1 T.1).val = true := by
  have hMem :
      (qGeTwoM4PhaseDiff r Q.1 T.1).val ∈
        qGeTwoM4PhaseDiffList r := by
    unfold qGeTwoM4PhaseDiffList
    apply List.mem_flatMap.mpr
    refine ⟨Q.1, List.mem_range.mpr Q.2, ?_⟩
    apply List.mem_map.mpr
    exact ⟨T.1, List.mem_range.mpr T.2, rfl⟩
  simpa only [
    qGeTwoM4PhaseDiffSet,
    Std.HashSet.contains_ofList,
    List.contains_eq_mem,
    decide_eq_true_eq
  ] using hMem

/-!
B/D の計算 certificate。

`q,t` の関係は一切使わず、両 2-power phase を 486 通り全部許している。
それでも survivor は 0。
-/

/-- B (`r=1`) の M₄ certificate。even 3-tail state は一つも生き残らない。 -/
private theorem even_q_ge_two_m4_finite_sieve :
    ∀ K : Fin 978,
      ∀ N : Fin 103,
        4 ≤ K.1 →
        3 ≤ N.1 →
        K.1 % 2 = 0 →
        (qGeTwoM4PhaseDiffSet 1).contains
          (qGeTwoM4Core K.1 N.1 1).val = false := by
  native_decide

/-- D (`r=2`) の M₄ certificate。odd 3-tail state も一つも生き残らない。 -/
private theorem odd_q_ge_two_m4_finite_sieve :
    ∀ K : Fin 978,
      ∀ N : Fin 103,
        4 ≤ K.1 →
        3 ≤ N.1 →
        K.1 % 2 = 1 →
        (qGeTwoM4PhaseDiffSet 2).contains
          (qGeTwoM4Core K.1 N.1 2).val = false := by
  native_decide

/-! ## exact geometric equation から finite phase equation へ -/

/--
幾何和 equation を `2^n-1` 倍した exact identity。

この形では `q,t` は 2-power exponent `nq,nt` にしか現れず、M₄ の period 486 で
完全に有限 phase へ送れる。
-/
private theorem TargetOneHoleGeometricData.qGeTwo_exact_phase_identity
    {k n r L b : ℕ}
    (h : TargetOneHoleGeometricData k n r L b) :
    (2 ^ n - 1) * 3 ^ k + 2 ^ (n * h.q) + (2 ^ r - 1) =
      2 ^ (r + n * h.t) := by
  let x : ℕ := 2 ^ n
  let R : ℕ := 2 ^ r
  have hxOne : 1 ≤ x := by
    dsimp [x]
    have hxPos : 0 < 2 ^ n := by positivity
    omega
  have hqOne : 1 ≤ x ^ h.q :=
    Nat.one_le_pow h.q x hxOne
  have htOne : 1 ≤ x ^ h.t :=
    Nat.one_le_pow h.t x hxOne
  have hROne : 1 ≤ R := by
    dsimp [R]
    have hRPos : 0 < 2 ^ r := by positivity
    omega
  have hGq :
      targetGeomSum x h.q * (x - 1) = x ^ h.q - 1 := by
    unfold targetGeomSum
    exact geom_sum_mul_of_one_le hxOne h.q
  have hGt :
      targetGeomSum x h.t * (x - 1) = x ^ h.t - 1 := by
    unfold targetGeomSum
    exact geom_sum_mul_of_one_le hxOne h.t
  have hMul := congrArg (fun z : ℕ => z * (x - 1)) h.equation
  change
      (3 ^ k + targetGeomSum x h.q) * (x - 1) =
        (R * targetGeomSum x h.t) * (x - 1) at hMul
  rw [Nat.add_mul, hGq, mul_assoc, hGt] at hMul
  have hCommon :
      3 ^ k * (x - 1) + R + x ^ h.q =
        R * x ^ h.t + 1 := by
    calc
      3 ^ k * (x - 1) + R + x ^ h.q
          = (3 ^ k * (x - 1) + (x ^ h.q - 1)) + R + 1 := by
              omega
      _ = R * (x ^ h.t - 1) + R + 1 := by
              rw [hMul]
      _ = R * ((x ^ h.t - 1) + 1) + 1 := by
              simp [Nat.mul_add]
      _ = R * x ^ h.t + 1 := by
              rw [Nat.sub_add_cancel htOne]
  have hCore :
      3 ^ k * (x - 1) + x ^ h.q + (R - 1) =
        R * x ^ h.t := by
    omega
  dsimp [x, R] at hCore
  simpa [pow_mul, pow_add, Nat.mul_comm] using hCore

/-- 3-tail representative は mod 2 で元の `k` と同じ parity を持つ。 -/
private theorem threeTailRep_mod_two (k : ℕ) :
    tailLoopExponent 6 972 k % 2 = k % 2 := by
  unfold tailLoopExponent
  split
  · rfl
  · rename_i h
    have hk6 : 6 ≤ k := Nat.le_of_not_gt h
    have hmod : ((k - 6) % 972) % 2 = (k - 6) % 2 := by
      simp only [Nat.reduceDvd, Nat.mod_mod_of_dvd]
    rw [Nat.add_mod, hmod]
    omega

/-- `k≥4` なら 3-tail representative も 4 以上。 -/
private theorem four_le_threeTailRep
    {k : ℕ}
    (hk : 4 ≤ k) :
    4 ≤ tailLoopExponent 6 972 k := by
  unfold tailLoopExponent
  split <;> omega

/--
任意の geometric data から、実際の `q,t` 位相を M₄ reachable set の witness にする。

ここでは `q,t` の大小・gcd・`q≥2` は不要。
-/
private theorem TargetOneHoleGeometricData.qGeTwo_m4_membership
    {k n r L b : ℕ}
    (h : TargetOneHoleGeometricData k n r L b)
    (hk : 4 ≤ k)
    (hn : 3 ≤ n)
    (hn103 : n < 103) :
    ∃ K : Fin 978,
      ∃ N : Fin 103,
        4 ≤ K.1 ∧
        3 ≤ N.1 ∧
        K.1 % 2 = k % 2 ∧
        (qGeTwoM4PhaseDiffSet r).contains
          (qGeTwoM4Core K.1 N.1 r).val = true := by
  have hExact := h.qGeTwo_exact_phase_identity
  have hnOne : 1 ≤ 2 ^ n := by
    have hp : 0 < 2 ^ n := by positivity
    omega
  have hrOne : 1 ≤ 2 ^ r := by
    have hp : 0 < 2 ^ r := by positivity
    omega
  have hCast :=
    congrArg (fun z : ℕ => (z : ZMod oneHoleThreeTailModulus)) hExact
  push_cast [Nat.cast_sub hnOne, Nat.cast_sub hrOne] at hCast
  rw [pow_add] at hCast
  have hCastZ :
      (((2 ^ n - 1 : ℕ) : ZMod oneHoleThreeTailModulus) *
          (3 : ZMod oneHoleThreeTailModulus) ^ k +
        (2 : ZMod oneHoleThreeTailModulus) ^ (n * h.q) +
          ((2 ^ r - 1 : ℕ) : ZMod oneHoleThreeTailModulus)) =
        (2 : ZMod oneHoleThreeTailModulus) ^ r *
          (2 : ZMod oneHoleThreeTailModulus) ^ (n * h.t) := by
    exact_mod_cast hCast
  push_cast [Nat.cast_sub hnOne, Nat.cast_sub hrOne] at hCastZ
  have h3k' :
      (3 : ZMod oneHoleThreeTailModulus) ^ k =
        (3 : ZMod oneHoleThreeTailModulus) ^
          tailLoopExponent 6 972 k := by
    simpa using
      (pow_reduce
        (h := powTailLoop_three_oneHoleThreeTail)
        (e := k))
  have h2q' :
      (2 : ZMod oneHoleThreeTailModulus) ^ (n * h.q) =
        (2 : ZMod oneHoleThreeTailModulus) ^
          tailLoopExponent 0 486 (n * h.q) := by
    simpa using
      (pow_reduce
        (h := powTailLoop_two_oneHoleThreeTail)
        (e := n * h.q))
  have h2t' :
      (2 : ZMod oneHoleThreeTailModulus) ^ (n * h.t) =
        (2 : ZMod oneHoleThreeTailModulus) ^
          tailLoopExponent 0 486 (n * h.t) := by
    simpa using
      (pow_reduce
        (h := powTailLoop_two_oneHoleThreeTail)
        (e := n * h.t))
  rw [h3k', h2q', h2t'] at hCastZ
  let K : ℕ := tailLoopExponent 6 972 k
  let Q : ℕ := tailLoopExponent 0 486 (n * h.q)
  let T : ℕ := tailLoopExponent 0 486 (n * h.t)
  have hKlt : K < 978 := by
    dsimp [K]
    have hRep :=
      powTailLoop_three_oneHoleThreeTail.tailLoopExponent_lt (e := k)
    norm_num at hRep ⊢
    exact hRep
  have hQlt : Q < 486 := by
    dsimp [Q]
    have hRep :=
      powTailLoop_two_oneHoleThreeTail.tailLoopExponent_lt (e := n * h.q)
    norm_num at hRep ⊢
    exact hRep
  have hTlt : T < 486 := by
    dsimp [T]
    have hRep :=
      powTailLoop_two_oneHoleThreeTail.tailLoopExponent_lt (e := n * h.t)
    norm_num at hRep ⊢
    exact hRep
  let Kf : Fin 978 := ⟨K, hKlt⟩
  let Nf : Fin 103 := ⟨n, hn103⟩
  let Qf : Fin 486 := ⟨Q, hQlt⟩
  let Tf : Fin 486 := ⟨T, hTlt⟩
  have hFiniteEq :
      qGeTwoM4Core Kf.1 Nf.1 r +
          (2 : ZMod oneHoleThreeTailModulus) ^ Qf.1 =
        (2 : ZMod oneHoleThreeTailModulus) ^ r *
          (2 : ZMod oneHoleThreeTailModulus) ^ Tf.1 := by
    dsimp [qGeTwoM4Core, Kf, Nf, Qf, Tf, K, Q, T]
    simpa [mul_comm, add_assoc, add_comm, add_left_comm] using hCastZ
  have hDiff :
      qGeTwoM4Core Kf.1 Nf.1 r =
        qGeTwoM4PhaseDiff r Qf.1 Tf.1 := by
    unfold qGeTwoM4PhaseDiff
    linear_combination hFiniteEq
  have hVal := congrArg ZMod.val hDiff
  have hMem :
      (qGeTwoM4PhaseDiffSet r).contains
          (qGeTwoM4Core Kf.1 Nf.1 r).val = true := by
    rw [hVal]
    exact qGeTwoM4PhaseDiffSet_contains r Qf Tf
  refine ⟨Kf, Nf, ?_, hn, ?_, hMem⟩
  · dsimp [Kf, K]
    exact four_le_threeTailRep hk
  · dsimp [Kf, K]
    exact threeTailRep_mod_two k

/-! ## `k<2^101` から `n<103` -/

/-- B では `n=2+v₂(k)` と `k<2^101` から `n<103`。 -/
private theorem qGeTwo_width_lt_103_even
    {k n L b : ℕ}
    (h : TargetOneHoleGeometricData k n 1 L b)
    (hk : 4 ≤ k)
    (hn : 3 ≤ n)
    (hkEven : k % 2 = 0)
    (hqt : h.q < h.t)
    (hqTwo : 2 ≤ h.q)
    (hBound : k < targetOneQGeTwoInternalDepthBound) :
    n < 103 := by
  have hWidth :=
    h.even_q_ge_two_width_eq
      (by omega) ((Nat.even_iff).2 hkEven) (by omega) hqt hqTwo
  by_contra hNot
  have hv : 101 ≤ padicValNat 2 k := by
    omega
  have hdvd : 2 ^ 101 ∣ k :=
    (padicValNat_dvd_iff_le
      (p := 2) (a := k) (n := 101) (by omega)).2 hv
  have hle : 2 ^ 101 ≤ k :=
    Nat.le_of_dvd (by omega) hdvd
  unfold targetOneQGeTwoInternalDepthBound at hBound
  omega

/-- D では `n=2+v₂(k-1)` と `k<2^101` から同じく `n<103`。 -/
private theorem qGeTwo_width_lt_103_odd
    {k n L b : ℕ}
    (h : TargetOneHoleGeometricData k n 2 L b)
    (hk : 4 ≤ k)
    (hn : 3 ≤ n)
    (hkOdd : k % 2 = 1)
    (hqt : h.q < h.t)
    (hqTwo : 2 ≤ h.q)
    (hBound : k < targetOneQGeTwoInternalDepthBound) :
    n < 103 := by
  have hWidth :=
    h.odd_q_ge_two_width_eq (by omega) hkOdd (by omega) hqt hqTwo
  by_contra hNot
  have hv : 101 ≤ padicValNat 2 (k - 1) := by
    omega
  have hdvd : 2 ^ 101 ∣ k - 1 :=
    (padicValNat_dvd_iff_le
      (p := 2) (a := k - 1) (n := 101) (by omega)).2 hv
  have hle : 2 ^ 101 ≤ k - 1 :=
    Nat.le_of_dvd (by omega) hdvd
  unfold targetOneQGeTwoInternalDepthBound at hBound
  omega

/-! ## B/D public finite sieve -/

/--
B (`even,q≥2`) の bounded residual は M₄ certificate だけで排除できる。

`gcd(q,t)=1` は仮定しない。実際の `nq,nt` phase よりはるかに大きい
486×486 の自由 phase 空間を許しても survivor がないためである。
-/
theorem TargetOneHoleGeometricData.even_q_ge_two_internal_finite_sieve
    {k n L b : ℕ}
    (h : TargetOneHoleGeometricData k n 1 L b)
    (hk : 4 ≤ k)
    (hn : 3 ≤ n)
    (hkEven : k % 2 = 0)
    (hqt : h.q < h.t)
    (hqTwo : 2 ≤ h.q)
    (hBound : k < targetOneQGeTwoInternalDepthBound) :
    False := by
  have hn103 :=
    qGeTwo_width_lt_103_even h hk hn hkEven hqt hqTwo hBound
  rcases h.qGeTwo_m4_membership hk hn hn103 with
    ⟨K, N, hK4, hN3, hKParity, hMem⟩
  have hKEven : K.1 % 2 = 0 := by
    omega
  have hNo := even_q_ge_two_m4_finite_sieve K N hK4 hN3 hKEven
  rw [hMem] at hNo
  cases hNo

/--
D (`odd,q≥2`) の bounded residual も同じ M₄ certificate で排除できる。

こちらも `gcd(q,t)=1` は不要。
-/
theorem TargetOneHoleGeometricData.odd_q_ge_two_internal_finite_sieve
    {k n L b : ℕ}
    (h : TargetOneHoleGeometricData k n 2 L b)
    (hk : 4 ≤ k)
    (hn : 3 ≤ n)
    (hkOdd : k % 2 = 1)
    (hqt : h.q < h.t)
    (hqTwo : 2 ≤ h.q)
    (hBound : k < targetOneQGeTwoInternalDepthBound) :
    False := by
  have hn103 :=
    qGeTwo_width_lt_103_odd h hk hn hkOdd hqt hqTwo hBound
  rcases h.qGeTwo_m4_membership hk hn hn103 with
    ⟨K, N, hK4, hN3, hKParity, hMem⟩
  have hKOdd : K.1 % 2 = 1 := by
    omega
  have hNo := odd_q_ge_two_m4_finite_sieve K N hK4 hN3 hKOdd
  rw [hMem] at hNo
  cases hNo

/-! ## B/D 最終無条件 closure -/

/-- B (`even,q≥2`) は解析 bound と M₄ finite sieve の合成で内部排除。 -/
theorem TargetOneHoleGeometricData.even_q_ge_two_impossible_internal
    {k n L b : ℕ}
    (h : TargetOneHoleGeometricData k n 1 L b)
    (hk : 4 ≤ k)
    (hn : 3 ≤ n)
    (hkEven : k % 2 = 0)
    (hqt : h.q < h.t)
    (hqTwo : 2 ≤ h.q) :
    False := by
  have hBound :=
    h.even_q_ge_two_internal_depth_bound hk hn hkEven hqt hqTwo
  exact h.even_q_ge_two_internal_finite_sieve
    hk hn hkEven hqt hqTwo hBound

/-- D (`odd,q≥2`) も解析 bound と M₄ finite sieve の合成で内部排除。 -/
theorem TargetOneHoleGeometricData.odd_q_ge_two_impossible_internal
    {k n L b : ℕ}
    (h : TargetOneHoleGeometricData k n 2 L b)
    (hk : 4 ≤ k)
    (hn : 3 ≤ n)
    (hkOdd : k % 2 = 1)
    (hqt : h.q < h.t)
    (hqTwo : 2 ≤ h.q) :
    False := by
  have hBound :=
    h.odd_q_ge_two_internal_depth_bound hk hn hkOdd hqt hqTwo
  exact h.odd_q_ge_two_internal_finite_sieve
    hk hn hkOdd hqt hqTwo hBound

end Mersenne
end Collatz3
