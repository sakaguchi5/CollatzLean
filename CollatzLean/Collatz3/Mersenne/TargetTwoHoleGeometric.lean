import CollatzLean.Collatz3.Mersenne.TargetTwoHolePhase
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring


/-!
# Collatz3 Mersenne: target-two-hole の geometric reduction

`TargetTwoHolePhase` の三つの phase を、それぞれ base `2^n` の幾何和方程式へ持ち上げる。

* wrapped:
  `2*3^k + G_q + G_u = 2^(r+1) G_t`, `q<u<=t`。
* split-forward:
  `3^k + G_q + 2^r G_u = 2^(r+1) G_t`, `q<=u<=t`。
* split-reverse:
  同じ geometric equation だが `u<q<=t`。

split の二型を分けるのは、二つの cut の順序を後段の 2-adic theorem でそのまま読めるようにするため。
-/

namespace Collatz3
namespace Mersenne

/-- wrapped phase の exact geometric data。 -/
structure TargetTwoHoleWrappedGeometricData
    (k n r L a b : ℕ) : Type where
  q : ℕ
  u : ℕ
  t : ℕ
  q_pos : 0 < q
  q_lt_u : q < u
  u_le_t : u ≤ t
  a_phase_eq : a + r + 1 = n * q
  b_phase_eq : b + r + 1 = n * u
  length_eq : L = n * t
  equation :
    2 * 3 ^ k + targetGeomSum (2 ^ n) q + targetGeomSum (2 ^ n) u =
      2 ^ (r + 1) * targetGeomSum (2 ^ n) t

/-- split phase で、先に並ぶ hole `a` が shifted phase を持つ data。 -/
structure TargetTwoHoleSplitForwardGeometricData
    (k n r L a b : ℕ) : Type where
  q : ℕ
  u : ℕ
  t : ℕ
  q_pos : 0 < q
  u_pos : 0 < u
  q_le_u : q ≤ u
  u_le_t : u ≤ t
  a_phase_eq : a + r = n * q
  b_phase_eq : b = n * u
  length_eq : L = n * t + 1
  equation :
    3 ^ k + targetGeomSum (2 ^ n) q +
        2 ^ r * targetGeomSum (2 ^ n) u =
      2 ^ (r + 1) * targetGeomSum (2 ^ n) t

/-- split phase で、後ろの hole `b` が shifted phase を持つ data。 -/
structure TargetTwoHoleSplitReverseGeometricData
    (k n r L a b : ℕ) : Type where
  q : ℕ
  u : ℕ
  t : ℕ
  q_pos : 0 < q
  u_pos : 0 < u
  u_lt_q : u < q
  q_le_t : q ≤ t
  b_phase_eq : b + r = n * q
  a_phase_eq : a = n * u
  length_eq : L = n * t + 1
  equation :
    3 ^ k + targetGeomSum (2 ^ n) q +
        2 ^ r * targetGeomSum (2 ^ n) u =
      2 ^ (r + 1) * targetGeomSum (2 ^ n) t

/-- geometric sum の整数版 `G_m(x)(x-1)=x^m-1`。 -/
private theorem targetTwo_geom_int
    (x m : ℕ)
    (hx : 1 ≤ x) :
    ((targetGeomSum x m : ℕ) : ℤ) * ((x : ℤ) - 1) =
      (x : ℤ) ^ m - 1 := by
  have hNat : targetGeomSum x m * (x - 1) = x ^ m - 1 := by
    unfold targetGeomSum
    exact geom_sum_mul_of_one_le hx m
  have hPowOne : 1 ≤ x ^ m := Nat.one_le_pow m x (by omega)
  have hCast := congrArg (fun z : ℕ => (z : ℤ)) hNat
  simp only [Nat.cast_mul, Nat.cast_sub hx, Nat.cast_one,
    Nat.cast_pow, Nat.cast_sub hPowOne] at hCast
  exact hCast

/-- wrapped divisibility phase から exact geometric data を構成する。 -/
def TargetTwoHoleEquation.wrappedGeometricData
    {k n r L a b : ℕ}
    (hn4 : 4 ≤ n)
    (hr : r = 1 ∨ r = 2)
    (ha0 : 0 < a)
    (hab : a < b)
    (hbL : b < L)
    (hPhase : n ∣ L ∧ n ∣ a + r + 1 ∧ n ∣ b + r + 1)
    (hEq : TargetTwoHoleEquation k n r L a b) :
    TargetTwoHoleWrappedGeometricData k n r L a b := by
  let q : ℕ := (a + r + 1) / n
  let u : ℕ := (b + r + 1) / n
  let t : ℕ := L / n
  have hnPos : 0 < n := by omega
  have hrlt : r < n := by
    rcases hr with rfl | rfl <;> omega
  have hr1lt : r + 1 < n := by
    rcases hr with rfl | rfl <;> omega
  have hq : a + r + 1 = n * q := by
    dsimp [q]
    exact (Nat.mul_div_cancel' hPhase.2.1).symm
  have hu : b + r + 1 = n * u := by
    dsimp [u]
    exact (Nat.mul_div_cancel' hPhase.2.2).symm
  have ht : L = n * t := by
    dsimp [t]
    exact (Nat.mul_div_cancel' hPhase.1).symm
  have hqPos : 0 < q := by
    by_contra hNot
    have hq0 : q = 0 := Nat.eq_zero_of_not_pos hNot
    rw [hq0, Nat.mul_zero] at hq
    omega
  have hqLtU : q < u := by
    have hMul : n * q < n * u := by
      rw [← hq, ← hu]
      omega
    exact (Nat.mul_lt_mul_left hnPos).mp hMul
  have huLeT : u ≤ t := by
    have hlt : b + r + 1 < L + n := by omega
    rw [hu, ht] at hlt
    have hlt' : n * u < n * (t + 1) := by
      simpa [Nat.mul_succ] using hlt
    exact Nat.lt_succ_iff.mp ((Nat.mul_lt_mul_left hnPos).mp hlt')
  refine ⟨q, u, t, hqPos, hqLtU, huLeT, hq, hu, ht, ?_⟩
  let x : ℕ := 2 ^ n
  have hxTwo : 2 ≤ x := by
    dsimp [x]
    have h := Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) (by omega : 1 ≤ n)
    norm_num at h ⊢
    exact h
  have hxOne : 1 ≤ x := by omega
  have hGeomQ := targetTwo_geom_int x q hxOne
  have hGeomU := targetTwo_geom_int x u hxOne
  have hGeomT := targetTwo_geom_int x t hxOne
  have hPowL : (2 : ℤ) ^ L = (x : ℤ) ^ t := by
    rw [ht]
    dsimp [x]
    rw [pow_mul]
  have hPowA :
      (x : ℤ) ^ q =
        2 * (2 : ℤ) ^ r * (2 : ℤ) ^ a := by
    calc
      (x : ℤ) ^ q = (2 : ℤ) ^ (n * q) := by
        dsimp [x]
        rw [pow_mul]
      _ = (2 : ℤ) ^ (a + r + 1) := by rw [← hq]
      _ = (2 : ℤ) ^ a * (2 : ℤ) ^ r * 2 := by
        rw [pow_succ, pow_add]
      _ = 2 * (2 : ℤ) ^ r * (2 : ℤ) ^ a := by ring
  have hPowB :
      (x : ℤ) ^ u =
        2 * (2 : ℤ) ^ r * (2 : ℤ) ^ b := by
    calc
      (x : ℤ) ^ u = (2 : ℤ) ^ (n * u) := by
        dsimp [x]
        rw [pow_mul]
      _ = (2 : ℤ) ^ (b + r + 1) := by rw [← hu]
      _ = (2 : ℤ) ^ b * (2 : ℤ) ^ r * 2 := by
        rw [pow_succ, pow_add]
      _ = 2 * (2 : ℤ) ^ r * (2 : ℤ) ^ b := by ring
  have hEqZ := hEq
  unfold TargetTwoHoleEquation at hEqZ
  change
      (3 : ℤ) ^ k * ((x : ℤ) - 1) =
        (2 : ℤ) ^ r *
          ((2 : ℤ) ^ L - 1 - (2 : ℤ) ^ a - (2 : ℤ) ^ b) + 1 at hEqZ
  rw [hPowL] at hEqZ
  have hExpanded :
      2 * (3 : ℤ) ^ k * ((x : ℤ) - 1) =
        2 * (2 : ℤ) ^ r * ((x : ℤ) ^ t - 1) -
          (x : ℤ) ^ q - (x : ℤ) ^ u + 2 := by
    rw [hPowA, hPowB]
    linear_combination 2 * hEqZ
  have hGeomTScaled :
      (2 : ℤ) ^ (r + 1) * (targetGeomSum x t : ℕ) * ((x : ℤ) - 1) =
        (2 : ℤ) ^ (r + 1) * ((x : ℤ) ^ t - 1) := by
    calc
      (2 : ℤ) ^ (r + 1) * (targetGeomSum x t : ℕ) * ((x : ℤ) - 1) =
          (2 : ℤ) ^ (r + 1) *
            ((targetGeomSum x t : ℕ) * ((x : ℤ) - 1)) := by ring
      _ = (2 : ℤ) ^ (r + 1) * ((x : ℤ) ^ t - 1) := by
        rw [hGeomT]
  have hMain :
      (2 * (3 : ℤ) ^ k +
          (targetGeomSum x q : ℕ) +
          (targetGeomSum x u : ℕ)) * ((x : ℤ) - 1) =
        (2 : ℤ) ^ (r + 1) *
          (targetGeomSum x t : ℕ) * ((x : ℤ) - 1) := by
    rw [add_mul, add_mul, hGeomQ, hGeomU, hGeomTScaled, pow_succ]
    linear_combination hExpanded
  have hxNe : (x : ℤ) - 1 ≠ 0 := by
    have hxGt : (1 : ℤ) < x := by exact_mod_cast hxTwo
    omega
  have hCancel :
      2 * (3 : ℤ) ^ k +
          (targetGeomSum x q : ℕ) + (targetGeomSum x u : ℕ) =
        (2 : ℤ) ^ (r + 1) * (targetGeomSum x t : ℕ) := by
    apply mul_right_cancel₀ hxNe
    simpa [mul_assoc] using hMain
  exact_mod_cast hCancel

/-- split-forward divisibility phase から exact geometric data を構成する。 -/
def TargetTwoHoleEquation.splitForwardGeometricData
    {k n r L a b : ℕ}
    (hn4 : 4 ≤ n)
    (hr : r = 1 ∨ r = 2)
    (ha0 : 0 < a)
    (hab : a < b)
    (hbL : b < L)
    (hPhase : n ∣ L - 1 ∧ n ∣ a + r ∧ n ∣ b)
    (hEq : TargetTwoHoleEquation k n r L a b) :
    TargetTwoHoleSplitForwardGeometricData k n r L a b := by
  let q : ℕ := (a + r) / n
  let u : ℕ := b / n
  let t : ℕ := (L - 1) / n
  have hnPos : 0 < n := by omega
  have hrPos : 0 < r := by rcases hr with rfl | rfl <;> omega
  have hrlt : r < n := by rcases hr with rfl | rfl <;> omega
  have hq : a + r = n * q := by
    dsimp [q]
    exact (Nat.mul_div_cancel' hPhase.2.1).symm
  have hu : b = n * u := by
    dsimp [u]
    exact (Nat.mul_div_cancel' hPhase.2.2).symm
  have hLsub : L - 1 = n * t := by
    dsimp [t]
    exact (Nat.mul_div_cancel' hPhase.1).symm
  have hLPos : 1 ≤ L := by omega
  have ht : L = n * t + 1 := by
    omega
  have hqPos : 0 < q := by
    by_contra hNot
    have hq0 : q = 0 := Nat.eq_zero_of_not_pos hNot
    rw [hq0, Nat.mul_zero] at hq
    omega
  have huPos : 0 < u := by
    by_contra hNot
    have hu0 : u = 0 := Nat.eq_zero_of_not_pos hNot
    rw [hu0, Nat.mul_zero] at hu
    omega
  have hqLeU : q ≤ u := by
    by_contra hNot
    have huq : u < q := by omega
    have hMulLe : n * (u + 1) ≤ n * q :=
      Nat.mul_le_mul_left n (by omega)
    have hMulLt : n * q < n * (u + 1) := by
      rw [Nat.mul_succ, ← hq, ← hu]
      omega
    omega
  have huLeT : u ≤ t := by
    by_contra hNot
    have htu : t < u := by omega
    have hMulLe : n * t + n ≤ b := by
      calc
        n * t + n = n * (t + 1) := by ring
        _ ≤ n * u := Nat.mul_le_mul_left n (by omega)
        _ = b := hu.symm
    rw [ht] at hbL
    omega
  refine ⟨q, u, t, hqPos, huPos, hqLeU, huLeT, hq, hu, ht, ?_⟩
  let x : ℕ := 2 ^ n
  have hxTwo : 2 ≤ x := by
    dsimp [x]
    have h := Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) (by omega : 1 ≤ n)
    norm_num at h ⊢
    exact h
  have hxOne : 1 ≤ x := by omega
  have hGeomQ := targetTwo_geom_int x q hxOne
  have hGeomU := targetTwo_geom_int x u hxOne
  have hGeomT := targetTwo_geom_int x t hxOne
  have hPowL : (2 : ℤ) ^ L = 2 * (x : ℤ) ^ t := by
    rw [ht, pow_add, pow_mul]
    dsimp [x]
    ring
  have hPowQ :
      (x : ℤ) ^ q = (2 : ℤ) ^ r * (2 : ℤ) ^ a := by
    calc
      (x : ℤ) ^ q = (2 : ℤ) ^ (n * q) := by
        dsimp [x]
        rw [pow_mul]
      _ = (2 : ℤ) ^ (a + r) := by rw [← hq]
      _ = (2 : ℤ) ^ a * (2 : ℤ) ^ r := by rw [pow_add]
      _ = (2 : ℤ) ^ r * (2 : ℤ) ^ a := by ring
  have hPowU : (x : ℤ) ^ u = (2 : ℤ) ^ b := by
    calc
      (x : ℤ) ^ u = (2 : ℤ) ^ (n * u) := by
        dsimp [x]
        rw [pow_mul]
      _ = (2 : ℤ) ^ b := by rw [← hu]
  have hEqZ := hEq
  unfold TargetTwoHoleEquation at hEqZ
  change
      (3 : ℤ) ^ k * ((x : ℤ) - 1) =
        (2 : ℤ) ^ r *
          ((2 : ℤ) ^ L - 1 - (2 : ℤ) ^ a - (2 : ℤ) ^ b) + 1 at hEqZ
  rw [hPowL] at hEqZ
  have hExpanded :
      (3 : ℤ) ^ k * ((x : ℤ) - 1) =
        2 * (2 : ℤ) ^ r * (x : ℤ) ^ t - (2 : ℤ) ^ r -
          (x : ℤ) ^ q - (2 : ℤ) ^ r * (x : ℤ) ^ u + 1 := by
    rw [hPowQ, hPowU]
    linear_combination hEqZ
  have hGeomUScaled :
      ((2 : ℤ) ^ r * (targetGeomSum x u : ℕ)) * ((x : ℤ) - 1) =
        (2 : ℤ) ^ r * ((x : ℤ) ^ u - 1) := by
    calc
      ((2 : ℤ) ^ r * (targetGeomSum x u : ℕ)) * ((x : ℤ) - 1) =
          (2 : ℤ) ^ r *
            ((targetGeomSum x u : ℕ) * ((x : ℤ) - 1)) := by ring
      _ = (2 : ℤ) ^ r * ((x : ℤ) ^ u - 1) := by
        rw [hGeomU]
  have hGeomTScaled :
      (2 : ℤ) ^ (r + 1) * (targetGeomSum x t : ℕ) * ((x : ℤ) - 1) =
        (2 : ℤ) ^ (r + 1) * ((x : ℤ) ^ t - 1) := by
    calc
      (2 : ℤ) ^ (r + 1) * (targetGeomSum x t : ℕ) * ((x : ℤ) - 1) =
          (2 : ℤ) ^ (r + 1) *
            ((targetGeomSum x t : ℕ) * ((x : ℤ) - 1)) := by ring
      _ = (2 : ℤ) ^ (r + 1) * ((x : ℤ) ^ t - 1) := by
        rw [hGeomT]
  have hMain :
      ((3 : ℤ) ^ k + (targetGeomSum x q : ℕ) +
          (2 : ℤ) ^ r * (targetGeomSum x u : ℕ)) * ((x : ℤ) - 1) =
        (2 : ℤ) ^ (r + 1) *
          (targetGeomSum x t : ℕ) * ((x : ℤ) - 1) := by
    rw [add_mul, add_mul, hGeomQ, hGeomUScaled, hGeomTScaled, pow_succ]
    linear_combination hExpanded
  have hxNe : (x : ℤ) - 1 ≠ 0 := by
    have hxGt : (1 : ℤ) < x := by exact_mod_cast hxTwo
    omega
  have hCancel :
      (3 : ℤ) ^ k + (targetGeomSum x q : ℕ) +
          (2 : ℤ) ^ r * (targetGeomSum x u : ℕ) =
        (2 : ℤ) ^ (r + 1) * (targetGeomSum x t : ℕ) := by
    apply mul_right_cancel₀ hxNe
    simpa [mul_assoc] using hMain
  exact_mod_cast hCancel

/-- split-reverse divisibility phase から exact geometric data を構成する。 -/
def TargetTwoHoleEquation.splitReverseGeometricData
    {k n r L a b : ℕ}
    (hn4 : 4 ≤ n)
    (hr : r = 1 ∨ r = 2)
    (ha0 : 0 < a)
    (hab : a < b)
    (hbL : b < L)
    (hPhase : n ∣ L - 1 ∧ n ∣ b + r ∧ n ∣ a)
    (hEq : TargetTwoHoleEquation k n r L a b) :
    TargetTwoHoleSplitReverseGeometricData k n r L a b := by
  let q : ℕ := (b + r) / n
  let u : ℕ := a / n
  let t : ℕ := (L - 1) / n
  have hnPos : 0 < n := by omega
  have hrPos : 0 < r := by rcases hr with rfl | rfl <;> omega
  have hr1lt : r + 1 < n := by rcases hr with rfl | rfl <;> omega
  have hq : b + r = n * q := by
    dsimp [q]
    exact (Nat.mul_div_cancel' hPhase.2.1).symm
  have hu : a = n * u := by
    dsimp [u]
    exact (Nat.mul_div_cancel' hPhase.2.2).symm
  have hLsub : L - 1 = n * t := by
    dsimp [t]
    exact (Nat.mul_div_cancel' hPhase.1).symm
  have ht : L = n * t + 1 := by omega
  have hqPos : 0 < q := by
    by_contra hNot
    have hq0 : q = 0 := Nat.eq_zero_of_not_pos hNot
    rw [hq0, Nat.mul_zero] at hq
    omega
  have huPos : 0 < u := by
    by_contra hNot
    have hu0 : u = 0 := Nat.eq_zero_of_not_pos hNot
    rw [hu0, Nat.mul_zero] at hu
    omega
  have huLtQ : u < q := by
    have hMul : n * u < n * q := by
      rw [← hu, ← hq]
      omega
    exact (Nat.mul_lt_mul_left hnPos).mp hMul
  have hqLeT : q ≤ t := by
    have hlt : b + r < L + r := by omega
    rw [hq, ht] at hlt
    have hlt' : n * q < n * (t + 1) := by
      simp only [Nat.mul_succ]
      omega
    exact Nat.lt_succ_iff.mp ((Nat.mul_lt_mul_left hnPos).mp hlt')
  refine ⟨q, u, t, hqPos, huPos, huLtQ, hqLeT, hq, hu, ht, ?_⟩
  let x : ℕ := 2 ^ n
  have hxTwo : 2 ≤ x := by
    dsimp [x]
    have h := Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) (by omega : 1 ≤ n)
    norm_num at h ⊢
    exact h
  have hxOne : 1 ≤ x := by omega
  have hGeomQ := targetTwo_geom_int x q hxOne
  have hGeomU := targetTwo_geom_int x u hxOne
  have hGeomT := targetTwo_geom_int x t hxOne
  have hPowL : (2 : ℤ) ^ L = 2 * (x : ℤ) ^ t := by
    rw [ht, pow_add, pow_mul]
    dsimp [x]
    ring
  have hPowQ :
      (x : ℤ) ^ q = (2 : ℤ) ^ r * (2 : ℤ) ^ b := by
    calc
      (x : ℤ) ^ q = (2 : ℤ) ^ (n * q) := by
        dsimp [x]
        rw [pow_mul]
      _ = (2 : ℤ) ^ (b + r) := by rw [← hq]
      _ = (2 : ℤ) ^ b * (2 : ℤ) ^ r := by rw [pow_add]
      _ = (2 : ℤ) ^ r * (2 : ℤ) ^ b := by ring
  have hPowU : (x : ℤ) ^ u = (2 : ℤ) ^ a := by
    calc
      (x : ℤ) ^ u = (2 : ℤ) ^ (n * u) := by
        dsimp [x]
        rw [pow_mul]
      _ = (2 : ℤ) ^ a := by rw [← hu]
  have hEqZ := hEq
  unfold TargetTwoHoleEquation at hEqZ
  change
      (3 : ℤ) ^ k * ((x : ℤ) - 1) =
        (2 : ℤ) ^ r *
          ((2 : ℤ) ^ L - 1 - (2 : ℤ) ^ a - (2 : ℤ) ^ b) + 1 at hEqZ
  rw [hPowL] at hEqZ
  have hExpanded :
      (3 : ℤ) ^ k * ((x : ℤ) - 1) =
        2 * (2 : ℤ) ^ r * (x : ℤ) ^ t - (2 : ℤ) ^ r -
          (x : ℤ) ^ q - (2 : ℤ) ^ r * (x : ℤ) ^ u + 1 := by
    rw [hPowQ, hPowU]
    linear_combination hEqZ
  have hGeomUScaled :
      ((2 : ℤ) ^ r * (targetGeomSum x u : ℕ)) * ((x : ℤ) - 1) =
        (2 : ℤ) ^ r * ((x : ℤ) ^ u - 1) := by
    calc
      ((2 : ℤ) ^ r * (targetGeomSum x u : ℕ)) * ((x : ℤ) - 1) =
          (2 : ℤ) ^ r *
            ((targetGeomSum x u : ℕ) * ((x : ℤ) - 1)) := by ring
      _ = (2 : ℤ) ^ r * ((x : ℤ) ^ u - 1) := by
        rw [hGeomU]
  have hGeomTScaled :
      (2 : ℤ) ^ (r + 1) * (targetGeomSum x t : ℕ) * ((x : ℤ) - 1) =
        (2 : ℤ) ^ (r + 1) * ((x : ℤ) ^ t - 1) := by
    calc
      (2 : ℤ) ^ (r + 1) * (targetGeomSum x t : ℕ) * ((x : ℤ) - 1) =
          (2 : ℤ) ^ (r + 1) *
            ((targetGeomSum x t : ℕ) * ((x : ℤ) - 1)) := by ring
      _ = (2 : ℤ) ^ (r + 1) * ((x : ℤ) ^ t - 1) := by
        rw [hGeomT]
  have hMain :
      ((3 : ℤ) ^ k + (targetGeomSum x q : ℕ) +
          (2 : ℤ) ^ r * (targetGeomSum x u : ℕ)) * ((x : ℤ) - 1) =
        (2 : ℤ) ^ (r + 1) *
          (targetGeomSum x t : ℕ) * ((x : ℤ) - 1) := by
    rw [add_mul, add_mul, hGeomQ, hGeomUScaled, hGeomTScaled, pow_succ]
    linear_combination hExpanded
  have hxNe : (x : ℤ) - 1 ≠ 0 := by
    have hxGt : (1 : ℤ) < x := by exact_mod_cast hxTwo
    omega
  have hCancel :
      (3 : ℤ) ^ k + (targetGeomSum x q : ℕ) +
          (2 : ℤ) ^ r * (targetGeomSum x u : ℕ) =
        (2 : ℤ) ^ (r + 1) * (targetGeomSum x t : ℕ) := by
    apply mul_right_cancel₀ hxNe
    simpa [mul_assoc] using hMain
  exact_mod_cast hCancel

/-- `n>=4` target-two-hole から三 geometric phase のどれかを直接取り出す。 -/
theorem TargetTwoHoleEquation.exists_geometricData
    {k n r L a b : ℕ}
    (hn4 : 4 ≤ n)
    (hr : r = 1 ∨ r = 2)
    (ha0 : 0 < a)
    (hab : a < b)
    (hbL : b < L)
    (hEq : TargetTwoHoleEquation k n r L a b) :
    Nonempty (TargetTwoHoleWrappedGeometricData k n r L a b) ∨
      Nonempty (TargetTwoHoleSplitForwardGeometricData k n r L a b) ∨
      Nonempty (TargetTwoHoleSplitReverseGeometricData k n r L a b) := by
  rcases hEq.mersenne_phase_dichotomy hn4 hr ha0 hab hbL with
    hWrapped | hForward | hReverse
  · exact Or.inl ⟨hEq.wrappedGeometricData hn4 hr ha0 hab hbL hWrapped⟩
  · exact Or.inr (Or.inl
      ⟨hEq.splitForwardGeometricData hn4 hr ha0 hab hbL hForward⟩)
  · exact Or.inr (Or.inr
      ⟨hEq.splitReverseGeometricData hn4 hr ha0 hab hbL hReverse⟩)

/-! ## 三 block normal forms -/

/--
二段階に分解された geometric block から共通部分を消去する。

  K + p(B + M) + qB = C((B + M) + T)

かつ p + q ≤ C なら

  K = (C - p - q)B + (C - p)M + CT.
-/
private theorem weighted_three_block_residual
    {K B M T p q C : ℕ}
    (hpq : p + q ≤ C)
    (hEq :
      K + p * (B + M) + q * B =
        C * ((B + M) + T)) :
    K =
      (C - p - q) * B +
        (C - p) * M +
        C * T := by
  have hp : p ≤ C := by
    omega
  have hCoeffB :
      (C - p - q) + p + q = C := by
    omega
  have hCoeffM :
      (C - p) + p = C := by
    omega
  have hRhs :
      C * ((B + M) + T) =
        ((C - p - q) * B +
          (C - p) * M +
          C * T) +
        (p * (B + M) + q * B) := by
    calc
      C * ((B + M) + T)
          = C * B + C * M + C * T := by
              ring
      _ =
          ((C - p - q) + p + q) * B +
            ((C - p) + p) * M +
            C * T := by
              rw [hCoeffB, hCoeffM]
      _ =
          ((C - p - q) * B +
            (C - p) * M +
            C * T) +
          (p * (B + M) + q * B) := by
              ring
  have hCancel :
      K + (p * (B + M) + q * B) =
        ((C - p - q) * B +
          (C - p) * M +
          C * T) +
        (p * (B + M) + q * B) := by
    calc
      K + (p * (B + M) + q * B)
          = K + p * (B + M) + q * B := by
              ring
      _ = C * ((B + M) + T) := hEq
      _ =
          ((C - p - q) * B +
            (C - p) * M +
            C * T) +
          (p * (B + M) + q * B) := hRhs
  exact Nat.add_right_cancel hCancel

/-- wrapped phase では `2*3^k` が三つの constant block に分かれる。 -/
theorem TargetTwoHoleWrappedGeometricData.baseBlock_normalForm
    {k n r L a b : ℕ}
    (h : TargetTwoHoleWrappedGeometricData k n r L a b) :
    2 * 3 ^ k =
      (2 ^ (r + 1) - 2) * targetGeomSum (2 ^ n) h.q +
      (2 ^ (r + 1) - 1) * (2 ^ n) ^ h.q *
        targetGeomSum (2 ^ n) (h.u - h.q) +
      2 ^ (r + 1) * (2 ^ n) ^ h.u *
        targetGeomSum (2 ^ n) (h.t - h.u) := by
  let x : ℕ := 2 ^ n
  let R2 : ℕ := 2 ^ (r + 1)
  have hqLeU : h.q ≤ h.u := Nat.le_of_lt h.q_lt_u
  have hqu : h.q + (h.u - h.q) = h.u := by
    exact Nat.add_sub_of_le hqLeU
  have hut : h.u + (h.t - h.u) = h.t := by
    exact Nat.add_sub_of_le h.u_le_t
  have hGu :
      targetGeomSum x h.u =
        targetGeomSum x h.q + x ^ h.q * targetGeomSum x (h.u - h.q) := by
    calc
      targetGeomSum x h.u = targetGeomSum x (h.q + (h.u - h.q)) := by rw [hqu]
      _ = _ := targetGeomSum_add x h.q (h.u - h.q)
  have hGt :
      targetGeomSum x h.t =
        targetGeomSum x h.u + x ^ h.u * targetGeomSum x (h.t - h.u) := by
    calc
      targetGeomSum x h.t = targetGeomSum x (h.u + (h.t - h.u)) := by rw [hut]
      _ = _ := targetGeomSum_add x h.u (h.t - h.u)
  have hR2 : 2 ≤ R2 := by
    dsimp [R2]
    have hp :=
      Nat.pow_le_pow_right
        (by norm_num : 0 < (2 : ℕ))
        (by omega : 1 ≤ r + 1)
    norm_num at hp ⊢
    exact hp
  have hEq := h.equation
  change
      2 * 3 ^ k +
          targetGeomSum x h.q +
          targetGeomSum x h.u =
        R2 * targetGeomSum x h.t at hEq
  -- 先に t→u、次に u→q の順で展開する。
  rw [hGt, hGu] at hEq
  have hpq : 1 + 1 ≤ R2 := by
    omega
  have hWeighted :
      2 * 3 ^ k +
          1 *
            (targetGeomSum x h.q +
              x ^ h.q *
                targetGeomSum x (h.u - h.q)) +
          1 * targetGeomSum x h.q =
        R2 *
          ((targetGeomSum x h.q +
              x ^ h.q *
                targetGeomSum x (h.u - h.q)) +
            x ^ h.u *
              targetGeomSum x (h.t - h.u)) := by
    calc
      2 * 3 ^ k +
            1 *
              (targetGeomSum x h.q +
                x ^ h.q *
                  targetGeomSum x (h.u - h.q)) +
            1 * targetGeomSum x h.q
          =
        2 * 3 ^ k +
          targetGeomSum x h.q +
          (targetGeomSum x h.q +
            x ^ h.q *
              targetGeomSum x (h.u - h.q)) := by
              ring
      _ =
        R2 *
          ((targetGeomSum x h.q +
              x ^ h.q *
                targetGeomSum x (h.u - h.q)) +
            x ^ h.u *
              targetGeomSum x (h.t - h.u)) := hEq
  have hResidual :=
    weighted_three_block_residual
      (K := 2 * 3 ^ k)
      (B := targetGeomSum x h.q)
      (M :=
        x ^ h.q *
          targetGeomSum x (h.u - h.q))
      (T :=
        x ^ h.u *
          targetGeomSum x (h.t - h.u))
      (p := 1)
      (q := 1)
      (C := R2)
      hpq
      hWeighted
  have hCoeff :
      R2 - 1 - 1 = R2 - 2 := by
    omega
  rw [hCoeff] at hResidual
  change
    2 * 3 ^ k =
      (R2 - 2) * targetGeomSum x h.q +
      (R2 - 1) * x ^ h.q *
        targetGeomSum x (h.u - h.q) +
      R2 * x ^ h.u *
        targetGeomSum x (h.t - h.u)
  simpa [mul_assoc] using hResidual

/-- split-forward では `3^k` が lower/middle/upper の三 block に分かれる。 -/
theorem TargetTwoHoleSplitForwardGeometricData.baseBlock_normalForm
    {k n r L a b : ℕ}
    (h : TargetTwoHoleSplitForwardGeometricData k n r L a b) :
    3 ^ k =
      (2 ^ r - 1) * targetGeomSum (2 ^ n) h.q +
      2 ^ r * (2 ^ n) ^ h.q * targetGeomSum (2 ^ n) (h.u - h.q) +
      2 ^ (r + 1) * (2 ^ n) ^ h.u * targetGeomSum (2 ^ n) (h.t - h.u) := by
  let x : ℕ := 2 ^ n
  let R : ℕ := 2 ^ r
  have hqu : h.q + (h.u - h.q) = h.u := by
    exact Nat.add_sub_of_le h.q_le_u
  have hut : h.u + (h.t - h.u) = h.t := by
    exact Nat.add_sub_of_le h.u_le_t
  have hGu := targetGeomSum_add x h.q (h.u - h.q)
  have hGt := targetGeomSum_add x h.u (h.t - h.u)
  rw [hqu] at hGu
  rw [hut] at hGt
  have hEq := h.equation
  change
      3 ^ k +
          targetGeomSum x h.q +
          R * targetGeomSum x h.u =
        2 ^ (r + 1) *
          targetGeomSum x h.t at hEq
  have hTwoR : 2 ^ (r + 1) = 2 * R := by
    dsimp [R]
    rw [pow_succ]
    ring
  -- t→u→q の順で展開。
  rw [hTwoR, hGt, hGu] at hEq
  have hROne : 1 ≤ R := by
    have hRPos : 0 < R := by
      dsimp [R]
      exact Nat.pow_pos (by norm_num)
    omega
  have hpq : R + 1 ≤ 2 * R := by
    omega
  have hWeighted :
      3 ^ k +
          R *
            (targetGeomSum x h.q +
              x ^ h.q *
                targetGeomSum x (h.u - h.q)) +
          1 * targetGeomSum x h.q =
        (2 * R) *
          ((targetGeomSum x h.q +
              x ^ h.q *
                targetGeomSum x (h.u - h.q)) +
            x ^ h.u *
              targetGeomSum x (h.t - h.u)) := by
    calc
      3 ^ k +
            R *
              (targetGeomSum x h.q +
                x ^ h.q *
                  targetGeomSum x (h.u - h.q)) +
            1 * targetGeomSum x h.q
          =
        3 ^ k +
          targetGeomSum x h.q +
          R *
            (targetGeomSum x h.q +
              x ^ h.q *
                targetGeomSum x (h.u - h.q)) := by
              ring
      _ =
        (2 * R) *
          ((targetGeomSum x h.q +
              x ^ h.q *
                targetGeomSum x (h.u - h.q)) +
            x ^ h.u *
              targetGeomSum x (h.t - h.u)) := hEq
  have hResidual :=
    weighted_three_block_residual
      (K := 3 ^ k)
      (B := targetGeomSum x h.q)
      (M :=
        x ^ h.q *
          targetGeomSum x (h.u - h.q))
      (T :=
        x ^ h.u *
          targetGeomSum x (h.t - h.u))
      (p := R)
      (q := 1)
      (C := 2 * R)
      hpq
      hWeighted
  have hCoeffLow :
      2 * R - R - 1 = R - 1 := by
    omega
  have hCoeffMid :
      2 * R - R = R := by
    omega
  rw [hCoeffLow, hCoeffMid] at hResidual
  rw [hTwoR]
  change
    3 ^ k =
      (R - 1) * targetGeomSum x h.q +
      R * x ^ h.q *
        targetGeomSum x (h.u - h.q) +
      2 * R * x ^ h.u *
        targetGeomSum x (h.t - h.u)
  simpa [mul_assoc] using hResidual

/-- split-reverse では middle digit が `2^(r+1)-1` になる。 -/
theorem TargetTwoHoleSplitReverseGeometricData.baseBlock_normalForm
    {k n r L a b : ℕ}
    (h : TargetTwoHoleSplitReverseGeometricData k n r L a b) :
    3 ^ k =
      (2 ^ r - 1) * targetGeomSum (2 ^ n) h.u +
      (2 ^ (r + 1) - 1) * (2 ^ n) ^ h.u *
        targetGeomSum (2 ^ n) (h.q - h.u) +
      2 ^ (r + 1) * (2 ^ n) ^ h.q *
        targetGeomSum (2 ^ n) (h.t - h.q) := by
  let x : ℕ := 2 ^ n
  let R : ℕ := 2 ^ r
  have huLeQ : h.u ≤ h.q := Nat.le_of_lt h.u_lt_q
  have huq : h.u + (h.q - h.u) = h.q := by
    exact Nat.add_sub_of_le huLeQ
  have hqt : h.q + (h.t - h.q) = h.t := by
    exact Nat.add_sub_of_le h.q_le_t
  have hGq := targetGeomSum_add x h.u (h.q - h.u)
  have hGt := targetGeomSum_add x h.q (h.t - h.q)
  rw [huq] at hGq
  rw [hqt] at hGt
  have hEq := h.equation
  change
      3 ^ k +
          targetGeomSum x h.q +
          R * targetGeomSum x h.u =
        2 ^ (r + 1) *
          targetGeomSum x h.t at hEq
  have hTwoR : 2 ^ (r + 1) = 2 * R := by
    dsimp [R]
    rw [pow_succ]
    ring
  -- t→q、さらに q→u と展開する。
  rw [hTwoR, hGt, hGq] at hEq
  have hROne : 1 ≤ R := by
    have hRPos : 0 < R := by
      dsimp [R]
      exact Nat.pow_pos (by norm_num)
    omega
  have hpq : 1 + R ≤ 2 * R := by
    omega
  have hWeighted :
      3 ^ k +
          1 *
            (targetGeomSum x h.u +
              x ^ h.u *
                targetGeomSum x (h.q - h.u)) +
          R * targetGeomSum x h.u =
        (2 * R) *
          ((targetGeomSum x h.u +
              x ^ h.u *
                targetGeomSum x (h.q - h.u)) +
            x ^ h.q *
              targetGeomSum x (h.t - h.q)) := by
    simpa [one_mul] using hEq
  have hResidual :=
    weighted_three_block_residual
      (K := 3 ^ k)
      (B := targetGeomSum x h.u)
      (M :=
        x ^ h.u *
          targetGeomSum x (h.q - h.u))
      (T :=
        x ^ h.q *
          targetGeomSum x (h.t - h.q))
      (p := 1)
      (q := R)
      (C := 2 * R)
      hpq
      hWeighted
  have hCoeffLow :
      2 * R - 1 - R = R - 1 := by
    omega
  rw [hCoeffLow] at hResidual
  rw [hTwoR]
  change
    3 ^ k =
      (R - 1) * targetGeomSum x h.u +
      (2 * R - 1) * x ^ h.u *
        targetGeomSum x (h.q - h.u) +
      2 * R * x ^ h.q *
        targetGeomSum x (h.t - h.q)
  simpa [mul_assoc] using hResidual

end Mersenne
end Collatz3
