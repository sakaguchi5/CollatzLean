import CollatzLean.Collatz2.Geometry.CriticalFerrersThreeAdicAnchor
import CollatzLean.Collatz2.Geometry.InformationBoundary
import Mathlib.Data.Int.Lemmas

/-!
# Collatz2 Geometry: critical Ferrers code の下端・上端・幅

valid word では各 exponent が 1 以上なので、長さ `r` の affine translation の最小値は
all-one word の値

  3^r - 2^r

である。

FirstCrossing では既存 `criticalAffineConst r` が上端を与える。
そこで

  criticalFerrersWidth r
    = criticalAffineConst r - (3^r - 2^r)

を定義する。
-/

namespace Collatz2
namespace Word

/-- critical Ferrers code の valid 側の普遍下端。 -/
def criticalFerrersLower (r : ℕ) : ℕ :=
  3 ^ r - 2 ^ r

/-- critical roof と valid 下端の間の全幅。 -/
def criticalFerrersWidth (r : ℕ) : ℕ :=
  criticalAffineConst r - criticalFerrersLower r

/-- `2^n <= 3^n`。Nat subtraction を安全に扱うための小補題。 -/
theorem twoPow_le_threePow (n : ℕ) : 2 ^ n ≤ 3 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pow_succ, pow_succ]
      omega

/-- valid word の `affineConst` は all-one word の値 `3^r - 2^r` 以上。 -/
theorem criticalFerrersLower_le_affineConst_of_valid
    {w : Word}
    (hV : Valid w) :
    criticalFerrersLower (oddSteps w) ≤ affineConst w := by
  induction w with
  | nil =>
      simp [criticalFerrersLower, oddSteps, affineConst]
  | cons e w ih =>
      have hePos : 0 < e := hV e (by simp)
      have heOne : 1 ≤ e := by omega
      have hVTail : Valid w := by
        intro x hx
        exact hV x (by simp [hx])
      have hIH := ih hVTail
      let n := oddSteps w
      have h23 : 2 ^ n ≤ 3 ^ n := twoPow_le_threePow n
      have hSubAdd : 3 ^ n - 2 ^ n + 2 ^ n = 3 ^ n :=
        Nat.sub_add_cancel h23
      have hTwoLe : 2 ≤ 2 ^ e := by
        calc
          2 = 2 ^ (1 : ℕ) := by norm_num
          _ ≤ 2 ^ e :=
            Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) heOne
      have hMul :
          2 * (3 ^ n - 2 ^ n) ≤ 2 ^ e * affineConst w := by
        exact Nat.mul_le_mul hTwoLe (by simpa [criticalFerrersLower, n] using hIH)
      have hTarget :
          3 ^ (n + 1) - 2 ^ (n + 1) =
            3 ^ n + 2 * (3 ^ n - 2 ^ n) := by
        rw [pow_succ, pow_succ]
        omega
      rw [oddSteps_cons]
      change criticalFerrersLower (n + 1) ≤ affineConst (e :: w)
      rw [criticalFerrersLower, hTarget, affineConst_cons]
      exact Nat.add_le_add_left hMul (3 ^ n)

/--
同じ長さ `r >= 2` の valid FirstCrossing word の `affineConst` は modulo 4 で同じ。
より強く、各 `affineConst` は長さだけで決まる共通項 + `4*t` の形になる。
-/
theorem affineConst_eq_common_mod_four
    {w : Word}
    (hV : Valid w)
    (hF : FirstCrossing w)
    (hLen : 2 ≤ oddSteps w) :
    ∃ t : ℕ,
      affineConst w =
        3 ^ (oddSteps w - 1) +
          2 * 3 ^ (oddSteps w - 2) + 4 * t := by
  cases w with
  | nil => simp [oddSteps] at hLen
  | cons e0 w =>
      cases w with
      | nil => simp [oddSteps] at hLen
      | cons e1 tail =>
          have he0Pos : 0 < e0 := hV e0 (by simp)
          have he1Pos : 0 < e1 := hV e1 (by simp)
          have hDepth1 : prefixTwoDepth (e0 :: e1 :: tail) 1 = 1 :=
            prefixTwoDepth_one_eq_one_of_valid_firstCrossing hV hF (by simp [oddSteps])
          have he0 : e0 = 1 := by
            simpa [prefixTwoDepth, twoSteps] using hDepth1
          subst e0
          cases e1 with
          | zero => omega
          | succ d =>
              refine ⟨2 ^ d * affineConst tail, ?_⟩
              simp only [affineConst_cons, oddSteps_cons]
              simp [oddSteps, pow_succ]
              ring

/-- 同じ長さ 2 以上の valid FirstCrossing codes の差は 4 の倍数。 -/
theorem four_dvd_affineConst_diff_of_valid_firstCrossing
    {u v : Word}
    (hVu : Valid u)
    (hVv : Valid v)
    (hFu : FirstCrossing u)
    (hFv : FirstCrossing v)
    (hp : oddSteps u = oddSteps v)
    (hLen : 2 ≤ oddSteps u) :
    ((4 : ℤ) ∣ (affineConst u : ℤ) - (affineConst v : ℤ)) := by
  obtain ⟨a, ha⟩ := affineConst_eq_common_mod_four hVu hFu hLen
  have hLenV : 2 ≤ oddSteps v := by simpa [← hp] using hLen
  obtain ⟨b, hb⟩ := affineConst_eq_common_mod_four hVv hFv hLenV
  refine ⟨(a : ℤ) - (b : ℤ), ?_⟩
  rw [ha, hb, hp]
  push_cast
  ring

/--
下端 `L` と上端 `U` の間にある二自然数の差の絶対値は `U-L` 以下。
-/
theorem natAbs_sub_le_width
    {A B L U : ℕ}
    (hLA : L ≤ A)
    (hLB : L ≤ B)
    (hAU : A ≤ U)
    (hBU : B ≤ U) :
    Int.natAbs ((A : ℤ) - (B : ℤ)) ≤ U - L := by
  have hA' : A - L ≤ U - L := by omega
  have hB' : B - L ≤ U - L := by omega
  have hAbs := Int.natAbs_coe_sub_coe_le_of_le hA' hB'
  have hEq :
      ((A : ℤ) - (B : ℤ)) =
        ((A - L : ℕ) : ℤ) - ((B - L : ℕ) : ℤ) := by
    rw [Nat.cast_sub hLA, Nat.cast_sub hLB]
    ring
  rw [hEq]
  exact hAbs

/-- valid FirstCrossing codes の差は critical width 以下。 -/
theorem affineConst_diff_natAbs_le_criticalFerrersWidth
    {u v : Word}
    (hVu : Valid u)
    (hVv : Valid v)
    (hFu : FirstCrossing u)
    (hFv : FirstCrossing v)
    (hp : oddSteps u = oddSteps v) :
    Int.natAbs ((affineConst u : ℤ) - (affineConst v : ℤ)) ≤
      criticalFerrersWidth (oddSteps u) := by
  let r := oddSteps u
  let L := criticalFerrersLower r
  let U := criticalAffineConst r
  have hLu : L ≤ affineConst u := by
    simpa [L, r] using criticalFerrersLower_le_affineConst_of_valid hVu
  have hLv : L ≤ affineConst v := by
    have := criticalFerrersLower_le_affineConst_of_valid hVv
    simpa [L, r, hp] using this
  have hUu : affineConst u ≤ U := by
    simpa [U, r] using affineConst_le_criticalAffineConst_of_firstCrossing hFu
  have hUv : affineConst v ≤ U := by
    have := affineConst_le_criticalAffineConst_of_firstCrossing hFv
    simpa [U, r, hp] using this
  simpa [criticalFerrersWidth, L, U, r] using
    natAbs_sub_le_width hLu hLv hUu hUv

end Word
end Collatz2
