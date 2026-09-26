import CollatzLean.Collatz4.Dynamics.Merge


/-!
# Collatz4.Dynamics.ThreePowerFamily

`3^n - 1` から始まる累積 2 指数軌道の局所合流則。

M=7 固有の候補数や時刻には依存しない。特に、指数 `n` が奇数なら

`3^n - 1  ->  3^(n+1) - 1`

が累積写像 1 回で正確に成立することを証明する。
この規則は、多数の開始指数が同じ後続軌道へ合流する最初の一般的な原因になる。
-/

namespace Collatz4.Dynamics

/-- `1 + 3 + ... + 3^(n-1)` を除算なしで表す再帰。 -/
def threeGeom : ℕ → ℕ
  | 0 => 0
  | n + 1 => 3 * threeGeom n + 1

/-- `2 * (1+3+...+3^(n-1)) + 1 = 3^n`。 -/
theorem two_mul_threeGeom_add_one (n : ℕ) :
    2 * threeGeom n + 1 = 3 ^ n := by
  induction n with
  | zero => simp [threeGeom]
  | succ n ih =>
      rw [threeGeom, pow_succ]
      rw [← ih]
      ring

/-- 幾何和の通常形 `2*S_n = 3^n - 1`。 -/
theorem two_mul_threeGeom (n : ℕ) :
    2 * threeGeom n = 3 ^ n - 1 := by
  have h := two_mul_threeGeom_add_one n
  omega

/-- `threeGeom n` の偶奇は `n` の偶奇と一致する。 -/
theorem threeGeom_mod_two (n : ℕ) :
    threeGeom n % 2 = n % 2 := by
  induction n with
  | zero =>
      simp [threeGeom]
  | succ n ih =>
      rw [threeGeom]
      omega

/-- 奇数指数に対応する幾何和は奇数。 -/
theorem threeGeom_odd_mod_two (k : ℕ) :
    threeGeom (2 * k + 1) % 2 = 1 := by
  rw [threeGeom_mod_two]
  simp [Nat.add_mod]

/-- 奇数指数 `2k+1` では `v₂(3^(2k+1)-1)=1`。 -/
theorem v2_threePow_sub_one_odd (k : ℕ) :
    padicValNat 2 (3 ^ (2 * k + 1) - 1) = 1 := by
  let g : ℕ := threeGeom (2 * k + 1)
  have hfactor : 3 ^ (2 * k + 1) - 1 = 2 * g := by
    dsimp [g]
    symm
    exact two_mul_threeGeom (2 * k + 1)
  have hmod : g % 2 = 1 := by
    dsimp [g]
    exact threeGeom_odd_mod_two k
  have hg0 : g ≠ 0 := by
    intro hg
    rw [hg] at hmod
    norm_num at hmod
  have hnot : ¬ 2 ∣ g := by
    intro hd
    have hz : g % 2 = 0 := Nat.mod_eq_zero_of_dvd hd
    omega
  have hv0 : padicValNat 2 g = 0 := by
    rw [padicValNat.eq_zero_iff]
    exact Or.inr (Or.inr hnot)
  rw [hfactor]
  have hv :=
    padicValNat_base_mul
      (p := 2) (n := g) (by norm_num : 1 < (2 : ℕ)) hg0
  omega

/--
一般条件版。
`v₂(3^n-1)=1` なら、累積写像 1 回で `3^(n+1)-1` へ正確に移る。
-/
theorem accumulatedStep_threePow_sub_one_of_v2_eq_one
    {n : ℕ}
    (hv : padicValNat 2 (3 ^ n - 1) = 1) :
    accumulatedStep (3 ^ n - 1) = 3 ^ (n + 1) - 1 := by
  unfold accumulatedStep accumulatedV2
  rw [hv, pow_succ]
  norm_num
  have hp : 0 < 3 ^ n := by positivity
  omega

/--
奇数指数では上の条件が自動的に成立するため、
`3^(2k+1)-1` は 1 step で `3^(2k+2)-1` に合流する。
-/
theorem accumulatedStep_threePow_sub_one_odd (k : ℕ) :
    accumulatedStep (3 ^ (2 * k + 1) - 1) =
      3 ^ (2 * k + 2) - 1 := by
  have hv := v2_threePow_sub_one_odd k
  have h := accumulatedStep_threePow_sub_one_of_v2_eq_one
    (n := 2 * k + 1) hv
  simpa [show 2 * k + 1 + 1 = 2 * k + 2 by omega] using h

/--
奇数指数側の開始点を 1 step 進めた後は、次の偶数指数側の開始点と永久に同じ軌道を通る。
-/
theorem accumulatedRun_threePow_odd_merge (k s : ℕ) :
    accumulatedRun (s + 1) (3 ^ (2 * k + 1) - 1) =
      accumulatedRun s (3 ^ (2 * k + 2) - 1) := by
  rw [show s + 1 = 1 + s by omega]
  rw [accumulatedRun_add]
  simp only [accumulatedRun_succ, accumulatedRun_zero]
  rw [accumulatedStep_threePow_sub_one_odd]

end Collatz4.Dynamics
