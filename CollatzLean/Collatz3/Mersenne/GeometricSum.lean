import CollatzLean.Collatz3.Mersenne.TargetOneHoleGeometric
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring


/-!
# Collatz3 Mersenne: geometric sum 共通補題

`targetGeomSum` 自体は既存 API を維持するため `TargetOneHoleGeometric` に置いたままにし、
one-hole / two-hole の後段で重複していた局所補題だけをこの層へ公開する。

今後 `TargetOneHoleLocks`, `TargetOneHoleValuation`, `TargetOneHoleGcd`,
`TargetTwoHoleGcd`, `TargetTwoHoleValuation` はこの薄い API を共通に使える。
-/

namespace Collatz3
namespace Mersenne

/-- 正の長さの geometric sum は正。 -/
theorem targetGeomSum_pos
    {x t : ℕ}
    (ht : 0 < t) :
    0 < targetGeomSum x t := by
  obtain ⟨s, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
  rw [targetGeomSum_succ]
  omega

/-- 長さについて geometric sum は単調。 -/
theorem targetGeomSum_mono_length
    {x a b : ℕ}
    (hab : a ≤ b) :
    targetGeomSum x a ≤ targetGeomSum x b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [targetGeomSum_add]
  omega

/-- base が 2 以上なら `G_t(x) < x^t`。 -/
theorem targetGeomSum_lt_pow
    {x t : ℕ}
    (hx : 2 ≤ x) :
    targetGeomSum x t < x ^ t := by
  induction t with
  | zero =>
      simp [targetGeomSum]
  | succ t ih =>
      rw [targetGeomSum_succ, pow_succ]
      have hOneLt : 1 < x := by omega
      have hSuccLe : targetGeomSum x t + 1 ≤ x ^ t := by
        omega
      calc
        x * targetGeomSum x t + 1
            < x * targetGeomSum x t + x := Nat.add_lt_add_left hOneLt _
        _ = x * (targetGeomSum x t + 1) := by ring
        _ ≤ x * x ^ t := Nat.mul_le_mul_left x hSuccLe
        _ = x ^ t * x := by ring

/-- 正長の geometric sum は最上位項の 2 倍より小さい。 -/
theorem targetGeomSum_lt_two_mul_last
    {x t : ℕ}
    (hx : 2 ≤ x)
    (ht : 0 < t) :
    targetGeomSum x t < 2 * x ^ (t - 1) := by
  obtain ⟨s, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
  have hPrev := targetGeomSum_lt_pow (x := x) (t := s) hx
  have hG1 : targetGeomSum x 1 = 1 := by
    simp [targetGeomSum]
  change targetGeomSum x (s + 1) < 2 * x ^ s
  rw [targetGeomSum_add, hG1, mul_one]
  omega

/-- even base の正長 geometric sum は odd。 -/
theorem targetGeomSum_odd_of_even_base
    {x t : ℕ}
    (hx : Even x)
    (ht : 0 < t) :
    Odd (targetGeomSum x t) := by
  obtain ⟨s, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
  change Odd (targetGeomSum x (s + 1))
  rw [targetGeomSum_succ]
  rcases hx with ⟨a, ha⟩
  refine ⟨a * targetGeomSum x s, ?_⟩
  rw [ha]
  ring

/-- `q≤t` に対応する標準 tail 分解。 -/
theorem targetGeomSum_split
    {x q t : ℕ}
    (hqt : q ≤ t) :
    targetGeomSum x t =
      targetGeomSum x q +
        x ^ q * targetGeomSum x (t - q) := by
  have hDecomp : q + (t - q) = t := by omega
  calc
    targetGeomSum x t =
        targetGeomSum x (q + (t - q)) := by rw [hDecomp]
    _ = _ := targetGeomSum_add x q (t - q)

/-- `x≥2`, `d≥2` なら geometric sum は 1 より大きい。 -/
theorem one_lt_targetGeomSum
    {x d : ℕ}
    (hx : 2 ≤ x)
    (hd : 2 ≤ d) :
    1 < targetGeomSum x d := by
  have hdEq : d = 2 + (d - 2) := by omega
  rw [hdEq, targetGeomSum_add]
  have hG2 : targetGeomSum x 2 = x + 1 := by
    simp [targetGeomSum]
  rw [hG2]
  omega

/-- `G_t(x)(x-1)=x^t-1` の自然数版。 -/
theorem targetGeomSum_mul_sub_one
    {x t : ℕ}
    (hx : 1 ≤ x) :
    targetGeomSum x t * (x - 1) = x ^ t - 1 := by
  unfold targetGeomSum
  exact geom_sum_mul_of_one_le hx t

end Mersenne
end Collatz3
