import CollatzLean.Collatz2.Geometry.WeightedRankBaseline

/-!
# Collatz2 Geometry: direct rank-unit geometric inverse

primitive weighted-rank geometry では inverse unit `v=u⁻¹` の baseline と並行して、
direct unit `u` 自身の geometric sum も使える。

rank unit は

  u^p = 2

を満たすので

  (u-1) * (1 + u + ... + u^(p-1)) = 1.

また inverse baseline についても

  (1-v) * (2*baselineResidueSum) = 1

となる。current A の Ferrers inverse equation と同じ左因子を持つため、
後で inverse の一意性を使って exact closed form を得られる。
-/

namespace Collatz2
namespace Word

/-- rank unit `u` の underlying value。 -/
def directUnitValue
    {w : Word}
    (R : RankUnitData w) : ZMod (terminalGap w) :=
  (↑R.unit : ZMod (terminalGap w))

/-- direct unit の geometric residue sum `1+u+...+u^(p-1)`。 -/
def directGeometricResidueSum
    {w : Word}
    (R : RankUnitData w) : ZMod (terminalGap w) :=
  Finset.sum (Finset.range (oddSteps w))
    (fun r => directUnitValue R ^ r)

@[simp] theorem RankUnitData.directUnitValue_pow_oddSteps_eq_two
    {w : Word}
    (R : RankUnitData w) :
    directUnitValue R ^ oddSteps w =
      ((2 : ℕ) : ZMod (terminalGap w)) := by
  exact R.unit_pow_oddSteps

/-- `u*v=1`。 -/
theorem RankUnitData.directUnitValue_mul_inverseUnitValue_eq_one
    {w : Word}
    (R : RankUnitData w) :
    directUnitValue R * inverseUnitValue R = 1 := by
  unfold directUnitValue inverseUnitValue
  simp

private theorem direct_sub_one_mul_sum_range_pow
    {N : ℕ}
    (x : ZMod N)
    (p : ℕ) :
    (x - 1) * Finset.sum (Finset.range p) (fun r => x ^ r) =
      x ^ p - 1 := by
  induction p with
  | zero =>
      simp
  | succ p ih =>
      rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
      ring

/--
`u^p=2` から direct geometric sum は `(u-1)` の inverse。
-/
theorem RankUnitData.directUnitValue_sub_one_mul_directGeometricResidueSum_eq_one
    {w : Word}
    (R : RankUnitData w) :
    (directUnitValue R - 1) * directGeometricResidueSum R = 1 := by
  unfold directGeometricResidueSum
  rw [direct_sub_one_mul_sum_range_pow]
  rw [R.directUnitValue_pow_oddSteps_eq_two]
  ring

/--
primitive inverse baseline は `(1-v)` の inverse を `2*baseline` として与える。
-/
theorem RankUnitData.one_sub_inverseUnitValue_mul_two_mul_baselineResidueSum_eq_one
    {w : Word}
    (R : RankUnitData w)
    (hF : FirstCrossing w)
    (hcop : Nat.Coprime (twoSteps w) (oddSteps w)) :
    (1 - inverseUnitValue R) * (2 * baselineResidueSum R) = 1 := by
  have hBase :=
    R.inverseUnitValue_sub_one_mul_baselineResidueSum_eq_half_sub_one
      hF hcop
  have hHalfRaw := R.halfUnitValue_mul_two_eq_one
  have hHalf :
      2 * halfUnitValue R = 1 := by
    simpa [mul_comm] using hHalfRaw
  calc
    (1 - inverseUnitValue R) * (2 * baselineResidueSum R)
        = -2 * ((inverseUnitValue R - 1) * baselineResidueSum R) := by
            ring
    _ = -2 * (halfUnitValue R - 1) := by rw [hBase]
    _ = 2 - 2 * halfUnitValue R := by ring
    _ = 1 := by rw [hHalf]; ring

end Word
end Collatz2
