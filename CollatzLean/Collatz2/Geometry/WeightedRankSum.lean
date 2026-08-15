import CollatzLean.Collatz2.Geometry.RankUnit
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Collatz2 Geometry: translation path の weighted-rank sum

Small-Residue FirstCrossing Principle に向けた rank-unit 側の総和化。

FirstCrossing word `w` に対し

  p = oddSteps w,
  H = twoSteps w,
  d_k = H*k - p*h_k,
  G = 2^H - 3^p

とする。primitive exponent pair から得た rank unit `u` は

  u^p = 2,
  u^H = 3              (mod G)

を満たす。

各 normalized translation monomial

  M_k = 2^h_k * 3^(p-k)

には既に

  u^d_k * M_k = 3^p

がある。このファイルではそれを全 `0 <= k < p` で足し上げ、

  3*B = 3^p * sum_k u^(-d_k)       (mod G)

を一つの theorem にする。
-/

namespace Collatz2
namespace Word

/-- cons word の cut 0 の normalized monomial。 -/
@[simp] theorem normalizedCutTerm_cons_zero
    (e : ℕ)
    (w : Word) :
    normalizedCutTerm (e :: w) 0 = 3 * 3 ^ oddSteps w := by
  unfold normalizedCutTerm prefixTwoDepth
  simp only [List.take_zero, twoSteps_nil, pow_zero, one_mul, oddSteps_cons,
    Nat.sub_zero]
  rw [pow_succ]
  ring

/-- cons word の positive cut は tail cut の `2^e` 倍。 -/
theorem normalizedCutTerm_cons_succ
    (e : ℕ)
    (w : Word)
    (k : ℕ) :
    normalizedCutTerm (e :: w) (k + 1) =
      2 ^ e * normalizedCutTerm w k := by
  have hSub :
      oddSteps (e :: w) - (k + 1) = oddSteps w - k := by
    simp only [oddSteps_cons]
    omega
  unfold normalizedCutTerm prefixTwoDepth
  rw [hSub]
  simp only [List.take_succ_cons, twoSteps_cons]
  rw [pow_add]
  ring

/--
normalized cut monomial を全 proper cut `0,...,p-1` で足すと exact に `3*B`。

これは

  B = 3^(p-1) + 2^h_1 3^(p-2) + ... + 2^h_(p-1)

を rank 側で扱いやすい normalization にしたもの。
-/
theorem sum_normalizedCutTerm_eq_three_mul_affineConst
    (w : Word) :
    Finset.sum (Finset.range (oddSteps w)) (fun k => normalizedCutTerm w k) =
      3 * affineConst w := by
  induction w with
  | nil =>
      simp [oddSteps, affineConst]
  | cons e w ih =>
      rw [oddSteps_cons, Finset.sum_range_succ']
      rw [normalizedCutTerm_cons_zero]
      simp_rw [normalizedCutTerm_cons_succ]
      rw [← Finset.mul_sum, ih]
      rw [affineConst_cons]
      ring

/-- rank unit の inverse weight `u^(-d_k)`。 -/
def inverseRankWeight
    {w : Word}
    (R : RankUnitData w)
    (k : ℕ) : ZMod (terminalGap w) :=
  (↑(R.unit⁻¹) : ZMod (terminalGap w)) ^ chordRank w k

/-- 全 proper cut の inverse rank weights の和。 -/
def weightedRankSum
    {w : Word}
    (R : RankUnitData w) : ZMod (terminalGap w) :=
  Finset.sum (Finset.range (oddSteps w)) (fun k => inverseRankWeight R k)

namespace RankUnitData

/--
`k=0` を含む全 proper cut について、normalized monomial を inverse rank weight へ解く。

  M_k = 3^p * u^(-d_k)   (mod G).
-/
theorem normalizedCutTerm_eq_threePow_mul_inverseRankWeight
    {w : Word}
    (R : RankUnitData w)
    (hF : FirstCrossing w)
    {k : ℕ}
    (hkLt : k < oddSteps w) :
    ((normalizedCutTerm w k : ℕ) : ZMod (terminalGap w)) =
      ((3 ^ oddSteps w : ℕ) : ZMod (terminalGap w)) *
        inverseRankWeight R k := by
  by_cases hk0 : k = 0
  · subst k
    simp [inverseRankWeight, normalizedCutTerm, prefixTwoDepth, chordRank]
  · have hkPos : 0 < k := Nat.pos_of_ne_zero hk0
    have hCert := R.cut_certificate hF hkPos hkLt
    let u : ZMod (terminalGap w) := ↑R.unit
    let v : ZMod (terminalGap w) := ↑(R.unit⁻¹)
    have huv : v * u = 1 := by
      dsimp [u, v]
      simp
    have hCert' :
        u ^ chordRank w k *
            ((normalizedCutTerm w k : ℕ) : ZMod (terminalGap w)) =
          ((3 ^ oddSteps w : ℕ) : ZMod (terminalGap w)) := by
      simpa [u] using hCert
    calc
      ((normalizedCutTerm w k : ℕ) : ZMod (terminalGap w))
          = (v * u) ^ chordRank w k *
              ((normalizedCutTerm w k : ℕ) : ZMod (terminalGap w)) := by
                rw [huv]
                simp
      _ = v ^ chordRank w k *
            (u ^ chordRank w k *
              ((normalizedCutTerm w k : ℕ) : ZMod (terminalGap w))) := by
            rw [mul_pow]
            ring
      _ = v ^ chordRank w k *
            ((3 ^ oddSteps w : ℕ) : ZMod (terminalGap w)) := by
            rw [hCert']
      _ = ((3 ^ oddSteps w : ℕ) : ZMod (terminalGap w)) *
            v ^ chordRank w k := by
            ring
      _ = ((3 ^ oddSteps w : ℕ) : ZMod (terminalGap w)) *
            inverseRankWeight R k := by
            simp [inverseRankWeight, v]

/--
translation path 全体の weighted-rank identity。

  3*B = 3^p * weightedRankSum    (mod G).
-/
theorem three_mul_affineConst_cast_eq_threePow_mul_weightedRankSum
    {w : Word}
    (R : RankUnitData w)
    (hF : FirstCrossing w) :
    (((3 * affineConst w : ℕ) : ZMod (terminalGap w))) =
      ((3 ^ oddSteps w : ℕ) : ZMod (terminalGap w)) *
        weightedRankSum R := by
  rw [← sum_normalizedCutTerm_eq_three_mul_affineConst]
  push_cast
  unfold weightedRankSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hTerm :=
    R.normalizedCutTerm_eq_threePow_mul_inverseRankWeight
      hF (Finset.mem_range.mp hk)
  push_cast at hTerm
  exact hTerm

/-- `3^p` を表す rank-unit 自身。cancel 用。 -/
def threePowUnit
    {w : Word}
    (R : RankUnitData w) : (ZMod (terminalGap w))ˣ :=
  R.unit ^ (twoSteps w * oddSteps w)

/-- `threePowUnit` の underlying value は `3^p`。 -/
theorem threePowUnit_coe
    {w : Word}
    (R : RankUnitData w) :
    (↑R.threePowUnit : ZMod (terminalGap w)) =
      ((3 ^ oddSteps w : ℕ) : ZMod (terminalGap w)) := by
  unfold threePowUnit
  change
    (↑R.unit : ZMod (terminalGap w)) ^
        (twoSteps w * oddSteps w) =
      ((3 ^ oddSteps w : ℕ) : ZMod (terminalGap w))
  rw [pow_mul, R.unit_pow_twoSteps]
  push_cast
  rfl

/-- `3^p` は rank-unit 由来の unit なので左から cancel できる。 -/
theorem cancel_threePow
    {w : Word}
    (R : RankUnitData w)
    {x y : ZMod (terminalGap w)}
    (hEq :
      ((3 ^ oddSteps w : ℕ) : ZMod (terminalGap w)) * x =
        ((3 ^ oddSteps w : ℕ) : ZMod (terminalGap w)) * y) :
    x = y := by
  let U := R.threePowUnit
  have hU :
      (↑U : ZMod (terminalGap w)) =
        ((3 ^ oddSteps w : ℕ) : ZMod (terminalGap w)) := by
    simpa [U] using R.threePowUnit_coe
  have hEq' :
      (↑U : ZMod (terminalGap w)) * x =
        (↑U : ZMod (terminalGap w)) * y := by
    simpa [hU] using hEq
  have hCancel :=
    congrArg
      (fun z : ZMod (terminalGap w) =>
        (↑(U⁻¹) : ZMod (terminalGap w)) * z)
      hEq'
  simpa [← mul_assoc] using hCancel

end RankUnitData
end Word
end Collatz2
