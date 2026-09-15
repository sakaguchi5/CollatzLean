import CollatzLean.Collatz3.Critical.WordFerrers
import CollatzLean.Collatz3.Core.WordTransfer
import Mathlib.Tactic.Ring

/-!
# Collatz3 Bridge: Ferrers 1-cell move と affineConst の exact weight

2021 年論文 Lemma 21 の有限局所交換を、現在の odd-only exponent word に直接書き直す。

binary parity word の `01 -> 10` に対応する odd-only 側の局所操作は

`u ++ [a+1, b] ++ v  ->  u ++ [a, b+1] ++ v`

である。すなわち一個の 2 除算を左 block から右 block へ移す。
`a,b>0` なら両側は正 exponent の局所 word であり、odd-step 数と total two-depth は保存される。

この操作で `affineConst` は exact に

`2^(twoSteps u + a) * 3^(oddSteps v)`

だけ減少する。

この値を 1 Ferrers cell の affine weight と読む。
無限 word、real completion、2進 completion は一切使わない純粋な有限 word 算術である。
-/

namespace Collatz3
namespace Word

/--
1 Ferrers cell に対応する affine numerator の exact weight。

prefix `u` の後で指数 `a+1` から一個の 2 除算を右へ移し、
suffix `v` が後ろに続く場合の重み。
-/
def ferrersCellAffineWeight
    (u v : Word)
    (a : ℕ) : ℕ :=
  2 ^ (twoSteps u + a) * 3 ^ oddSteps v

/--
1個の 2 除算を右隣 block へ移す weighted Ferrers step。

`wBefore = u ++ [a+1,b] ++ v`
`wAfter  = u ++ [a,b+1] ++ v`

で、`weight` はその 1-cell affine weight。
-/
def FerrersCellStep
    (wBefore wAfter : Word)
    (weight : ℕ) : Prop :=
  ∃ (u v : Word) (a b : ℕ),
    0 < a ∧
    0 < b ∧
    wBefore = u ++ [a + 1, b] ++ v ∧
    wAfter = u ++ [a, b + 1] ++ v ∧
    weight = ferrersCellAffineWeight u v a

/-- 2文字だけの局所交換では affineConst の差は exactly `2^a`。 -/
theorem affineConst_pair_move_one_right
    (a b : ℕ) :
    affineConst [a + 1, b] = affineConst [a, b + 1] + 2 ^ a := by
  simp [pow_succ]
  ring

/--
prefix `u` の後ろで 1-cell move すると、その差は `2^(twoSteps u + a)`。
-/
theorem affineConst_prefix_pair_move_one_right
    (u : Word)
    (a b : ℕ) :
    affineConst (u ++ [a + 1, b]) =
      affineConst (u ++ [a, b + 1]) + 2 ^ (twoSteps u + a) := by
  rw [affineConst_append u [a + 1, b], affineConst_append u [a, b + 1]]
  have hLocal := affineConst_pair_move_one_right a b
  simp only [oddSteps_cons, oddSteps_nil]
  rw [hLocal, pow_add]
  ring

/--
任意 suffix `v` を含む 1-cell move の exact affineConst 差。

`B(before) = B(after) + 2^(twoSteps u+a) * 3^(oddSteps v)`。
-/
theorem affineConst_ferrersCellMove
    (u v : Word)
    (a b : ℕ) :
    affineConst (u ++ [a + 1, b] ++ v) =
      affineConst (u ++ [a, b + 1] ++ v) +
        ferrersCellAffineWeight u v a := by
  rw [affineConst_append (u ++ [a + 1, b]) v,
    affineConst_append (u ++ [a, b + 1]) v]
  rw [affineConst_prefix_pair_move_one_right u a b]
  have hTwo :
      twoSteps (u ++ [a + 1, b]) =
        twoSteps (u ++ [a, b + 1]) := by
    simp
    omega
  rw [hTwo]
  unfold ferrersCellAffineWeight
  ring

/-- weighted Ferrers step は odd-step 数と total two-depth を保存する。 -/
theorem FerrersCellStep.length_depth_eq
    {wBefore wAfter : Word}
    {weight : ℕ}
    (h : FerrersCellStep wBefore wAfter weight) :
    oddSteps wBefore = oddSteps wAfter ∧
      twoSteps wBefore = twoSteps wAfter := by
  rcases h with ⟨u, v, a, b, _ha, _hb, rfl, rfl, _hc⟩
  constructor <;> simp
  omega

/--
weighted Ferrers step は affineConst を exact に `weight` だけ減らす。
-/
theorem FerrersCellStep.affineConst_eq
    {wBefore wAfter : Word}
    {weight : ℕ}
    (h : FerrersCellStep wBefore wAfter weight) :
    affineConst wBefore = affineConst wAfter + weight := by
  rcases h with ⟨u, v, a, b, _ha, _hb, rfl, rfl, rfl⟩
  exact affineConst_ferrersCellMove u v a b

end Word
end Collatz3
