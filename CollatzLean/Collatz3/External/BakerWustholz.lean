import Mathlib.NumberTheory.Height.NumberField
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.NumberTheory.Height.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Baker--Wüstholz の引用定理と有理数上の薄い補助層

このファイルで trusted input として置くのは、Baker--Wüstholz [BW93] のうち
現在の `Collatz3/Mersenne` が実際に使う三対数特殊化だけである。

repo 内の実際の利用形は常に

* 数体は `ℚ`
* 対数は三個
* 基数は `(2, α, 3)`（`α` は正の有理数）
* 係数は `(a, ε, -k)`（`a,k : ℕ`, `ε = ±1`）

である。そのため、任意の数体・任意個数の対数・任意係数を量化する
一般 Baker--Wüstholz 定理を axiom としては置かない。

`C` と `modifiedHeight` は通常の定義であり axiom ではない。
高さ評価、実対数への特殊化、具体定数評価はすべて mathlib から証明する。
-/

open Complex

namespace BakerWustholz

/-- Baker--Wüstholz の明示定数
`C(n,d)=18 (n+1)! n^(n+1) (32d)^(n+2) log(2nd)`。 -/
noncomputable def C (n d : ℕ) : ℝ :=
  18 * (n + 1).factorial * (n : ℝ) ^ (n + 1) *
    (32 * (d : ℝ)) ^ (n + 2) * Real.log (2 * n * d)

/-- Baker--Wüstholz の modified height。定義であって trusted input ではない。 -/
noncomputable def modifiedHeight
    {K : Type*} [Field K] [NumberField K] (φ : K →+* ℂ) (α : K) : ℝ :=
  let d : ℝ := Module.finrank ℚ K
  max (Height.logHeight₁ α / d) (max (‖Complex.log (φ α)‖ / d) (1 / d))

/--
repo で実際に使う三対数線形形式

`a log 2 + ε log α - k log 3`

を明示する。`α` は後の axiom では正の有理数、`ε` は `±1` に限定する。
-/
noncomputable def threeLogRatForm
    (a k : ℕ) (ε : ℤ) (α : ℚ) : ℝ :=
  (a : ℝ) * Real.log 2 +
    (ε : ℝ) * Real.log (α : ℝ) -
    (k : ℝ) * Real.log 3

/--
Baker--Wüstholz [BW93] のうち、この repository が実際に必要とする特殊化。

基数を `(2, α, 3)`、数体を `ℚ`、対数の個数を `3`、
係数を `(a, ε, -k)` (`ε = ±1`) に固定している。

これがこのファイルに残す唯一の trusted mathematical input である。
Collatz 固有の式、Mersenne block、depth bound、有限 sieve は仮定しない。
-/
axiom linearForms_logs_three_rat
    {a k B : ℕ}
    (α : ℚ) (hα : 0 < α)
    (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (hB : 2 ≤ B)
    (haB : a ≤ B)
    (hkB : k ≤ B)
    (hΛ_ne_zero : threeLogRatForm a k ε α ≠ 0) :
    -(BakerWustholz.C 3 1 * max (Real.log B) 1 *
        (BakerWustholz.modifiedHeight (Rat.castHom ℂ) (2 : ℚ) *
          BakerWustholz.modifiedHeight (Rat.castHom ℂ) α *
          BakerWustholz.modifiedHeight (Rat.castHom ℂ) (3 : ℚ)))
      ≤ Real.log |threeLogRatForm a k ε α|

end BakerWustholz

namespace Collatz3
namespace External
namespace BakerWustholzQ

/-- `log 2 > 0`。 -/
lemma log_two_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)

/-- `log 3 > 0`。 -/
lemma log_three_pos : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)

/-- `log 2 ≤ 1`。 -/
lemma log_two_le_one : Real.log 2 ≤ 1 := by
  exact le_trans Real.log_two_lt_d9.le (by norm_num)

/-- `log 3 ≤ 2`。 -/
lemma log_three_le_two : Real.log 3 ≤ 2 := by
  exact le_trans Real.log_three_lt_d9.le (by norm_num)

/-- `d=1` の Baker--Wüstholz 定数は非負。 -/
lemma C_one_nonneg (n : ℕ) : 0 ≤ BakerWustholz.C n 1 := by
  unfold BakerWustholz.C
  simp only [Nat.cast_one]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hlog : (0 : ℝ) ≤ Real.log (2 * (n : ℝ) * 1) :=
      Real.log_nonneg (by nlinarith [hn1])
    exact mul_nonneg (by positivity) hlog

/-- `d=1` での modified height の展開。 -/
lemma modifiedHeight_rat (q : ℚ) :
    BakerWustholz.modifiedHeight (Rat.castHom ℂ) q
      = max (Height.logHeight₁ q) (max ‖Complex.log ((q : ℂ))‖ 1) := by
  unfold BakerWustholz.modifiedHeight
  rw [eq_ratCast]
  norm_num [Module.finrank_self]

/-- 正の有理数では複素 log の norm は実 log の絶対値。 -/
lemma norm_log_ratCast {q : ℚ} (hq : 0 < q) :
    ‖Complex.log ((q : ℂ))‖ = |Real.log ((q : ℝ))| := by
  have hcast : ((q : ℚ) : ℂ) = (((q : ℝ)) : ℂ) := by
    push_cast
    ring
  rw [hcast, ← Complex.ofReal_log (by exact_mod_cast hq.le : (0 : ℝ) ≤ (q : ℝ)),
    Complex.norm_real, Real.norm_eq_abs]

/-- `h'(2) ≤ 1`。 -/
lemma mh_two : BakerWustholz.modifiedHeight (Rat.castHom ℂ) (2 : ℚ) ≤ 1 := by
  rw [modifiedHeight_rat, norm_log_ratCast (by norm_num)]
  have h1 : Height.logHeight₁ (2 : ℚ) = Real.log 2 := by
    simpa using Rat.logHeight₁_natCast 2
  have h2 : |Real.log (((2 : ℚ) : ℝ))| = Real.log 2 := by
    rw [show ((2 : ℚ) : ℝ) = 2 by norm_num,
      abs_of_nonneg (Real.log_nonneg (by norm_num))]
  rw [h1, h2]
  exact max_le log_two_le_one (max_le log_two_le_one le_rfl)

/-- `h'(3) ≤ log 3`。 -/
lemma mh_three :
    BakerWustholz.modifiedHeight (Rat.castHom ℂ) (3 : ℚ) ≤ Real.log 3 := by
  rw [modifiedHeight_rat, norm_log_ratCast (by norm_num)]
  have h1 : Height.logHeight₁ (3 : ℚ) = Real.log 3 := by
    simpa using Rat.logHeight₁_natCast 3
  have h2 : |Real.log (((3 : ℚ) : ℝ))| = Real.log 3 := by
    rw [show ((3 : ℚ) : ℝ) = 3 by norm_num,
      abs_of_nonneg (Real.log_nonneg (by norm_num))]
  have hOne : (1 : ℝ) ≤ Real.log 3 := by
    exact le_trans (by norm_num : (1 : ℝ) ≤ 1.0986122885) Real.log_three_gt_d9.le
  rw [h1, h2]
  exact max_le le_rfl (max_le le_rfl hOne)

/-- 正整数 `u` に対し `h'(u) ≤ max(log u,1)`。 -/
lemma mh_intCast {u : ℤ} (hu : 1 ≤ u) :
    BakerWustholz.modifiedHeight (Rat.castHom ℂ) ((u : ℤ) : ℚ)
      ≤ max (Real.log ((u : ℤ) : ℝ)) 1 := by
  have huQ : (0 : ℚ) < (u : ℚ) := by
    exact_mod_cast lt_of_lt_of_le one_pos hu
  have huR : (1 : ℝ) ≤ ((u : ℤ) : ℝ) := by
    exact_mod_cast hu
  rw [modifiedHeight_rat, norm_log_ratCast huQ]
  have h1 :
      Height.logHeight₁ ((u : ℤ) : ℚ) =
        Real.log ((u : ℤ) : ℝ) := by
    have hu0 : (0 : ℤ) ≤ u := by omega
    have hune : u ≠ 0 := by omega
    have hnat : u.natAbs ≠ 0 :=
      Int.natAbs_ne_zero.mpr hune
    let : NeZero u.natAbs := ⟨hnat⟩
    have huZ : (u.natAbs : ℤ) = u :=
      Int.natAbs_of_nonneg hu0
    have huQnat :
        ((u.natAbs : ℕ) : ℚ) = (u : ℚ) := by
      simpa using congrArg (fun z : ℤ => (z : ℚ)) huZ
    have huRnat :
        ((u.natAbs : ℕ) : ℝ) = ((u : ℤ) : ℝ) := by
      simpa using congrArg (fun z : ℤ => (z : ℝ)) huZ
    calc
      Height.logHeight₁ ((u : ℤ) : ℚ)
          = Height.logHeight₁ ((u.natAbs : ℕ) : ℚ) := by
              rw [huQnat]
      _ = Real.log ((u.natAbs : ℕ) : ℝ) :=
        Rat.logHeight₁_natCast u.natAbs
      _ = Real.log ((u : ℤ) : ℝ) := by
        rw [huRnat]
  rw [h1]
  have hlog : 0 ≤ Real.log ((u : ℤ) : ℝ) :=
    Real.log_nonneg huR
  have hcast :
      (((u : ℤ) : ℚ) : ℝ) = ((u : ℤ) : ℝ) := by
    norm_num
  rw [hcast, abs_of_nonneg hlog]
  simp only [le_max_iff, Std.le_refl, true_or, sup_of_le_right]

/-- modified height は非負。 -/
lemma modifiedHeight_nonneg (q : ℚ) :
    0 ≤ BakerWustholz.modifiedHeight (Rat.castHom ℂ) q := by
  rw [modifiedHeight_rat]
  exact le_trans zero_le_one (le_max_of_le_right (le_max_right _ _))

/--
特殊化した Baker--Wüstholz axiom を、正の実線形形式へ使いやすく包装する。

この定理自身は axiom ではなく、`linearForms_logs_three_rat` と
`|Λ| = Λ` (`Λ>0`) から直接従う。
-/
theorem log_threeForm_rat_ge
    {a k B : ℕ}
    {α : ℚ} (hα : 0 < α)
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hB : 2 ≤ B)
    (haB : a ≤ B)
    (hkB : k ≤ B)
    {Λ : ℝ}
    (hΛeq : Λ = BakerWustholz.threeLogRatForm a k ε α)
    (hΛPos : 0 < Λ) :
    -(BakerWustholz.C 3 1 * max (Real.log B) 1 *
        (BakerWustholz.modifiedHeight (Rat.castHom ℂ) (2 : ℚ) *
          BakerWustholz.modifiedHeight (Rat.castHom ℂ) α *
          BakerWustholz.modifiedHeight (Rat.castHom ℂ) (3 : ℚ)))
      ≤ Real.log Λ := by
  have hFormPos : 0 < BakerWustholz.threeLogRatForm a k ε α := by
    rw [← hΛeq]
    exact hΛPos
  have hBW :=
    BakerWustholz.linearForms_logs_three_rat
      (a := a) (k := k) (B := B) α hα ε hε hB haB hkB hFormPos.ne'
  rw [abs_of_pos hFormPos] at hBW
  rw [← hΛeq] at hBW
  exact hBW

/-- A/C 用の粗い安全定数: `C(3,1) * log 3 ≤ 8·10^12`。 -/
lemma C_three_mul_log_three_le :
    BakerWustholz.C 3 1 * Real.log 3 ≤ (8000000000000 : ℝ) := by
  have h6 : Real.log 6 ≤ 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)]
    linarith [log_two_le_one, log_three_le_two]
  have h3nonneg : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have h6nonneg : (0 : ℝ) ≤ Real.log 6 := Real.log_nonneg (by norm_num)
  have hprod : Real.log 6 * Real.log 3 ≤ 3 * 2 :=
    mul_le_mul h6 log_three_le_two h3nonneg (by norm_num)
  have hC :
      BakerWustholz.C 3 1 = (1174136684544 : ℝ) * Real.log 6 := by
    norm_num [BakerWustholz.C]
  rw [hC]
  nlinarith

end BakerWustholzQ
end External
end Collatz3
