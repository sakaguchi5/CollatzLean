import Mathlib.NumberTheory.Height.NumberField
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.NumberTheory.Height.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Baker--Wüstholz の引用定理と有理数上の薄い補助層

A/C (`q=1`) を外部 package の仮定ではなく、既知の線形対数形定理から
直接閉じるために必要な最小部分だけを置く。

ここで `linearForms_logs` は Baker--Wüstholz [BW93] の主定理そのものを
引用定理として記録する。Collatz 固有の結論や `q=1` の不可能性を axiom として
置くものではない。

定数・modified height・有理数特殊化は Ralf Stephan の 2026 年の Lean
formalization `Aperiodicity-and-Subword-Complexity` の CC0 実装と同じ規約を使う。
-/

open Complex

namespace BakerWustholz

/-- Baker--Wüstholz の明示定数
`C(n,d)=18 (n+1)! n^(n+1) (32d)^(n+2) log(2nd)`。 -/
noncomputable def C (n d : ℕ) : ℝ :=
  18 * (n + 1).factorial * (n : ℝ) ^ (n + 1) *
    (32 * (d : ℝ)) ^ (n + 2) * Real.log (2 * n * d)

/-- Baker--Wüstholz の modified height。 -/
noncomputable def modifiedHeight
    {K : Type*} [Field K] [NumberField K] (φ : K →+* ℂ) (α : K) : ℝ :=
  let d : ℝ := Module.finrank ℚ K
  max (Height.logHeight₁ α / d) (max (‖Complex.log (φ α)‖ / d) (1 / d))

/--
Baker--Wüstholz [BW93] の線形対数形下界。

これは既知の外部数学定理そのものを引用する唯一の trusted input であり、
A/C や Collatz 固有の命題は仮定していない。
-/
axiom linearForms_logs
    {n : ℕ} (hn : 0 < n)
    {K : Type*} [Field K] [NumberField K] (φ : K →+* ℂ)
    (α : Fin n → K) (hα : ∀ i, α i ≠ 0)
    (b : Fin n → ℤ) {B : ℕ} (hB : 2 ≤ B) (hbB : ∀ i, (b i).natAbs ≤ B)
    (hΛ_ne_zero : (∑ i, (b i : ℂ) * Complex.log (φ (α i))) ≠ 0) :
    Real.log ‖∑ i, (b i : ℂ) * Complex.log (φ (α i))‖
      ≥ -(BakerWustholz.C n (Module.finrank ℚ K)
          * max (Real.log B) (1 / (Module.finrank ℚ K : ℝ))
          * ∏ i, BakerWustholz.modifiedHeight φ (α i))

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

/-- 正有理数の複素 principal log は実 log の cast。 -/
lemma complex_log_ratCast_pos {q : ℚ} (hq : 0 < q) :
    Complex.log ((Rat.castHom ℂ) q) = ((Real.log (q : ℝ) : ℝ) : ℂ) := by
  rw [eq_ratCast, show ((q : ℚ) : ℂ) = (((q : ℝ)) : ℂ) by push_cast; ring,
    ← Complex.ofReal_log (by exact_mod_cast hq.le)]

/--
Baker--Wüstholz を有理数の実線形形式へ包装した版。
-/
theorem log_linearForm_rat_ge {n : ℕ} (hn : 0 < n) (α : Fin n → ℚ)
    (hα : ∀ i, 0 < α i) (b : Fin n → ℤ) {B : ℕ} (hB : 2 ≤ B)
    (hbB : ∀ i, (b i).natAbs ≤ B) {Λ : ℝ}
    (hΛeq : Λ = ∑ i, (b i : ℝ) * Real.log (α i : ℝ)) (hΛ : Λ ≠ 0) :
    -(BakerWustholz.C n 1 * max (Real.log B) 1
        * ∏ i, BakerWustholz.modifiedHeight (Rat.castHom ℂ) (α i))
      ≤ Real.log Λ := by
  have hαne : ∀ i, α i ≠ 0 := fun i => (hα i).ne'
  have hsum :
      (∑ i, ((b i : ℂ) * Complex.log ((Rat.castHom ℂ) (α i)))) = ((Λ : ℝ) : ℂ) := by
    rw [hΛeq]
    push_cast
    exact Finset.sum_congr rfl fun i _ => by rw [complex_log_ratCast_pos (hα i)]
  have hΛneC :
      (∑ i, ((b i : ℂ) * Complex.log ((Rat.castHom ℂ) (α i)))) ≠ 0 := by
    rw [hsum]
    exact Complex.ofReal_ne_zero.mpr hΛ
  have hBW := BakerWustholz.linearForms_logs (n := n) hn
    (Rat.castHom ℂ) α hαne b (B := B) hB hbB hΛneC
  rw [hsum, Complex.norm_real, Real.norm_eq_abs, Real.log_abs,
    Module.finrank_self, Nat.cast_one] at hBW
  rw [show (1 : ℝ) / (1 : ℝ) = 1 by norm_num] at hBW
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
