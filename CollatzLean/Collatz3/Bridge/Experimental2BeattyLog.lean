import CollatzLean.Collatz3.Bridge.Experimental2BeattyNatLog
import CollatzLean.Collatz3.Bridge.Experimental2Beatty
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Collatz3 Bridge: Beatty roof の実数対数 slope 同定

power-form で定義された `Critical.beattyIndex` を、実数対数

`Real.logb 2 3`

へ接続する analytic bridge。

証明順は次の通り。

1. `Nat.log` と `Real.logb` の floor bridge から
   `beattyIndex m = floor(m * log₂ 3)` を得る。
2. これを lower mechanical roof として Experimental2 に渡す。
3. power-form の strict lower inequality を対数へ移し、正幅では strict lower cell を得る。
4. floor formula と strictness を rational denominator で衝突させ、`log₂ 3` の無理数性を示す。
5. Experimental2 の slope 一意性により Beatty roof の canonical slope を `log₂ 3` と同定する。
6. 正規化後の slope を `log₂(3/2)` と同定し、最後に一歩 Beatty carry を
   irrational mechanical word の floor 差分として書く。

`Real.logb` 自体は noncomputable だが、新しい noncomputable definition は導入しない。
-/

namespace Collatz3
namespace Bridge

/--
Beatty index の実数 floor 表現。

`beattyIndex m = floor(m * log₂ 3)`。
-/
theorem beattyIndex_eq_natFloor_logb_two_three
    (m : ℕ) :
    Critical.beattyIndex m =
      ⌊(m : ℝ) * Real.logb 2 3⌋₊ := by
  calc
    Critical.beattyIndex m = Nat.log 2 (3 ^ m) :=
      beattyIndex_eq_natLog_two_threePow m
    _ = ⌊Real.logb 2 (((3 ^ m : ℕ) : ℝ))⌋₊ := by
      symm
      exact Real.natFloor_logb_natCast 2 (3 ^ m)
    _ = ⌊(m : ℝ) * Real.logb 2 3⌋₊ := by
      have hLog :
          Real.logb 2 (((3 ^ m : ℕ) : ℝ)) =
            (m : ℝ) * Real.logb 2 3 := by
        simpa using
          (Real.logb_pow (2 : ℝ) (3 : ℝ) m)
      rw [hLog]

/--
`beattyIndex` は slope `log₂ 3` の lower mechanical roof。

ここでは floor 公式を cell 条件へ戻しているだけであり、
unit-carry は追加仮定として使わない。
-/
theorem beattyIndex_isLowerMechanical_logb_two_three :
    Experimental2.IsLowerMechanicalRoof
      Critical.beattyIndex (Real.logb 2 3) := by
  intro n
  have hEq := beattyIndex_eq_natFloor_logb_two_three n
  have hLogNonneg : 0 ≤ Real.logb (2 : ℝ) 3 :=
    Real.logb_nonneg (by norm_num) (by norm_num)
  have hNonneg :
      0 ≤ (n : ℝ) * Real.logb 2 3 :=
    mul_nonneg (Nat.cast_nonneg n) hLogNonneg
  simpa [Experimental2.IsNatFloor] using
    ((Nat.floor_eq_iff hNonneg).1 hEq.symm)

/--
正の幅では Beatty roof は `m * log₂ 3` より strict に下にある。

power-form の `2^beattyIndex(m) < 3^m` を、base 2 の対数の strict monotonicity で移す。
この strictness は後続の irrationality 証明で boundary equality を排除する。
-/
theorem beattyIndex_lt_mul_logb_two_three
    {m : ℕ}
    (hm : 0 < m) :
    (Critical.beattyIndex m : ℝ) <
      (m : ℝ) * Real.logb 2 3 := by
  have hPowR :
      (((2 ^ Critical.beattyIndex m : ℕ) : ℝ)) <
        (((3 ^ m : ℕ) : ℝ)) := by
    exact_mod_cast Critical.beattyIndex_lower_strict hm
  have hLog :
      Real.logb 2 (((2 ^ Critical.beattyIndex m : ℕ) : ℝ)) <
        Real.logb 2 (((3 ^ m : ℕ) : ℝ)) :=
    Real.logb_lt_logb
      (by norm_num : (1 : ℝ) < 2)
      (by positivity)
      hPowR
  have hLeft :
      Real.logb 2 (((2 ^ Critical.beattyIndex m : ℕ) : ℝ)) =
        (Critical.beattyIndex m : ℝ) := by
    calc
      Real.logb 2 (((2 ^ Critical.beattyIndex m : ℕ) : ℝ)) =
          (Critical.beattyIndex m : ℝ) * Real.logb 2 2 := by
        simpa using
          (Real.logb_pow
            (2 : ℝ) (2 : ℝ) (Critical.beattyIndex m))
      _ = (Critical.beattyIndex m : ℝ) := by
        rw [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
        simp
  have hRight :
      Real.logb 2 (((3 ^ m : ℕ) : ℝ)) =
        (m : ℝ) * Real.logb 2 3 := by
    simpa using
      (Real.logb_pow (2 : ℝ) (3 : ℝ) m)
  rw [hLeft, hRight] at hLog
  exact hLog

/--
`log₂ 3` は無理数。

非無理と仮定して `log₂ 3 = p/q` (`q>0`) と書く。
幅 `q` の floor formula は `beattyIndex q = p` を与える一方、
power-form strictness は `beattyIndex q < p` を与えるため矛盾する。

従って素因数分解を実数指数へ持ち上げる必要はない。
-/
theorem irrational_logb_two_three :
    Irrational (Real.logb 2 3) := by
  by_contra hNot
  have hNonneg : 0 ≤ Real.logb (2 : ℝ) 3 :=
    beattyIndex_isLowerMechanical_logb_two_three.slope_nonneg
  obtain ⟨p, q, hq, _hCoprime, hRatio⟩ :=
    Experimental2.exists_reduced_nat_ratio_of_not_irrational_nonneg
      hNot hNonneg
  have hqR : (q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hq)
  have hMul :
      (q : ℝ) * ((p : ℝ) / (q : ℝ)) = (p : ℝ) := by
    calc
      (q : ℝ) * ((p : ℝ) / (q : ℝ)) =
          ((q : ℝ) * (p : ℝ)) / (q : ℝ) := by
            rw [mul_div_assoc]
      _ = (p : ℝ) := by
            exact mul_div_cancel_left₀ (p : ℝ) hqR
  have hStrict :
      (Critical.beattyIndex q : ℝ) < (p : ℝ) := by
    have h := beattyIndex_lt_mul_logb_two_three hq
    rw [hRatio, hMul] at h
    exact h
  have hBeta : Critical.beattyIndex q = p := by
    calc
      Critical.beattyIndex q =
          ⌊(q : ℝ) * Real.logb 2 3⌋₊ :=
        beattyIndex_eq_natFloor_logb_two_three q
      _ = ⌊(p : ℝ)⌋₊ := by
        rw [hRatio, hMul]
      _ = p := by simp
  have hBetaR :
      (Critical.beattyIndex q : ℝ) = (p : ℝ) := by
    exact_mod_cast hBeta
  linarith

/--
Beatty roof の Experimental2 slope は `log₂ 3` に一意に固定される。

任意の slope certificate `S` を受け取り、既に得た lower mechanical certificate と
Experimental2 の slope uniqueness を衝突させる。
-/
theorem roofSlope_eq_logb_two_three
    {σ : ℝ}
    (S : Experimental2.IsRoofSlope Critical.beattyIndex σ) :
    σ = Real.logb 2 3 := by
  exact
    Experimental2.roofSlope_unique S
      beattyIndex_isLowerMechanical_logb_two_three.isRoofSlope

/--
正規化後に現れる一歩回転角の対数恒等式。

`log₂(3/2) = log₂ 3 - 1`。
-/
theorem logb_two_three_div_two :
    Real.logb 2 ((3 : ℝ) / 2) =
      Real.logb 2 3 - 1 := by
  calc
    Real.logb 2 ((3 : ℝ) / 2) =
        Real.logb 2 3 - Real.logb 2 2 := by
      exact Real.logb_div (by norm_num) (by norm_num)
    _ = Real.logb 2 3 - 1 := by
      rw [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]

/--
Beatty roof を integer anchor `beattyIndex 1 = 1` で正規化すると、
slope は exact に `log₂(3/2)` になる。
-/
theorem normalizeBeatty_isLowerMechanical_logb_three_halves :
    Experimental2.IsLowerMechanicalRoof
      (Experimental2.normalizeRoof Critical.beattyIndex)
      (Real.logb 2 ((3 : ℝ) / 2)) := by
  have M :=
    (beattyIndex_hasUnitCarry.lowerMechanical_normalizeRoof_iff
      (σ := Real.logb 2 3)).1
      beattyIndex_isLowerMechanical_logb_two_three
  simpa [Critical.beattyIndex_one, logb_two_three_div_two] using M

/--
正規化 Beatty roof の exact floor formula。

`beattyIndex(n) - n = floor(n * log₂(3/2))` を
`normalizeRoof` の語彙で述べる。
-/
theorem normalizeBeatty_eq_natFloor_logb_three_halves
    (n : ℕ) :
    Experimental2.normalizeRoof Critical.beattyIndex n =
      ⌊(n : ℝ) * Real.logb 2 ((3 : ℝ) / 2)⌋₊ := by
  exact
    normalizeBeatty_isLowerMechanical_logb_three_halves.eq_natFloor' n

/--
正規化 slope `log₂(3/2)` も無理数。

`log₂(3/2) = log₂ 3 - 1` と、無理数から整数を引いても無理数であることだけを使う。
-/
theorem irrational_logb_two_three_halves :
    Irrational (Real.logb 2 ((3 : ℝ) / 2)) := by
  rw [logb_two_three_div_two]
  simpa using irrational_logb_two_three.sub_natCast 1

/--
一歩 Beatty carry の exact irrational mechanical-word 公式。

`beattyCarry(n,1)` は normalized Beatty roof の離散微分なので、
`log₂(3/2)` 回転の連続する二つの floor の差に一致する。
-/
theorem beattyCarry_one_eq_floorDiff_logb_three_halves
    (n : ℕ) :
    Critical.beattyCarry n 1 =
      ⌊((n + 1 : ℕ) : ℝ) * Real.logb 2 ((3 : ℝ) / 2)⌋₊ -
        ⌊(n : ℝ) * Real.logb 2 ((3 : ℝ) / 2)⌋₊ := by
  have h :=
    beattyIndex_hasUnitCarry.carryWord_eq_normalizedFloorDiff
      normalizeBeatty_isLowerMechanical_logb_three_halves n
  simpa only [carryWord_beattyIndex_eq] using h

end Bridge
end Collatz3
