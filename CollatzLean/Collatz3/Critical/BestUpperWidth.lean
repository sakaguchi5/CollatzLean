import CollatzLean.Collatz3.Critical.BeattyCarry
import Mathlib.Data.Nat.GCD.Basic

/-!
# Collatz3: width-only best-upper arithmetic

旧 `ContractingExponentPair (p,H)` を critical shape 層へ持ち込まない。
critical first-passage では terminal depth は

`H_m = criticalTwoDepth m`

に固定されるため、best-upper / strip-reduced / primitive の語彙は幅 `m` 一変数で書ける。

このファイルは pure arithmetic だけを扱い、Profile / Record / actual orbit を import しない。
-/

namespace Collatz3
namespace Critical

/--
幅 `m` が、それ以前の全 critical upper slope より上に出ない。

`H_m / m ≤ H_r / r` を division なしの cross product で書いたもの。
-/
def IsBestUpperWidth (m : ℕ) : Prop :=
  ∀ r : ℕ,
    0 < r →
    r < m →
    criticalTwoDepth m * r ≤ m * criticalTwoDepth r

/-- 幅 `m` の chord と denominator `r` の Beatty lower roof の間の整数幅。 -/
def criticalStripWidth (m r : ℕ) : ℕ :=
  criticalTwoDepth m * r - m * beattyIndex r

/-- critical pair `(m,H_m)` が primitive、すなわち slope が整数倍コピーでない。 -/
def IsPrimitiveWidth (m : ℕ) : Prop :=
  Nat.Coprime (criticalTwoDepth m) m

/-- critical width の content `gcd(m,H_m)`。 -/
def widthContent (m : ℕ) : ℕ :=
  Nat.gcd m (criticalTwoDepth m)

/-- content を除いた primitive denominator 候補。 -/
def primitiveWidth (m : ℕ) : ℕ :=
  m / widthContent m

/-- best-upper 条件の一点版。 -/
theorem IsBestUpperWidth.at
    {m : ℕ}
    (B : IsBestUpperWidth m)
    {r : ℕ}
    (hrPos : 0 < r)
    (hrLt : r < m) :
    criticalTwoDepth m * r ≤ m * criticalTwoDepth r :=
  B r hrPos hrLt
namespace IsBestUpperWidth

/-- best-upper なら旧 `strip ≤ width` 形式も満たす。 -/
theorem criticalStripWidth_le
    {m : ℕ}
    (B : IsBestUpperWidth m)
    {r : ℕ}
    (hrPos : 0 < r)
    (hrLt : r < m) :
    criticalStripWidth m r ≤ m := by
  have hBest := B.at hrPos hrLt
  have hBest' :
      criticalTwoDepth m * r ≤ m * beattyIndex r + m := by
    simpa [criticalTwoDepth, Nat.mul_add] using hBest
  unfold criticalStripWidth
  omega

/--
record block 内部で local depth `d` が whole chord より strict に下なら、
best-upper 性により `d` は local Beatty roof 以下。

後段の Record--Ferrers で使う中心的な算術補題。
-/
theorem depth_le_beatty_of_strict_below
    {m r d : ℕ}
    (B : IsBestUpperWidth m)
    (hm : 0 < m)
    (hrPos : 0 < r)
    (hrLt : r < m)
    (hBelow : m * d < criticalTwoDepth m * r) :
    d ≤ beattyIndex r := by
  have hBest := B.at hrPos hrLt
  have hScaled : m * d < m * criticalTwoDepth r :=
    lt_of_lt_of_le hBelow hBest
  have hDepth : d < criticalTwoDepth r :=
    (Nat.mul_lt_mul_left hm).mp hScaled
  rw [criticalTwoDepth] at hDepth
  exact Nat.lt_succ_iff.mp hDepth

end IsBestUpperWidth

/--
positive width では `IsBestUpperWidth` は旧 strip-reduced 形式と exact に同値。

新体系では左側を正本とし、右側は compatibility view として扱う。
-/
theorem isBestUpperWidth_iff_stripWidth_le
    {m : ℕ}
    (hm : 0 < m) :
    IsBestUpperWidth m ↔
      ∀ r : ℕ,
        0 < r →
        r < m →
        criticalStripWidth m r ≤ m := by
  constructor
  · intro B r hrPos hrLt
    exact B.criticalStripWidth_le hrPos hrLt
  · intro hStrip r hrPos hrLt
    have hLower :
        m * beattyIndex r ≤ criticalTwoDepth m * r :=
      Nat.le_of_lt (beattyIndex_below_criticalChord hm hrPos)
    have hStripLe := hStrip r hrPos hrLt
    have hSubAdd :
        criticalTwoDepth m * r - m * beattyIndex r +
            m * beattyIndex r =
          criticalTwoDepth m * r :=
      Nat.sub_add_cancel hLower
    calc
      criticalTwoDepth m * r
          = criticalTwoDepth m * r - m * beattyIndex r +
              m * beattyIndex r := hSubAdd.symm
      _ ≤ m + m * beattyIndex r :=
        Nat.add_le_add_right hStripLe _
      _ = m * criticalTwoDepth r := by
        simp [criticalTwoDepth, Nat.mul_add, Nat.add_comm]

/-- width content は常に正。 -/
theorem widthContent_pos (m : ℕ) :
    0 < widthContent m := by
  unfold widthContent
  have hDepthPos : 0 < criticalTwoDepth m := by
    simp [criticalTwoDepth]
  exact Nat.gcd_pos_of_pos_right m hDepthPos

/-- content は元の width を割る。 -/
theorem widthContent_dvd (m : ℕ) :
    widthContent m ∣ m := by
  unfold widthContent
  exact Nat.gcd_dvd_left _ _

/-- `content * primitiveWidth = width`。 -/
theorem widthContent_mul_primitiveWidth
    (m : ℕ) :
    widthContent m * primitiveWidth m = m := by
  unfold primitiveWidth
  exact Nat.mul_div_cancel' (widthContent_dvd m)

/-- primitive width 候補は元 width 以下。 -/
theorem primitiveWidth_le
    (m : ℕ) :
    primitiveWidth m ≤ m := by
  unfold primitiveWidth
  exact Nat.div_le_self _ _

/-- primitive なら content は 1。 -/
theorem widthContent_eq_one_of_primitive
    {m : ℕ}
    (P : IsPrimitiveWidth m) :
    widthContent m = 1 := by
  change Nat.gcd m (criticalTwoDepth m) = 1
  change Nat.gcd (criticalTwoDepth m) m = 1 at P
  rw [Nat.gcd_comm]
  exact P

/-- primitive width は primitive 化しても変わらない。 -/
theorem primitiveWidth_eq_self_of_primitive
    {m : ℕ}
    (P : IsPrimitiveWidth m) :
    primitiveWidth m = m := by
  unfold primitiveWidth
  rw [widthContent_eq_one_of_primitive P]
  simp

end Critical
end Collatz3
