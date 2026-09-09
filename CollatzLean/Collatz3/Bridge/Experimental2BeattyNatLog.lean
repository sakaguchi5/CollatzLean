import CollatzLean.Collatz3.Critical.BeattyCarry
import Mathlib.Data.Nat.Log

/-!
# Collatz3 Bridge: power-form Beatty index と `Nat.log`

`Critical.beattyIndex` は `Nat.find` によって power inequality から定義されている。
このファイルでは、その定義が mathlib の計算可能な 2 進 floor logarithm

`Nat.log 2 (3^m)`

と exact に一致することを示す。

実数対数はここでは使わない。従ってこの層は pure discrete / computable bridge である。
-/

namespace Collatz3
namespace Bridge

/--
Power-form `beattyIndex` は標準の 2 進 floor logarithmそのもの。

`2^beattyIndex(m) ≤ 3^m < 2^(beattyIndex(m)+1)` を
`Nat.log_eq_of_pow_le_of_lt_pow` に渡すだけで得られる。
-/
theorem beattyIndex_eq_natLog_two_threePow
    (m : ℕ) :
    Critical.beattyIndex m = Nat.log 2 (3 ^ m) := by
  have hUpper :
      3 ^ m < 2 ^ (Critical.beattyIndex m + 1) := by
    simpa [Critical.criticalTwoDepth] using
      Critical.threePow_lt_twoPow_criticalTwoDepth m
  exact
    (Nat.log_eq_of_pow_le_of_lt_pow
      (Critical.beattyIndex_lower m) hUpper).symm

end Bridge
end Collatz3
