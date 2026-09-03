import CollatzLean.Collatz2.CSTMicro.BeattyPositions
import CollatzLean.Collatz2.Geometry.RankStrip

/-!
# criticalHeight と Beatty index の橋

ここで使う `criticalHeight` は `Collatz2.Word` 側の Ferrers roof である。
`CSTMicro` 側の prefix-height 系とは別物なので、名前空間を明示する。

`Word.criticalHeight n` は

  2^h < 3^n

を満たす最大の `h`、一方 `beattyIndex n` は

  3^n ≤ 2^(q+1)

を初めて満たす `q` である。したがって両者は同じ整数を表す。
-/

namespace Collatz2
namespace CSTMicro
namespace DoubleDecomposition

/--
Ferrers roof の critical height は Beatty position と exact に一致する。

この定理が、構成側の Record/Ferrers 高さと、計算側の
Ostrowski/Christoffel index を同じ整数座標へ載せる最初の橋になる。
-/
theorem criticalHeight_eq_beattyIndex (n : ℕ) :
    Word.criticalHeight n = beattyIndex n := by
  cases n with
  | zero =>
      simp [Word.criticalHeight]
  | succ n =>
      have hLow :
          2 ^ Word.criticalHeight (n + 1) < 3 ^ (n + 1) :=
        Word.criticalHeight_pow_lt_threePow (by omega)
      have hHigh :
          3 ^ (n + 1) ≤ 2 ^ (Word.criticalHeight (n + 1) + 1) := by
        by_contra hnot
        have hStrict :
            2 ^ (Word.criticalHeight (n + 1) + 1) < 3 ^ (n + 1) := by
          omega
        have hTooHigh :=
          Word.le_criticalHeight_of_twoPow_lt_threePow hStrict
        omega
      have hBeatty :=
        beattyIndex_eq_of_adjacent_dyadic_bracket hLow hHigh
      exact hBeatty.symm

end DoubleDecomposition
end CSTMicro
end Collatz2
