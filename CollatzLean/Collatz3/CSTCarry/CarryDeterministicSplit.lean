import CollatzLean.Collatz3.CSTCarry.ShiftedBlockDefect
import CollatzLean.Collatz3.CSTCarry.CarryDeterministic
/-!
# Collatz3 CSTCarry: canonical carry run の lossless split

`canonicalCarryRun` は row list を左から決定的に読む。
したがって `rows₀ ++ rows₁` を走らせることは、

1. `rows₀` を initial carry `E` から走らせる、
2. その final carry を `rows₁` の initial carry に渡す、

ことと exact に一致する。

block 分解で canonical ternary digits を実際の row slice と同じ位置に切るための
純粋な deterministic bridge であり、profile / record / first-passage 仮定は不要。
-/

namespace Collatz3
namespace CSTCarry

/-- append した row listの canonical digit list は block ごとの digit listの append。 -/
theorem canonicalCarryDigits_append
    (H : ℕ)
    (rows₀ rows₁ : List FerrersRow)
    (E : ℕ) :
    canonicalCarryDigits H (rows₀ ++ rows₁) E =
      canonicalCarryDigits H rows₀ E ++
        canonicalCarryDigits H rows₁ (canonicalFinalCarry H rows₀ E) := by
  induction rows₀ generalizing E with
  | nil =>
      simp
  | cons R Rs ih =>
      simp [ih]

/-- append した row listの canonical final carry は前半 final carry を後半へ渡したもの。 -/
theorem canonicalFinalCarry_append
    (H : ℕ)
    (rows₀ rows₁ : List FerrersRow)
    (E : ℕ) :
    canonicalFinalCarry H (rows₀ ++ rows₁) E =
      canonicalFinalCarry H rows₁ (canonicalFinalCarry H rows₀ E) := by
  induction rows₀ generalizing E with
  | nil =>
      simp
  | cons R Rs ih =>
      simp [ih]

/-- `take/drop` で切った位置は canonical digit list でも exact な split 位置になる。 -/
theorem canonicalCarryDigits_eq_take_append_drop
    (H : ℕ)
    (rows : List FerrersRow)
    (E k : ℕ) :
    canonicalCarryDigits H rows E =
      canonicalCarryDigits H (rows.take k) E ++
        canonicalCarryDigits H (rows.drop k)
          (canonicalFinalCarry H (rows.take k) E) := by
  calc
    canonicalCarryDigits H rows E =
        canonicalCarryDigits H (rows.take k ++ rows.drop k) E := by
          rw [List.take_append_drop]
    _ =
        canonicalCarryDigits H (rows.take k) E ++
          canonicalCarryDigits H (rows.drop k)
            (canonicalFinalCarry H (rows.take k) E) := by
          exact canonicalCarryDigits_append H (rows.take k) (rows.drop k) E

/-- `take/drop` で切った後半の initial carry は前半の canonical final carry。 -/
theorem canonicalFinalCarry_eq_drop_after_take
    (H : ℕ)
    (rows : List FerrersRow)
    (E k : ℕ) :
    canonicalFinalCarry H rows E =
      canonicalFinalCarry H (rows.drop k)
        (canonicalFinalCarry H (rows.take k) E) := by
  calc
    canonicalFinalCarry H rows E =
        canonicalFinalCarry H (rows.take k ++ rows.drop k) E := by
          rw [List.take_append_drop]
    _ =
        canonicalFinalCarry H (rows.drop k)
          (canonicalFinalCarry H (rows.take k) E) := by
          exact canonicalFinalCarry_append H (rows.take k) (rows.drop k) E

end CSTCarry
end Collatz3
