import CollatzLean.Collatz3.Binary.RunResolution


/-!
# Collatz3 Binary: run resolution の反復 factor

既存 `runResolutionCode_factor_two` は threshold を一度に `2` だけ下げる。
ここではその純粋な反復帰結だけをまとめる。

新しい resolution object は導入しない。
-/

namespace Collatz3
namespace Binary

/-- `t + 2*m` の code equality は `t` の code equality へ降りる。 -/
theorem runResolutionCode_factor_iterate
    (m : ℕ)
    {t a b : ℕ}
    (h :
      runResolutionCode (t + 2 * m) a =
        runResolutionCode (t + 2 * m) b) :
    runResolutionCode t a = runResolutionCode t b := by
  induction m with
  | zero =>
      simpa using h
  | succ m ih =>
      have hStep :
          runResolutionCode (t + 2 * m) a =
            runResolutionCode (t + 2 * m) b := by
        apply runResolutionCode_factor_two (t := t + 2 * m)
        simpa [Nat.mul_succ, Nat.add_assoc] using h
      exact ih hStep

/-- run-length list 全体でも `2*m` 分の resolution を反復して落とせる。 -/
theorem resolveRunLengths_factor_iterate
    (m : ℕ)
    {t : ℕ} {a b : List ℕ}
    (h :
      resolveRunLengths (t + 2 * m) a =
        resolveRunLengths (t + 2 * m) b) :
    resolveRunLengths t a = resolveRunLengths t b := by
  induction m with
  | zero =>
      simpa using h
  | succ m ih =>
      have hStep :
          resolveRunLengths (t + 2 * m) a =
            resolveRunLengths (t + 2 * m) b := by
        apply resolveRunLengths_factor_two (t := t + 2 * m)
        simpa [Nat.mul_succ, Nat.add_assoc] using h
      exact ih hStep

/-- binary word の run resolution も `2*m` 分まとめて coarse 化できる。 -/
theorem runResolution_factor_iterate
    (m : ℕ)
    {t : ℕ} {u v : List Bool}
    (h :
      runResolution (t + 2 * m) u =
        runResolution (t + 2 * m) v) :
    runResolution t u = runResolution t v := by
  induction m with
  | zero =>
      simpa using h
  | succ m ih =>
      have hStep :
          runResolution (t + 2 * m) u =
            runResolution (t + 2 * m) v := by
        apply runResolution_factor_two (t := t + 2 * m)
        simpa [Nat.mul_succ, Nat.add_assoc] using h
      exact ih hStep

end Binary
end Collatz3
