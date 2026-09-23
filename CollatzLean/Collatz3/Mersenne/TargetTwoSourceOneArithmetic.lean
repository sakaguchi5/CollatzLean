import CollatzLean.Collatz3.External.StephanTransitions
import CollatzLean.Collatz3.Mersenne.TwoHoleFinalInternal

/-!
# Collatz3 Mersenne: target-two `n=1` の analytic depth bound

A2 target 側の small-source residual のうち `n=1` を、A1 と同じ

1. deep arithmetic で depth を有限上界へ落とす、
2. bounded residual を finite certificate で閉じる、

という二段へ分離する。

このファイルでは第1段だけを内部 theorem にする。

`TwoHoleFinalInternal` ですでに

`TargetTwoHoleEquation ... n=1 ... → HasPeriodBreakAtMost (3^k) 1 6`

が無条件に証明済みである。したがって外部 cited input は
`External.StephanTransitions` の「period-1 break が固定個以下なら exponent は一様有界」
だけでよい。Collatz 固有の `TargetTwoHoleEquation → False` や branch-specific depth bound は
trusted input にしない。

finite sieve は別段階に残す。従ってこの更新後、A2 final interface の `n=1` field は
「bound + sieve」ではなく bounded finite sieve だけになる。
-/

namespace Collatz3
namespace Mersenne

/--
Stephan period-1 theorem から選んだ、target-two `n=1` 用の depth bound。

値そのものを先回りして捏造せず、cited theorem の effective witness を固定する。
将来 p=1 proof engine を直接形式化すれば、明示的な自然数定数へ置き換えられる。
-/
noncomputable def targetTwoSourceOneInternalDepthBound : ℕ :=
  External.StephanTransitions.periodOneDepthBound 6

/--
interior target-two `n=1` は period-break≤6 なので、一様な有限 depth bound を持つ。

ここでは finite sieve を使わない。解析側の責務だけを閉じる theorem である。
-/
theorem TargetTwoHoleEquation.source_one_internal_depth_bound
    {k r L a b : ℕ}
    (hk7 : 7 ≤ k)
    (hr : 0 < r)
    (ha0 : 0 < a)
    (hab : a < b)
    (hbDeep : b + 1 < L)
    (hEq : TargetTwoHoleEquation k 1 r L a b) :
    k < targetTwoSourceOneInternalDepthBound := by
  have hBreak :=
    hEq.source_one_periodBreakAtMostSix hr ha0 hab hbDeep
  exact External.StephanTransitions.periodOneDepthBound_spec
    6 (by omega : 2 ≤ k) hBreak

end Mersenne
end Collatz3
