import CollatzLean.Collatz3.External.StephanTransitions
import CollatzLean.Collatz3.Mersenne.TwoHoleFinalInternal

/-!
# Collatz3 Mersenne: target-two `n=1` の explicit analytic depth bound

A2 target 側の small-source residual のうち `n=1` を、A1 と同じ

1. deep arithmetic で depth を explicit な有限上界へ落とす、
2. bounded residual を finite certificate で閉じる、

という二段へ分離する。

`TwoHoleFinalInternal` ですでに

`TargetTwoHoleEquation ... n=1 ... → HasPeriodBreakAtMost (3^k) 1 6`

が無条件に証明済みである。

前版では Stephan theorem の existential witness を `Classical.choose` していたため、
`targetTwoSourceOneInternalDepthBound` が noncomputable になり、後段 finite sieve の
実計算に使えなかった。

この版では `External.StephanTransitions` の explicit `B=6` specialization を使い、

`targetTwoSourceOneInternalDepthBound = 2^180000 + 1`

を計算可能な自然数定数として固定する。
-/

namespace Collatz3
namespace Mersenne

/--
Stephan period-1 theorem から得る target-two `n=1` 用 explicit depth bound。

計算可能な定数なので、次段の modular / tail-loop finite sieve が直接使える。
-/
def targetTwoSourceOneInternalDepthBound : ℕ :=
  External.StephanTransitions.periodOneBreakSixDepthBound

/-- bound の具体形。finite certificate 側で展開したい時の public lemma。 -/
theorem targetTwoSourceOneInternalDepthBound_eq :
    targetTwoSourceOneInternalDepthBound = 2 ^ 180000 + 1 := by
  rfl

/--
interior target-two `n=1` は period-break≤6 なので explicit depth bound を持つ。

finite sieve はここでは使わず、解析側の責務だけを閉じる。
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
  exact External.StephanTransitions.threePow_periodOne_breakSix_bounded
    (by omega : 2 ≤ k) hBreak

end Mersenne
end Collatz3
