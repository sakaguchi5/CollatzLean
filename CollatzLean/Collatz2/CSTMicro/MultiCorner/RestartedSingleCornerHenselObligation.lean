import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedSuffixHenselFinite36
import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedSuffixHenselLargeWidthClosure

/-!
# Legacy restarted single-corner Hensel obligation: theorem replacement

このファイルに以前あった large-width axiom は削除した。
現在は

* `4 ≤ width ≤ 36`: finite deterministic Hensel closure,
* `37 ≤ width`: Beatty-repeat large-width closure

で同じ negated extra-divisibility statement を theorem として得る。

新しい `RestartedBranchClosure` 自身はこの compatibility theorem に依存せず、
finite / large の `False` theorem を直接使う。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

/--
旧 large-width obligation と同じ API を theorem として保存する compatibility wrapper。
axiom は使用しない。
-/
theorem restartedSingleCorner_noExtraThreeAdic_large
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (hStart : 0 < P.criticalizationStart)
    (hWidth : 4 ≤ S.width) :
    ¬ (3 : ℤ) ^ (S.width + 1) ∣
      (singleCornerDefect S.b S.width : ℤ) := by
  intro hExtra
  by_cases hFinite : S.width ≤ 36
  · exact
      (S.restartedSingleCorner_noExtraThreeAdic_four_to_thirtySix
        hStart hWidth hFinite) hExtra
  · have hLarge : 37 ≤ S.width := by
      omega
    exact
      S.restartedSuffixHensel_false_of_width_ge_37
        hStart hLarge

end MultiCorner
end CSTMicro
end Collatz2
