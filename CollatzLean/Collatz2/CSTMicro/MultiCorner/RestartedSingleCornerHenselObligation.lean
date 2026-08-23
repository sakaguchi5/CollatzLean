import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedTerminalComponentRigidity
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBSingleCornerDefectRecurrence

/-!
# MultiCorner restarted branch: sole open arithmetic obligation

このファイルだけが未解決点を持つ。

以前は arbitrary な `b,w` に対して

  3^w | singleCornerDefect b w
    ->
  3^(w+1) ∤ singleCornerDefect b w

という一般的な exact-order axiom を置いていた。

しかし restarted Case I を閉じるために必要なのは、その一般命題ではない。
actual geometry から構成された `RestartedTerminalStraightPacket` に対してだけ、

  3^(width+1) ∤ singleCornerDefect b width

が言えれば十分である。

したがって open obligation を actual restarted branch に限定する。
今後消去すべき仮定も、この branch-specific theorem 一個だけである。

数学的には、

* restart entrance の exact depth 1,
* 直前 zero gap,
* terminal straight component,
* actual Beatty staircase,
* criticalization start の位置関係

をすべて `RestartedTerminalStraightPacket` に保持した状態で、
extra 3-adic digit が存在しないことを示せばよい。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

/--
restarted Case I にだけ必要な唯一の未証明算術補題。

以前の
`singleCornerDefect_fullDepth_exact_threeAdicOrder`
より意図的に弱い。

arbitrary `b,w` の full-depth exact-order は要求せず、
actual `RestartedTerminalStraightPacket` から生じる
`singleCornerDefect S.b S.width` が extra digit
`3^(S.width+1)` を持たないことだけを仮定する。

`hStart` も actual restarted closure の前提をそのまま保持するため
明示的に引数へ残している。
-/
axiom restartedSingleCorner_noExtraThreeAdic
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (hStart : 0 < P.criticalizationStart) :
    ¬ (3 : ℤ) ^ (S.width + 1) ∣
      (singleCornerDefect S.b S.width : ℤ)

end MultiCorner
end CSTMicro
end Collatz2
