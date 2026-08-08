import CollatzLean.CollatzSecondLayer3.FirstCrossingReturnArithmetic
import CollatzLean.CollatzSecondLayer3.FirstCrossingValuationTriangle
import CollatzLean.CollatzSecondLayer3.FutureMinimumCrossAnchor

/-!
# 発散側 actual-return 研究核

negative shadowを主矛盾源から降格した後の正本入口。

現在の主なactual情報は次の三群にまとめる。

* first-crossing return arithmetic
  * `B = 3^p*d + g*endpoint`
  * `3*d < p`
  * Baker入力下で十分後に`d < p < g`
* valuation / synchronization triangle
  * `A<C -> D=A`
  * `C<A -> D=C`
  * `A=C -> A<D`
  * `D=1 <-> highOffset=0`
* consecutive future-minimum geometry
  * `4 ≤ Δ ≤ d`
  * 標準future-minimum first-crossingでは`13 ≤ p`
  * 次minimum以前のproper suffixはcontracting

negative shadow・Special C3 terminal geometryは削除せず、必要な局所alignment補題を
参照するlegacy解析として保持する。
-/

namespace CollatzSecondLayer3

-- このファイル自身では新しいexclusion仮定を導入しない。
-- 上記三群を今後のactual-orbit矛盾証明の共通APIとして公開する。

end CollatzSecondLayer3
