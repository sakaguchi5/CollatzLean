import CollatzLean.Collatz4.M7.LivePruning
set_option linter.style.nativeDecide false
/-!
# Collatz4.M7.FiniteCertificate

m=7 前向き排除の唯一の有限計算部分。

巨大整数をリテラルとして埋め込まず、2179 個の候補を定義から native 実行で
再生成する。したがって certificate はソース中の固定巨大表に依存しない。
-/

namespace Collatz4.M7

/--
最終時刻 `s=8456` では、2179候補のどれも必要な2指数 `10996` を持たない。

これが主有限 certificate。`native_decide` はコンパイル済み自然数演算で評価する。
-/
theorem final_two_exponent_certificate :
    ∀ i : Fin candidateCount, (finalState i).t ≠ targetTwoExponent := by
  native_decide

/--
構造確認用 checkpoint certificate。

`s=8455` では各枝が

* 既に純粋な2のべき、または
* 2指数が 11057 以上、または
* 2指数が 10671 以下かつ奇数部分が `21 mod 64` ではない

の三群に分かれる。
-/
theorem checkpoint_certificate :
    ∀ i : Fin candidateCount, checkpointSafe (checkpointState i) := by
  simp only [checkpointSafe]
  native_decide

end Collatz4.M7
