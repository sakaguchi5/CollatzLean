import CollatzLean.Collatz4.Targets.M7.LivePruning
set_option linter.style.nativeDecide false
/-!
# Collatz4.Targets.M7.FiniteCertificate

m=7 に本当に固有な有限計算部分。

一般理論はこのファイルの数値を知らず、ここで得られた certificate だけを受け取る。
-/

namespace Collatz4.Targets.M7

open Collatz4.Finite

/--
最終時刻では、m=7 の有限候補のどれも必要な目標2指数を持たない。

一般 `ForwardProblem` に対する2指数 certificate の m=7 実体。
-/
theorem final_two_exponent_certificate :
    ∀ i : Fin candidateCount, (finalState i).t ≠ targetTwoExponent := by
  native_decide

/--
構造確認用 checkpoint certificate。

三分岐の形は一般層、11057/10671/64/21 という値だけが m=7 固有である。
-/
theorem checkpoint_certificate :
    ∀ i : Fin candidateCount, checkpointSafe (checkpointState i) := by
  simp only [checkpointSafe, Collatz4.Finite.checkpointSafe, checkpointSpec]
  native_decide

end Collatz4.Targets.M7
