import CollatzLean.Collatz3.Bridge.SurvivorCriticalEscapeWeightCesaroReduction
import CollatzLean.Collatz3.Bridge.FerrersAffineCellWeight
import CollatzLean.Collatz3.Bridge.FerrersAffineChainWeight
import CollatzLean.Collatz3.Bridge.FerrersCriticalEscapeWeight

/-!
# Collatz3 Bridge: 2021 論文から安全に回収する finite / rotation package

この umbrella は次だけをまとめる。

* Lemma 41 の Collatz 固有列を `criticalEscapeWeight` へ exact に同定する reduction
* Lemma 21 の有限局所交換を odd-only Ferrers 1-cell move として再証明
* Ferrers chain に沿う affineConst weighted telescope
* 1-cell normalized weight と criticalEscapeWeight の exact 接続

real completion と 2進 completion の極限同一視は含めない。
-/
