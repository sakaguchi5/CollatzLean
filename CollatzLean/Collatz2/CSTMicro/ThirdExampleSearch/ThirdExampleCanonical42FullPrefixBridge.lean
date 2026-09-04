import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleCanonical42ModularFold
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.CanonicalOstrowskiTransferFold

/-!
# 第3例探索 D0: canonical 42-block modular fold と exact full defect の最終 bridge

`ThirdExampleCanonical42ModularFold` では、最初の 305 columns を exact collar として処理し、
残り 32 blocks を certified modular transfer で処理することで、zero state から
`criticalPrefixDefectZ thirdExampleTargetP y` の `ZMod M` 像へ到達することを証明した。

一方 `CanonicalOstrowskiTransferFold` では、actual canonical Ostrowski block 全体の
exact `StandardBlockTransfer` を zero state に適用すると、同じ full prefix defect が
整数 `ℤ` 上で得られることを証明済みである。

このファイルでは両者を、transfer 構造そのものではなく「zero state に作用した最終値」で
接続する。これは重要である。高速 corrected transfer と actual endpoint transfer は
主係数が一般に異なるため、transfer object 自体の等号を要求してはいけない。
必要なのは、それぞれの certified semantics が同じ full prefix-defect state に着地することだけである。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

open ExternalArithmetic

/--
第3例 target に対する actual canonical Ostrowski transfer の exact 最終状態。

この定義は探索 hot path の新しい計算を導入しない。
既存の exact canonical transfer を zero state に適用した整数値に名前を付けるだけである。
-/
def thirdExampleExactCanonicalFullState
    (y : ℤ) : ℤ :=
  (actualCriticalOstrowskiTransfer thirdExampleTargetP y).apply 0

/--
actual canonical Ostrowski transfer の exact 最終状態は、
target 全体の full prefix defect `criticalPrefixDefectZ thirdExampleTargetP y` に一致する。
-/
theorem thirdExampleExactCanonicalFullState_eq_criticalPrefixDefectZ
    (y : ℤ) :
    thirdExampleExactCanonicalFullState y =
      criticalPrefixDefectZ thirdExampleTargetP y := by
  unfold thirdExampleExactCanonicalFullState
  exact actualCriticalOstrowskiTransfer_apply_zero thirdExampleTargetP y

/--
A/B の packet certification の下で、C の canonical 42-block modular fold の最終状態は、
actual canonical Ostrowski transfer の exact 最終状態を `ZMod M` に落としたものと一致する。

ここで比較しているのは transfer object そのものではなく、zero state に作用した結果である。
したがって corrected 高速側の主係数 `2^Q` と actual 側の主係数 `3^P` の違いを
誤って消去していない。
-/
theorem thirdExampleCanonical42ModularFold_apply_zero_eq_exactCanonicalFullState
    {M : ℕ}
    (Cert : ThirdExampleCFPacketCertification M)
    (y : ℤ) :
    (thirdExampleCanonical42ModularFold M y).apply 0 =
      ((thirdExampleExactCanonicalFullState y : ℤ) : ZMod M) := by
  rw [thirdExampleExactCanonicalFullState_eq_criticalPrefixDefectZ]
  exact thirdExampleCanonical42ModularFold_apply_zero Cert y

/--
上の bridge を actual canonical Ostrowski transfer の式を展開せずに直接使う形。

今後の SearchState / verifier 層では、巨大 canonical decomposition の内部を再計算せず、
この定理を使って hot-path modular state を exact canonical state の剰余像として扱える。
-/
theorem thirdExampleCanonical42ModularFold_apply_zero_eq_actualOstrowski_mod
    {M : ℕ}
    (Cert : ThirdExampleCFPacketCertification M)
    (y : ℤ) :
    (thirdExampleCanonical42ModularFold M y).apply 0 =
      (((actualCriticalOstrowskiTransfer thirdExampleTargetP y).apply 0 : ℤ) : ZMod M) := by
  simpa [thirdExampleExactCanonicalFullState] using
    thirdExampleCanonical42ModularFold_apply_zero_eq_exactCanonicalFullState Cert y

/--
同じ最終状態を、既存の canonical phase-defect fold の `ZMod M` 像として書いた版。

これにより

`高速 42-block modular fold`

と

`既存 actual canonical phase-defect fold`

が full target endpoint で lossless に接続される。
-/
theorem thirdExampleCanonical42ModularFold_apply_zero_eq_actualPhaseDefectFold_mod
    {M : ℕ}
    (Cert : ThirdExampleCFPacketCertification M)
    (y : ℤ) :
    (thirdExampleCanonical42ModularFold M y).apply 0 =
      ((actualCriticalPhaseDefectFold
          0
          (actualCriticalOstrowskiBlockScales thirdExampleTargetP)
          y : ℤ) : ZMod M) := by
  rw [thirdExampleCanonical42ModularFold_apply_zero Cert y]
  rw [criticalPrefixDefectZ_eq_actualOstrowskiPhaseDefectFold]

/--
left collar modulus `2^68` 側で使う専用 wrapper。
exact canonical full state との接続を modulus の名前付き API として固定する。
-/
theorem thirdExampleCanonical42LeftFold_apply_zero_eq_exactCanonicalFullState
    (Cert : ThirdExampleCFPacketCertification thirdExampleLeftModulus)
    (y : ℤ) :
    (thirdExampleCanonical42ModularFold thirdExampleLeftModulus y).apply 0 =
      ((thirdExampleExactCanonicalFullState y : ℤ) :
        ZMod thirdExampleLeftModulus) :=
  thirdExampleCanonical42ModularFold_apply_zero_eq_exactCanonicalFullState Cert y

/--
right collar modulus `3^42` 側で使う専用 wrapper。
Hensel / boundary 側はこの定理から同じ exact full state の右剰余像を受け取れる。
-/
theorem thirdExampleCanonical42RightFold_apply_zero_eq_exactCanonicalFullState
    (Cert : ThirdExampleCFPacketCertification thirdExampleRightModulus)
    (y : ℤ) :
    (thirdExampleCanonical42ModularFold thirdExampleRightModulus y).apply 0 =
      ((thirdExampleExactCanonicalFullState y : ℤ) :
        ZMod thirdExampleRightModulus) :=
  thirdExampleCanonical42ModularFold_apply_zero_eq_exactCanonicalFullState Cert y

end ThirdExampleSearch
end CSTMicro
end Collatz2
