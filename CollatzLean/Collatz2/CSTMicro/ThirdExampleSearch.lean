/-
# 第3例 fixed-window 探索核 集約

このファイルは、第3例探索の 1〜8 をまとめて import する。

1. 左 68 block の 2 進 affine 切断
2. 左 68 block から開始値 residue の一意復元
3. 右 42 block の 3 進 affine 切断
4. Record plateau の Hensel 一括転送
5. Record jump → Hensel boundary の局所 bridge
6. terminal Hensel の 3-lift survivor 上界
7. 標準ブロック transfer の合成
8. special return による actual first drop = coefficient first crossing

巨大整数 `G` や全軌道を hot loop で生成せず、左右 collar と中央の圧縮 transfer を
分離するための最小核である。
-/
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.AffinePrefixModTwo
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.StartValuePrefix68
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.AffineSuffixModThree
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.RecordPlateauQOneMacro
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.RecordJumpHenselBoundary
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.TerminalHenselThreeLift
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.StandardBlockTransfer
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.FirstCrossingSpecialReturn
--
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.RecordPlateauLocalMacro
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.PlateauPhiClosedForm
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.RecordPlateauOneParameter
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.RecordFerrersProvenanceAdapter
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.RecordJumpHenselDictionary
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.TerminalBoundaryLiftSurvival
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ActualOstrowskiStandardBlockTransfer
/-
# 第3例探索 次段 1-2
1. 実 Hensel 3-lift と criticalization boundary digit の exact adapter
2. canonical Ostrowski block list 全体の StandardBlockTransfer fold
-/
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.TerminalHenselBoundaryDigitAdapter
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.CanonicalOstrowskiTransferFold

/-
# 第3例探索: 計算可能性の追加修正

1. canonical Ostrowski decomposition を最小 rank で実行する高速版
2. `Fin 3` Hensel digit label を実際の三つの integer lift 値へ接続する adapter
-/

import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.FastCanonicalOstrowskiRank
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ArithmeticHenselLiftValueAdapter
--
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.GapOneSuffixHenselBridge
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleConvergent22Checkpoint
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ModularStandardBlockTransfer
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ModularContinuedFractionStandardBlock
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleOddScaleModularTransfers



namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

/-- 今回の continued-fraction target に対応する first-drop odd block 数。 -/
def targetP : ℕ := 6586818669

/-- 今回の continued-fraction target に対応する first-drop two-depth。 -/
def targetH : ℕ := 10439860590

/-- 左 collar の odd block 幅。 -/
def leftCollarWidth : ℕ := 68

/-- 右 collar の odd block 幅。 -/
def rightCollarWidth : ℕ := 42

/-- 左右 collar を除いた中央 odd block 数。 -/
def middleOddBlocks : ℕ :=
  targetP - leftCollarWidth - rightCollarWidth

/-- 中央 window は 6,586,818,559 odd blocks。 -/
theorem middleOddBlocks_eq :
    middleOddBlocks = 6586818559 := by
  decide

end ThirdExampleSearch
end CSTMicro
end Collatz2
