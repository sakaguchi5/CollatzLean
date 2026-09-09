import CollatzLean.Collatz3.Experimental.UnitCarryRoof
import CollatzLean.Collatz3.Experimental.RoofPathExact
import CollatzLean.Collatz3.Experimental.CarryCocycle
import CollatzLean.Collatz3.Experimental.RecordCarryBudget
import CollatzLean.Collatz3.Experimental.CarryDefectRefinement
import CollatzLean.Collatz3.Experimental.CarryWordBalance
import CollatzLean.Collatz3.Experimental.UnitCarryClassification
import CollatzLean.Collatz3.Experimental.RotationPhase
import CollatzLean.Collatz3.Experimental.HomogenizedSlopeExistence
import CollatzLean.Collatz3.Experimental.HomogenizedSlopeUniqueness
import CollatzLean.Collatz3.Experimental.IrrationalSlopeBridge
import CollatzLean.Collatz3.Experimental.RationalScaledSlopeBridge
import CollatzLean.Collatz3.Experimental.NonnegativeRationalSlopeExtraction
import CollatzLean.Collatz3.Experimental.UnitCarryCompleteClassification
import CollatzLean.Collatz3.Experimental.ReducedRationalSlope
import CollatzLean.Collatz3.Experimental.RationalMechanicalClosedForm
import CollatzLean.Collatz3.Experimental.CarryWordMechanicalFormula
import CollatzLean.Collatz3.Experimental.UnitCarryMechanicalCharacterization

set_option linter.style.header false

/-!
# Collatz3 mathematical experiments

Collatz3 全面書き換え前に、Collatz 固有の実装から一般数学を切り離して検証する import 入口。

現段階では、次の流れが Experimental 層だけで閉じている。

1. 一般整数値屋根 `β : ℕ → ℕ` に対する 0/1-carry 条件、
2. carry cocycle と有限 block の exact carry budget、
3. 一般 roof path 上の local failure / terminal minimality exact law、
4. carry word の balancedness と residual 分解、
5. unit-carry roof から canonical homogenized slope の存在と一意性、
6. slope の irrational / rational 完全分類、
7. rational slope の既約自然数表示 `p/q`、
8. rational lower / upper 型の全幅 closed form、
9. carry word の exact mechanical formula、
10. lower / upper mechanical roof から `HasUnitCarry` を復元する converse、
11. `HasUnitCarry ↔ mechanical roof` の特徴付け。

重要なのは、slope `ρ`、rational witness `p,q`、lower / upper 型、carry pattern を
primitive field として保存しないこと。
これらは薄い unit-carry 条件から theorem として導く。

この層は現行 `Critical` / `Ferrers` / `Semantics` を import せず、
全面書き換え時にどこまでを一般数学 kernel として再利用できるかを調べるための独立実験層である。
-/
