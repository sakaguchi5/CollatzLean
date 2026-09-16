import CollatzLean.Collatz3.CSTConditional.IntegerReduction.PowerIndex
import CollatzLean.Collatz3.CSTConditional.IntegerReduction.AdmissibleBlock
import CollatzLean.Collatz3.CSTConditional.IntegerReduction.AdmissibleBlockClassification
import CollatzLean.Collatz3.CSTConditional.IntegerReduction.BlockDefect
import CollatzLean.Collatz3.CSTConditional.IntegerReduction.BlockCounting
import CollatzLean.Collatz3.CSTConditional.IntegerReduction.CanonicalResidue
import CollatzLean.Collatz3.CSTConditional.IntegerReduction.CanonicalResidueBlock
import CollatzLean.Collatz3.CSTConditional.IntegerReduction.RecordBoundaryDecomposition
import CollatzLean.Collatz3.CSTConditional.IntegerReduction.InteriorDefectGrowth
import CollatzLean.Collatz3.CSTConditional.IntegerReduction.OddRecurrence
import CollatzLean.Collatz3.CSTConditional.IntegerReduction.ExponentialEscapeReduction
import CollatzLean.Collatz3.CSTConditional.IntegerReduction.EventualPeriodicity
import CollatzLean.Collatz3.CSTConditional.IntegerReduction.RightRecordCharacterization
import CollatzLean.Collatz3.CSTConditional.IntegerReduction.AdmissibleDecompositionUniqueness
import CollatzLean.Collatz3.CSTConditional.IntegerReduction.EscapeRecordReconstruction
import CollatzLean.Collatz3.CSTConditional.IntegerReduction.FromAType

set_option linter.style.longLine false

/-!
# Collatz3 CSTConditional Work package

GPT Work で得た独立整数問題への縮約を、`IntegerReduction` 以下に分離して集約する。

設計原則は `thin definitions + derived theorems`。

* pure integer 側では actual orbit / `GlobalCST` を使わない。
* right-record による boundary の完全特徴付けと、許容 block 分解の一意性を含む。
* Problem E 型の指数逃走から、有限 shift 後の許容 block 分解を再構成する逆向きも含む。
* `FromAType` だけが現行 CSTConditional の A 型仮定から pure integer package へ橋を架ける。
* 主 `CSTConditional.lean` には import を追加せず、この `CSTConditional.Work` を明示的に
  import したときだけ研究縮約層を読み込む。

未解決の存在・非存在問題そのものを theorem として仮定しない。
-/
