import CollatzLean.Collatz3.Experimental2.RoofCore
import CollatzLean.Collatz3.Experimental2.CarryCore
import CollatzLean.Collatz3.Experimental2.Normalization
import CollatzLean.Collatz3.Experimental2.BitList
import CollatzLean.Collatz3.Experimental2.FiniteComposition
import CollatzLean.Collatz3.Experimental2.Refinement
import CollatzLean.Collatz3.Experimental2.RoofPath
import CollatzLean.Collatz3.Experimental2.SlopeWindow
import CollatzLean.Collatz3.Experimental2.SlopeApproximation
import CollatzLean.Collatz3.Experimental2.SlopeExistence
import CollatzLean.Collatz3.Experimental2.RationalMechanical
import CollatzLean.Collatz3.Experimental2.MechanicalRoof
import CollatzLean.Collatz3.Experimental2.RotationPhase
import CollatzLean.Collatz3.Experimental2.MechanicalCharacterization

set_option linter.style.header false

/-!
# Collatz3 Experimental2

`Experimental` を凍結した後、その成果を

`thin definitions + derived theorems`

の原則で数学的依存順に再構成した第二実験層。

方針:

1. `HasUnitCarry` を下側超加法性と上側一単位誤差へ分解する。
2. carry は屋根から計算する derived quantity とする。
3. 正規化は carry を保存する冪等射影として扱う。
4. bit-list / finite composition / refinement を roof path や slope から分離する。
5. slope は residual ではなく屋根 `β` 自身に対して直接定義する。
6. exact Real slope は `noncomputable def` として保存せず、
   `∃! σ, IsRoofSlope β σ` を主 theorem とする。
7. 実行可能な slope 近似は `ℚ` で別に持つ。
8. mechanical roof は linear part や residual を field に保存せず、
   `β(n)` 自身の lower / upper cell 条件だけで定義する。
9. rational generic theory では `p ≤ q` を仮定しない。
10. `Experimental/*` は一切 import せず、旧層を regression oracle として固定する。

この層も `Critical` / `Ferrers` / `Semantics` には依存しない。
-/
