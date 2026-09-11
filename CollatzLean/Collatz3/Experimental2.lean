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

-- derived API: 旧 Experimental の便利な結論を新 kernel 上で再構成する。
import CollatzLean.Collatz3.Experimental2.NormalizationSlopeBridge
import CollatzLean.Collatz3.Experimental2.SlopeApproximationBounds
import CollatzLean.Collatz3.Experimental2.RoofDefect
import CollatzLean.Collatz3.Experimental2.RecordBudgetCorollaries
import CollatzLean.Collatz3.Experimental2.MechanicalRoofDerived
import CollatzLean.Collatz3.Experimental2.CarryWord
import CollatzLean.Collatz3.Experimental2.RotationPhaseDerived

-- 第三段: inverse / convergent corridor / Record chain law
import CollatzLean.Collatz3.Experimental2.MechanicalConvergentCorridor
import CollatzLean.Collatz3.Experimental2.MechanicalInverse
import CollatzLean.Collatz3.Experimental2.MechanicalInverseCorridor
import CollatzLean.Collatz3.Experimental2.MechanicalInverseCorridorEndpoint
import CollatzLean.Collatz3.Experimental2.MechanicalConvergentCorridorSharp
import CollatzLean.Collatz3.Experimental2.MechanicalConvergentCorridorSharpEndpoint
import CollatzLean.Collatz3.Experimental2.FiniteInverseCorridorComposition
import CollatzLean.Collatz3.Experimental2.OstrowskiCorridorArithmetic
import CollatzLean.Collatz3.Experimental2.OstrowskiCanonicalArithmetic
import CollatzLean.Collatz3.Experimental2.OstrowskiCanonicalGreedy
import CollatzLean.Collatz3.Experimental2.OstrowskiCanonicalCorridor
import CollatzLean.Collatz3.Experimental2.OstrowskiResidueScan
import CollatzLean.Collatz3.Experimental2.RecordCarryLaw

--サブフォルダ　GenericRecordFerrers
import CollatzLean.Collatz3.Experimental2.GenericRecordFerrers

set_option linter.style.header false

/-!
# Collatz3 Experimental2

`Experimental` を凍結した後、その成果を `thin definitions + derived theorems` の原則で
数学的依存順に再構成した第二実験層。

今回追加した canonical Ostrowski 層では、continued fraction の実数実装をこの層へ
持ち込まず、部分商と convergent weight が満たす自然数再帰だけを generic kernel とする。

* sharp Farey corridor の lower endpoint から不要な `P < Pn` を除く。
* bounded Ostrowski digit だけから sharp residual range を導く。
* canonical adjacency は exactness ではなく normal form / uniqueness にだけ使う。
* Euclidean greedy により任意の自然数へ canonical finite-support digits を与える。
* bounded digits から `ExactInverseCorridorChain` を自動生成し、外部 chain certificate を消す。
* 固定法に対する weighted sum を weight pair と residue の有限状態走査で復元する。

この層は引き続き `Critical` / `Ferrers` / `Semantics` には依存しない。
旧 `Experimental/*` も一切 import しない。
-/
