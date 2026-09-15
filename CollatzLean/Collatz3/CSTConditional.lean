import CollatzLean.Collatz3.CSTConditional.GlobalCST
import CollatzLean.Collatz3.CSTConditional.FutureMinimum
import CollatzLean.Collatz3.CSTConditional.MarginMass
import CollatzLean.Collatz3.CSTConditional.FlatStructure
import CollatzLean.Collatz3.CSTConditional.ACStructure
import CollatzLean.Collatz3.CSTConditional.ACCounting
import CollatzLean.Collatz3.CSTConditional.ACConservation
import CollatzLean.Collatz3.CSTConditional.ALinearGrowth
import CollatzLean.Collatz3.CSTConditional.ANormalizedEscape

-- normalized escape 以後の薄い derived bridge
import CollatzLean.Collatz3.Bridge.SurvivorNormalizedEscapeShadow
import CollatzLean.Collatz3.Bridge.SurvivorNormalizedEscapeCompletion
import CollatzLean.Collatz3.Bridge.SurvivorCompletionNormalizedLift
import CollatzLean.Collatz3.CSTConditional.ANormalizedEscapeShadow
import CollatzLean.Collatz3.CSTConditional.ACNormalizedEscapeShadow
import CollatzLean.Collatz3.CSTConditional.ANormalizedCompletionAnchor

-- completion residue / normalized lift の次段 thin-derived package
import CollatzLean.Collatz3.Bridge.SurvivorCompletionResidueDynamics
import CollatzLean.Collatz3.Bridge.SurvivorCompletionCenteredResidue
import CollatzLean.Collatz3.Bridge.SurvivorCompletionAllStepNormalizedLift
import CollatzLean.Collatz3.Bridge.SurvivorCompletionSharpNormalizedBranch
import CollatzLean.Collatz3.Bridge.SurvivorCompletionDyadicState
import CollatzLean.Collatz3.Bridge.SurvivorDefectNormalizedActual
import CollatzLean.Collatz3.CSTConditional.ADefectNormalizedActual

/-!
# Collatz3: CSTConditional package

`GlobalCST` を仮定した場合だけ使う条件付き bridge 群。
既存 unconditional kernel / Bridge / CSTMicro の定理そのものは変更しない。

追加の AC / A-type package では、Global CST により `B` が消えた後の future-minimum dynamics を

* exact two-depth / margin threshold
* `C / AC / AAC` 局所 cell
* `#A + #C = q`
* `defectGrowth + #C = q`
* defect / critical-margin exact conservation
* linear defect lower bound から future-minimum 密度・平均 block 長・actual log growth
* linear defect survivor の normalized escape coordinate の有限正実数極限
* escape limit から得られる negative real shadow の exact affine recurrence
* next-future-minimum block 上の positive shadow-gap affine contraction
* critical completion endpoint と normalized escape の finite exact identity
* completion lift cocycle の defect-normalized 5候補、および flat branch の3候補化
* A 型 real shadow と normalized completion branch の任意に遠い共通 future-minimum anchor
* canonical residue `rho` の flat/rise exact transition
* midpoint-centered residue `sigma` と `-3^(-(m+1))` 型 congruence
* exponent を消去した normalized completion lift の全-step recurrence
* Sturmian step `0/1` に応じた branch の `3/5 -> 2/4` sharp 化
* centered lift/residue をまとめる dyadic state `xi` と future-minimum skew-product
* actual value の defect-normalized compact state `V_m`

として整理する。

real escape limit と natural/2進 completion を同一視しない。
両側が同じ finite exponent itinerary 上で同時に満たす exact 制約だけを記録する。
-/
