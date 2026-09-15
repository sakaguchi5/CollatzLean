import CollatzLean.Collatz3.CSTConditional.GlobalCST
import CollatzLean.Collatz3.CSTConditional.FutureMinimum
import CollatzLean.Collatz3.CSTConditional.MarginMass
import CollatzLean.Collatz3.CSTConditional.FlatStructure
import CollatzLean.Collatz3.CSTConditional.ACStructure
import CollatzLean.Collatz3.CSTConditional.ACCounting
import CollatzLean.Collatz3.CSTConditional.ACConservation
import CollatzLean.Collatz3.CSTConditional.ALinearGrowth
import CollatzLean.Collatz3.CSTConditional.ANormalizedEscape
import CollatzLean.Collatz3.CSTConditional.FutureMinimumLocalRoof
import CollatzLean.Collatz3.CSTConditional.FutureMinimumLocalRoofAsymptotics
import CollatzLean.Collatz3.CSTConditional.FutureMinimumFerrersStrip
import CollatzLean.Collatz3.CSTConditional.FutureMinimumRoofCarryCocycle

-- A 型 exact defect / cut geometry / A-C-Sturmian / margin / counting / compact state / residue dynamics
import CollatzLean.Collatz3.CSTConditional.FutureMinimumDefectExact
import CollatzLean.Collatz3.CSTConditional.FutureMinimumCutGeometry
import CollatzLean.Collatz3.CSTConditional.ACSturmianRefinement
import CollatzLean.Collatz3.CSTConditional.ACMarginFloor
import CollatzLean.Collatz3.CSTConditional.ACStrongCounting
import CollatzLean.Collatz3.CSTConditional.ADefectNormalizedActualCompact
import CollatzLean.Collatz3.CSTConditional.ActualResidueDynamics

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

-- a4bf... 以後: actual finite residue / Hensel / Beatty target / defect floor
import CollatzLean.Collatz3.Bridge.SurvivorDefectActualResidue
import CollatzLean.Collatz3.Bridge.SurvivorActualCompletionHensel
import CollatzLean.Collatz3.Bridge.SurvivorActualCompletionGridSeparation
import CollatzLean.Collatz3.Bridge.SurvivorDefectBeattyScale
import CollatzLean.Collatz3.Bridge.SurvivorCriticalEscapeWeight
import CollatzLean.Collatz3.Bridge.Research2021SafeFinite
import CollatzLean.Collatz3.CSTConditional.AFutureMinimumDefectFloor
import CollatzLean.Collatz3.CSTConditional.AActualResidueQuotient
import CollatzLean.Collatz3.CSTConditional.AFiniteActualCompletionAnchor

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
* future minimum から見た local roof defect `beattyIndex r - twoSteps(segment)`
* local roof contribution `w_r / 2^d` と scaled normalized escape increment の exact 同一視
* local roof contribution の shadow-gap `tsum` identity
* local contribution の Cesàro 平均 `0` と weighted roof deficit の Lemma 41 平均
* 任意の固定 local roof depth band の自然密度 `0`
* weighted roof deficit と縦 Ferrers cell strip の finite exact identity
* weighted Ferrers strip area の Cesàro 極限 `1/(6 log 2)`
* fixed-anchor local roof defect の Beatty carry cocycle
* 標準 future-minimum endpoint depth と 0/1 Beatty carry 累積の exact 同一視
* global defect / fixed-anchor local roof defect / absolute Beatty carry の exact identity
* linear defect A 型では固定 anchor の bounded local roof depth が tail から完全消滅
* next-future-minimum block の任意 internal cut で `tailExcess = localDepth + relativeCarry`
* `A` transition の開始 absolute Sturmian step `=1`
* 非自明 `A` tail の exact `(carry,excess)=(1,1)`
* 非自明 `C` の `step=0/1` と tail `(1,1)/(0,1)` の exact 二分岐
* 全 A/C block length の universal margin floor `log2(4/3)`
* 強い A-count bound `#A < log2(3/2) q + 1`
* 5 transitions ごとに `#A≤3`, `#C≥2`
* A 型 defect-normalized actual state の late compact annulus `L/8 < V_m < L/2`
* actual residue fraction `theta` の exact one-step recurrence と A の denominator-4 branch
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
* actual `2^(δ+2)` residue の有限 future-word 決定
* actual ordinary quotient と residue fraction による `V_m = k_m + theta_m` 分解
* natural completion endpoint から得る finite Hensel congruence と bounded lift 一意性
* `theta + (3^m/4) upsilon in Z` という finite real/dyadic compatibility
* 同じ actual `theta` に対する spacing `2/1` completion branch の finite separation
* Beatty scale `P_m in [1,2)` と `V_m=(R_m/4)P_m` の exact factorization
* critical escape weight `w_m=2^beattyIndex(m)/3^(m+1)` と `1/6<w_m<=1/3`
* actual normalized escape increment の exact factorization `a_m=w_m/2^delta_m`
* critical weight の Sturmian one-step recurrence と `w_m=1/(3P_m)`
* 2021 Lemma 41 の列と `criticalEscapeWeight` の exact floor/Cesàro reduction
* Ferrers 1-cell move の exact affine weight と finite chain weighted telescope
* normalized Ferrers cell weight と critical escape weight の exact row/defect factorization
* Global CST future minimum を基点とする one-sided defect floor
* A 型 ordinary quotient の一様有限化
* 任意に遠い future minimum 上での real target + finite Hensel 共通 anchor

として整理する。

real escape limit と natural/2進 completion を同一視しない。
両側が同じ finite exponent itinerary 上で同時に満たす exact 制約だけを記録する。
-/
