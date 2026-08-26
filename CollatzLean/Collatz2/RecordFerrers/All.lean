import CollatzLean.Collatz2.RecordFerrers.Core.FixedChordFiber
import CollatzLean.Collatz2.RecordFerrers.Core.ProfileDisplacement
import CollatzLean.Collatz2.RecordFerrers.Lattice.FerrersFiber
import CollatzLean.Collatz2.RecordFerrers.Lattice.FirstCrossingLattice
import CollatzLean.Collatz2.RecordFerrers.Lattice.WeightedArea
import CollatzLean.Collatz2.RecordFerrers.Record.RecordBlock
import CollatzLean.Collatz2.RecordFerrers.Record.RecordDecomposition
import CollatzLean.Collatz2.RecordFerrers.Record.Skeleton
import CollatzLean.Collatz2.RecordFerrers.Record.RecordWalls

import CollatzLean.Collatz2.RecordFerrers.Deformation.IntervalTransfer
import CollatzLean.Collatz2.RecordFerrers.Deformation.BlockReplacement
import CollatzLean.Collatz2.RecordFerrers.Deformation.SplitMerge
import CollatzLean.Collatz2.RecordFerrers.Deformation.BlockPermutation

import CollatzLean.Collatz2.RecordFerrers.Factorization.RecordFerrersFactorization
import CollatzLean.Collatz2.RecordFerrers.Factorization.InitialAnchorFirstCrossing
import CollatzLean.Collatz2.RecordFerrers.Factorization.RecordInverse
import CollatzLean.Collatz2.RecordFerrers.Factorization.PrimitiveReducedInverse
import CollatzLean.Collatz2.RecordFerrers.Factorization.BlockFerrersDeficit

import CollatzLean.Collatz2.RecordFerrers.Reconstruction.FerrersReconstruction
import CollatzLean.Collatz2.RecordFerrers.Reconstruction.LocalTranslationSet
import CollatzLean.Collatz2.RecordFerrers.Reconstruction.InformationBoundary

-- RF-A+1 ... RF-A+4: specialist-theory completion before Phase B migration.
import CollatzLean.Collatz2.RecordFerrers.Extensions.PublicAPI
import CollatzLean.Collatz2.RecordFerrers.Record.Canonicality
import CollatzLean.Collatz2.RecordFerrers.Lattice.MetricCompletion
import CollatzLean.Collatz2.RecordFerrers.Lattice.WeightedPotential
-- RF-A+5 ... RF-A+8: carry statistics, permutation symmetry,
-- H-independent FirstCrossing geometry, and lossless local translation coordinates.
import CollatzLean.Collatz2.RecordFerrers.Record.CarryStatistics
import CollatzLean.Collatz2.RecordFerrers.Deformation.InteriorPermutation
import CollatzLean.Collatz2.RecordFerrers.Lattice.UniversalFirstCrossingFiber
import CollatzLean.Collatz2.RecordFerrers.Reconstruction.TranslationCoordinates

-- RF-B0 ... RF-B4: 既存数学から得る制約を、どの情報からどこまで戻せるかを
-- 明示する輸送基盤と、FirstCrossing の整数座標化。
import CollatzLean.Collatz2.RecordFerrers.Transport.Certificates
import CollatzLean.Collatz2.RecordFerrers.Transport.InformationLedger
import CollatzLean.Collatz2.RecordFerrers.Lattice.PrefixCoordinates
import CollatzLean.Collatz2.RecordFerrers.Lattice.ClearanceSlack
import CollatzLean.Collatz2.RecordFerrers.Lattice.PrefixPolytope

-- RF-B5: Phase A の affine 加法保存則を整数座標へ輸送し、
-- `affineConst` に関する制約を word 側へ exact に戻す最初の試験層。
import CollatzLean.Collatz2.RecordFerrers.Lattice.AffineValuationTransport

-- RF-C1 ... RF-C4: 三ブロック交換整合性と 2×2 行列式の符号障害。
import CollatzLean.Collatz2.RecordFerrers.Deformation.ThreeBlockBraid
import CollatzLean.Collatz2.RecordFerrers.Matrix.TwoByTwoPlanarNetwork
import CollatzLean.Collatz2.RecordFerrers.Matrix.ExchangeMinor
import CollatzLean.Collatz2.RecordFerrers.Matrix.TotalNonnegativeObstruction

-- RF-D1 ... RF-D3: 有限候補族に対する既存分配束不等式、
-- 臨界屋根の整数倍格子点計数、family-level の容量矛盾。
import CollatzLean.Collatz2.RecordFerrers.Family.FourFunctionsFKG
import CollatzLean.Collatz2.RecordFerrers.Counting.EhrhartCounting
import CollatzLean.Collatz2.RecordFerrers.Family.FamilyObstruction


/-!
# Record–Ferrers Phase A umbrella (pre-record stage)

既存ファイルを変更しない add-only shadow layer。

順序:

`FixedChordFiber`
  → `ProfileDisplacement`
  → `FerrersFiber`
  → `FirstCrossingLattice`
  → `WeightedArea`

record point / record block / skeleton / deformation specializations は次段で追加する。
-/

/-!
# Record–Ferrers Phase A complete umbrella

既存ファイルを move / rewrite せずに作る add-only specialist layer の完成入口。

pre-record:
`FixedChordFiber -> ProfileDisplacement -> FerrersFiber -> FirstCrossingLattice -> WeightedArea`

record:
`RecordBlock -> RecordDecomposition -> Skeleton -> RecordWalls`

deformation:
`IntervalTransfer -> BlockReplacement -> SplitMerge -> BlockPermutation`

final:
`Factorization (forward + generic inverse + primitive/reduced inverse) -> Reconstruction`

既存 `Collatz2.RecordFerrers` facade や `Collatz2.lean` の import 切替は Phase B で行う。
-/


/-!
# Record–Ferrers RF-A+1 ... RF-A+4 extension

Phase B の import migration より前に、専門層内部で以下を完成させる。

* public API extraction
* canonical record length / skeleton theory
* distributive Ferrers lattice + metric / unit-chain geometry
* weighted affine potential / bottom-top extremal theory
-/


/-!
# Record–Ferrers RF-A+5 ... RF-A+8 extension

* RF-A+5: arbitrary carry statistics / zero-carry telescope / permutation invariant
* RF-A+6: arbitrary interior `List.Perm` symmetry and contextual affine exchange law
* RF-A+7: universal H-independent FirstCrossing fiber and terminal-depth chord shear
* RF-A+8: local decoration `≃` local translation spectrum and global `(length,B)` coordinates
-/


/-!
# Record–Ferrers RF-B0 ... RF-B4

既存数学を取り込む前に、制約を Collatz 側へ戻すための受け皿を整える。

* RF-B0: 性質決定・数値決定・必要条件・完全翻訳を区別する証明書語彙
* RF-B1: Phase A までに得た情報境界を証明書として台帳化
* RF-B2: Ferrers 図形と累積整数座標の exact 同値
* RF-B3: critical clearance と整数上限制約の余裕の exact 同一視
* RF-B4: universal FirstCrossing object と臨界上限制約つき整数点の exact 同値

この段階では外部の多面体定理そのものは仮定しない。
後続段階では RF-B4 の整数点空間を入口として、既存の整数幾何・行列式制約を接続する。
-/


/-!
# Record–Ferrers RF-B5

Phase A ですでに証明済みの weighted-area / `affineConst` 加法保存則を、
RF-B2〜B4 の累積整数座標へ輸送する。

* 累積整数座標に meet / join を導入
* 整数座標上の affine 値が4項保存則を満たすことを証明
* 累積整数座標だけで fixed-chord word の `affineConst` が決まることを証明書化
* `affineConst` に依存する任意の性質を整数座標へ完全翻訳
* 臨界上限制約つき整数点の meet / join と affine 4項保存則
* 任意の contracting depth に実現した FirstCrossing word へ4項等式を exact に戻す

これにより、後続の既存整数数学から affine 値に対する不可能条件が得られた場合、
その矛盾を fixed-chord / FirstCrossing word 側へ戻す正式な経路ができる。
-/


/-!
# Record–Ferrers RF-C1 ... RF-C4

既存の block permutation / contextual swap law を、三ブロック整合性と
2×2 行列式の符号制約へ接続する。

* RF-C1: 三ブロックの braid 型交換経路から、元の三ブロックだけに残る exact 恒等式を抽出
* RF-C2: `affineConst` と `coefficientGap` から 2×2 exchange path matrix を構成し、
  平面非交差経路網の全非負性を受け取る証明書を用意
* RF-C3: `blockExchangeDeterminant` を exchange 行列の 2×2 minor と exact に同一視
* RF-C4: 全非負性から determinant 非負を引き戻し、
  contextual block swap の向きまで Record–Ferrers / word 側へ戻す

RF-C2 では一般の平面グラフや LGV 補題そのものはまだ formalize しない。
具体的な network 構成が得られた場合、その path matrix の全非負性証明を
`ExchangePlanarNetworkCertificate` に渡せば RF-C4 の符号障害へ直結する。
-/


/-!
# Record–Ferrers RF-D1 ... RF-D3

有限な候補族全体へ既存数学の制約を掛け、単一図形の局所制約とは別の
「候補空間の容量不足」を矛盾の種として導入する。

* RF-D1: Mathlib の四関数定理・Daykin 不等式・FKG 不等式を Ferrers 分配束へ接続
* RF-D2: critical roof を整数倍した領域の格子点数 `ehrhartCount` を定義し、
  倍率単調性・有限箱上界・倍率1での FirstCrossing 整数点との exact 同値を証明
* RF-D3: 元の候補状態から critical Ferrers shape への単射証明書を導入し、
  - 候補数が倍率1の格子点数を超える場合の容量矛盾
  - Daykin が要求する meet/join 生成族の容量積との矛盾
  - FKG と strict に逆向きの family-level 不等式との矛盾
  を `False` まで閉じる

D2 の名称は Ehrhart 型計数を意識するが、この段階では一般の Ehrhart 多項式性を
仮定も主張もしない。後続でより強い既存計数定理が得られた場合、
`ehrhartCount` に対する上界・下界・漸近評価として差し込む。
-/
