import CollatzLean.Collatz2.RecordFerrers.Family.FourFunctionsFKG
import Mathlib.Data.Fintype.OfMap
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators

/-!
# Record–Ferrers RF-D2: 臨界屋根の整数倍と格子点計数

Ehrhart 理論で中心になる発想は、整数多面体を整数倍し、その格子点数を数えることにある。
現行 Mathlib には、この Record–Ferrers 領域へそのまま適用できる一般 Ehrhart 多項式 API を
仮定しない。そのためここでは多項式性を主張せず、まず必要な有限計数対象を exact に作る。

倍率 `scale` に対して

  cumulative(i) ≤ scale * criticalExcess(i)

を満たす非減少累積整数座標を `DilatedCriticalPoint p scale` とする。

このファイルで証明することは次の通り。

* 各倍率の点集合は有限
* その格子点数 `ehrhartCount` を定義
* 倍率を増やすと点数は減らない
* 単純な直方体による明示的上界
* 倍率 1 は RF-B4 の `PrefixPolytopePoint` と exact 同値
* したがって任意 contracting depth の FirstCrossing fiber も倍率 1 の点集合と exact 同値

後続で既存の格子点計数・生成関数・漸近評価を導入するときの正式な受け口にする。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/--
critical roof を `scale` 倍した上限制約の下にある累積整数座標。
`scale = 1` が現在の universal FirstCrossing 領域そのもの。
-/
structure DilatedCriticalPoint (p scale : ℕ) where
  coordinates : PrefixCoordinates p
  belowScaled :
    ∀ i : Fin p,
      coordinates.cumulative i ≤ scale * criticalExcess i.1

namespace DilatedCriticalPoint

@[ext] theorem ext
    {p scale : ℕ}
    {A B : DilatedCriticalPoint p scale}
    (h : A.coordinates = B.coordinates) :
    A = B := by
  cases A
  cases B
  simp_all

/--
各 cut の値は、最後の critical excess を使った一つの共通有限箱にも入る。
-/
theorem cumulative_le_globalBound
    {p scale : ℕ}
    (P : DilatedCriticalPoint p scale)
    (i : Fin p) :
    P.coordinates.cumulative i ≤ scale * criticalExcess p := by
  have hCrit : criticalExcess i.1 ≤ criticalExcess p :=
    criticalExcess_mono (Nat.le_of_lt i.isLt)
  have hScaled :
      scale * criticalExcess i.1 ≤ scale * criticalExcess p :=
    Nat.mul_le_mul_left scale hCrit
  exact (P.belowScaled i).trans hScaled

/--
有限性を示すため、各点を有限箱
`Fin p → Fin (scale * criticalExcess p + 1)` に埋め込む。
-/
def finiteCode
    {p scale : ℕ}
    (P : DilatedCriticalPoint p scale) :
    Fin p → Fin (scale * criticalExcess p + 1) :=
  fun i =>
    ⟨P.coordinates.cumulative i, by
      have h := P.cumulative_le_globalBound i
      omega⟩

/-- 上の有限箱符号化は単射。 -/
theorem finiteCode_injective
    {p scale : ℕ} :
    Function.Injective
      (fun P : DilatedCriticalPoint p scale => P.finiteCode) := by
  intro A B h
  apply DilatedCriticalPoint.ext
  apply PrefixCoordinates.ext
  intro i
  have hi := congrFun h i
  exact congrArg Fin.val hi

/-- 各倍率の格子点集合は有限。 -/
noncomputable instance instFintype
    (p scale : ℕ) : Fintype (DilatedCriticalPoint p scale) :=
  Fintype.ofInjective
    (fun P : DilatedCriticalPoint p scale => P.finiteCode)
    finiteCode_injective

/-- 有限集合 API を使うための等号判定。 -/
noncomputable instance instDecidableEq
    (p scale : ℕ) : DecidableEq (DilatedCriticalPoint p scale) :=
  Classical.decEq _

/--
小さい倍率の点を、大きい倍率の同じ座標へ埋め込む。
-/
def scaleMap
    {p small large : ℕ}
    (hScale : small ≤ large)
    (P : DilatedCriticalPoint p small) :
    DilatedCriticalPoint p large :=
  { coordinates := P.coordinates
    belowScaled := by
      intro i
      exact
        (P.belowScaled i).trans
          (Nat.mul_le_mul_right (criticalExcess i.1) hScale) }

/-- 倍率拡大写像は単射。 -/
theorem scaleMap_injective
    {p small large : ℕ}
    (hScale : small ≤ large) :
    Function.Injective
      (scaleMap (p := p) hScale) := by
  intro A B h
  have hCoord :
      (scaleMap hScale A).coordinates =
        (scaleMap hScale B).coordinates :=
    congrArg DilatedCriticalPoint.coordinates h
  apply DilatedCriticalPoint.ext
  simpa [scaleMap] using hCoord

end DilatedCriticalPoint

/--
critical roof の `scale` 倍領域にある格子点数。
Ehrhart 型の計数関数として使うが、この時点では多項式性は主張しない。
-/
noncomputable def ehrhartCount (p scale : ℕ) : ℕ :=
  Fintype.card (DilatedCriticalPoint p scale)

/-- 倍率を増やすと格子点数は減らない。 -/
theorem ehrhartCount_mono
    {p small large : ℕ}
    (hScale : small ≤ large) :
    ehrhartCount p small ≤ ehrhartCount p large := by
  classical
  have hCard :=
    Fintype.card_le_of_injective
      (DilatedCriticalPoint.scaleMap (p := p) hScale)
      (DilatedCriticalPoint.scaleMap_injective (p := p) hScale)
  simpa [ehrhartCount] using hCard

/--
全座標を共通上界だけで自由に選んだ有限箱を使う粗い上界。
単調性などを捨てても

`ehrhartCount p scale ≤ (scale * criticalExcess p + 1)^p`

である。
-/
theorem ehrhartCount_le_box
    (p scale : ℕ) :
    ehrhartCount p scale ≤
      (scale * criticalExcess p + 1) ^ p := by
  classical
  have hCard :=
    Fintype.card_le_of_injective
      (fun P : DilatedCriticalPoint p scale => P.finiteCode)
      (DilatedCriticalPoint.finiteCode_injective
        (p := p) (scale := scale))
  simpa [ehrhartCount, Fintype.card_fun] using hCard

/--
RF-B4 の臨界上限制約つき整数点と、倍率 1 の格子点は exact に同値。
-/
noncomputable def prefixPolytopeEquivScaleOne
    (p : ℕ) :
    PrefixPolytopePoint p ≃ DilatedCriticalPoint p 1 where
  toFun := fun P =>
    { coordinates := P.coordinates
      belowScaled := by
        intro i
        simpa using P.belowCritical i }
  invFun := fun P =>
    { coordinates := P.coordinates
      belowCritical := by
        intro i
        simpa using P.belowScaled i }
  left_inv := by
    intro P
    apply PrefixPolytopePoint.ext
    rfl
  right_inv := by
    intro P
    apply DilatedCriticalPoint.ext
    rfl

/-- `PrefixPolytopePoint p` も有限であることを倍率 1 表現から得る。 -/
noncomputable instance instFintypePrefixPolytopePoint
    (p : ℕ) : Fintype (PrefixPolytopePoint p) :=
  Fintype.ofEquiv
    (DilatedCriticalPoint p 1)
    (prefixPolytopeEquivScaleOne p).symm

/-- `PrefixPolytopePoint` を有限集合で使うための等号判定。 -/
noncomputable instance instDecidableEqPrefixPolytopePoint
    (p : ℕ) : DecidableEq (PrefixPolytopePoint p) :=
  Classical.decEq _

/-- 倍率 1 の格子点数は universal FirstCrossing 整数点の個数そのもの。 -/
theorem ehrhartCount_one
    (p : ℕ) :
    ehrhartCount p 1 = Fintype.card (PrefixPolytopePoint p) := by
  classical
  simpa [ehrhartCount] using
    (Fintype.card_congr (prefixPolytopeEquivScaleOne p)).symm

namespace FirstCrossingFiber

/--
任意の contracting terminal depth の FirstCrossing fiber は、
倍率 1 の格子点空間と exact に同値。

したがって D2 の倍率 1 計数は terminal depth `H` に依存しない intrinsic count である。
-/
noncomputable def equivDilatedCriticalOne
    {p H : ℕ}
    (hp : 0 < p)
    (hContract : ContractingChord p H) :
    FirstCrossingFiber p H ≃ DilatedCriticalPoint p 1 :=
  (equivPrefixPolytopePoint hp hContract).trans
    (prefixPolytopeEquivScaleOne p)

end FirstCrossingFiber

end RecordFerrers
end Collatz2
