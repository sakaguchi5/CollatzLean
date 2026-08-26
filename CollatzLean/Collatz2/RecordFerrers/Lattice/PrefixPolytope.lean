import CollatzLean.Collatz2.RecordFerrers.Lattice.ClearanceSlack

/-!
# Record–Ferrers RF-B4: 臨界上限制約つき整数点

FirstCrossing の universal Ferrers 図形を、

* 非減少な累積整数座標
* 各 cut で `criticalExcess` 以下

という純粋な整数制約へ移す。

このファイルでは外部の多面体定理はまだ導入せず、
`CriticalSubshape` および fixed-depth `FirstCrossingFiber` との exact 同値を閉じる。
これが後続の既存整数幾何を差し込む正式な入口になる。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-- critical roof 以下にある累積整数座標。 -/
structure PrefixPolytopePoint (p : ℕ) where
  coordinates : PrefixCoordinates p
  belowCritical : ∀ i : Fin p, coordinates.cumulative i ≤ criticalExcess i.1

namespace PrefixPolytopePoint

@[ext] theorem ext
    {p : ℕ}
    {A B : PrefixPolytopePoint p}
    (h : A.coordinates = B.coordinates) :
    A = B := by
  cases A
  cases B
  simp_all

/-- 整数点を critical subshape へ戻す。 -/
def toCriticalSubshape
    {p : ℕ}
    (P : PrefixPolytopePoint p) : CriticalSubshape p :=
  { shape := P.coordinates.toFerrersShape
    below := by
      intro i
      change P.coordinates.cumulative i ≤ criticalExcess i.1
      exact P.belowCritical i }

/-- 整数点の各 cut の余裕。 -/
def slack
    {p : ℕ}
    (P : PrefixPolytopePoint p)
    (i : Fin p) : ℕ :=
  P.coordinates.criticalSlack i

/-- 整数点では「累積高さ + 余裕 = critical excess」。 -/
theorem cumulative_add_slack
    {p : ℕ}
    (P : PrefixPolytopePoint p)
    (i : Fin p) :
    P.coordinates.cumulative i + P.slack i = criticalExcess i.1 := by
  unfold slack PrefixCoordinates.criticalSlack
  have hle := P.belowCritical i
  omega

end PrefixPolytopePoint

namespace CriticalSubshape

/-- critical subshape を臨界上限制約つき整数点へ送る。 -/
def toPrefixPolytopePoint
    {p : ℕ}
    (S : CriticalSubshape p) : PrefixPolytopePoint p :=
  { coordinates := S.shape.toPrefixCoordinates
    belowCritical := by
      intro i
      simpa [criticalShape] using S.below i }

end CriticalSubshape

namespace PrefixPolytopePoint

/-- universal FirstCrossing Ferrers object と整数点は exact に同値。 -/
def equivCriticalSubshape
    (p : ℕ) :
    CriticalSubshape p ≃ PrefixPolytopePoint p where
  toFun := fun S => S.toPrefixPolytopePoint
  invFun := fun P => P.toCriticalSubshape
  left_inv := by
    intro S
    apply CriticalSubshape.ext
    apply FerrersShape.ext
    intro i
    rfl
  right_inv := by
    intro P
    apply PrefixPolytopePoint.ext
    apply PrefixCoordinates.ext
    intro i
    rfl

end PrefixPolytopePoint

namespace FiberPoint

/-- fixed chord point が持つ累積整数座標。 -/
def toPrefixCoordinates
    {p H : ℕ}
    (x : FiberPoint p H) : PrefixCoordinates p :=
  x.toFerrersShape.toPrefixCoordinates

/--
fixed chord 上の FirstCrossing 条件は、各累積整数座標が critical roof 以下であることと同値。
-/
theorem firstCrossing_iff_prefixBounds
    {p H : ℕ}
    (x : FiberPoint p H)
    (hp : 0 < p)
    (hContract : ContractingChord p H) :
    FirstCrossing x.word ↔
      ∀ i : Fin p, x.toPrefixCoordinates.cumulative i ≤ criticalExcess i.1 := by
  rw [firstCrossing_iff_criticalSubshape x hp hContract]
  constructor
  · intro h i
    simpa [toPrefixCoordinates, criticalShape] using h i
  · intro h i
    simpa [toPrefixCoordinates, criticalShape] using h i

end FiberPoint

namespace FirstCrossingFiber

/--
任意の contracting depth における FirstCrossing fiber は、
同じ臨界上限制約つき整数点空間と exact に同値。
-/
def equivPrefixPolytopePoint
    {p H : ℕ}
    (hp : 0 < p)
    (hContract : ContractingChord p H) :
    FirstCrossingFiber p H ≃ PrefixPolytopePoint p :=
  (equivCriticalSubshape hp hContract).trans
    (PrefixPolytopePoint.equivCriticalSubshape p)

end FirstCrossingFiber

end RecordFerrers
end Collatz2
