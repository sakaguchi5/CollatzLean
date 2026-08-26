import CollatzLean.Collatz2.RecordFerrers.Lattice.PrefixPolytope
import CollatzLean.Collatz2.RecordFerrers.Lattice.WeightedPotential

/-!
# Record–Ferrers RF-B5: affine 値の加法保存則と整数座標への輸送

Phase A ですでに得られている

`weightedArea(meet) + weightedArea(join) = weightedArea(A) + weightedArea(B)`

を、RF-B2〜B4 の累積整数座標へ移す。

このファイルの目的は新しい Ferrers 等式を重複して証明することではない。
既存の加法保存則を

* 累積整数座標
* 臨界上限制約つき整数点
* fixed-chord word の `affineConst`

へ順に運び、「この整数情報からどこまで戻せるか」を証明書として固定する。
-/

namespace Collatz2
namespace RecordFerrers

open Word

namespace PrefixCoordinates

/-- 二つの累積整数座標の各 cut で小さい方を取る。 -/
def meet
    {p : ℕ}
    (A B : PrefixCoordinates p) : PrefixCoordinates p :=
  { cumulative := fun i => min (A.cumulative i) (B.cumulative i)
    mono := by
      intro i j hij
      exact min_le_min (A.mono hij) (B.mono hij) }

/-- 二つの累積整数座標の各 cut で大きい方を取る。 -/
def join
    {p : ℕ}
    (A B : PrefixCoordinates p) : PrefixCoordinates p :=
  { cumulative := fun i => max (A.cumulative i) (B.cumulative i)
    mono := by
      intro i j hij
      exact max_le_max (A.mono hij) (B.mono hij) }

@[simp] theorem meet_cumulative
    {p : ℕ}
    (A B : PrefixCoordinates p)
    (i : Fin p) :
    (meet A B).cumulative i = min (A.cumulative i) (B.cumulative i) := rfl

@[simp] theorem join_cumulative
    {p : ℕ}
    (A B : PrefixCoordinates p)
    (i : Fin p) :
    (join A B).cumulative i = max (A.cumulative i) (B.cumulative i) := rfl

/--
累積整数座標だけから計算する affine 値。
Ferrers 図形へ戻した weighted area と baseline の和であり、
fixed-chord word を実現したときの genuine `affineConst` と一致する。
-/
def affineBudget
    {p : ℕ}
    (C : PrefixCoordinates p) : ℕ :=
  baseAffineConst p + weightedArea C.toFerrersShape

@[simp] theorem toFerrersShape_meet
    {p : ℕ}
    (A B : PrefixCoordinates p) :
    (meet A B).toFerrersShape =
      FerrersShape.meet A.toFerrersShape B.toFerrersShape := by
  apply FerrersShape.ext
  intro i
  rfl

@[simp] theorem toFerrersShape_join
    {p : ℕ}
    (A B : PrefixCoordinates p) :
    (join A B).toFerrersShape =
      FerrersShape.join A.toFerrersShape B.toFerrersShape := by
  apply FerrersShape.ext
  intro i
  rfl

/--
累積整数座標上でも affine 値は meet/join に対して加法保存則を満たす。
これは Phase A の weighted-area valuation を整数座標へ exact に移したもの。
-/
theorem affineBudget_meet_add_join
    {p : ℕ}
    (A B : PrefixCoordinates p) :
    (meet A B).affineBudget + (join A B).affineBudget =
      A.affineBudget + B.affineBudget := by
  have hVal :
      weightedArea (meet A B).toFerrersShape +
          weightedArea (join A B).toFerrersShape =
        weightedArea A.toFerrersShape + weightedArea B.toFerrersShape := by
    rw [toFerrersShape_meet, toFerrersShape_join]
    exact weightedArea_meet_add_join
      A.toFerrersShape B.toFerrersShape
  unfold affineBudget
  omega

end PrefixCoordinates

namespace FiberPoint

/--
fixed chord の word の `affineConst` は、その累積整数座標の affine 値そのもの。
開始値や実軌道値を復元せず、必要な数値だけを exact に戻す。
-/
theorem affineConst_eq_prefixAffineBudget
    {p H : ℕ}
    (x : FiberPoint p H) :
    affineConst x.word = x.toPrefixCoordinates.affineBudget := by
  rw [affineConst_eq_base_add_weightedArea x]
  rfl

/--
累積整数座標は fixed-chord word の `affineConst` を決定する。
word 全体の完全復元を使わなくてもよい数値決定証明書。
-/
theorem prefixCoordinates_determine_affineConst
    {p H : ℕ} :
    Transport.DeterminesValue
      (fun x : FiberPoint p H => x.toPrefixCoordinates)
      (fun x : FiberPoint p H => affineConst x.word) := by
  intro x y hxy
  change x.toPrefixCoordinates = y.toPrefixCoordinates at hxy
  change affineConst x.word = affineConst y.word
  rw [x.affineConst_eq_prefixAffineBudget,
      y.affineConst_eq_prefixAffineBudget]
  exact congrArg PrefixCoordinates.affineBudget hxy

/--
`affineConst` だけに依存する任意の性質は、累積整数座標上の affine 値へ完全翻訳できる。
等式・不等式・合同条件などを後からこの一つの証明書で引き戻せる。
-/
theorem prefixCoordinates_exactTranslation_affineProperty
    {p H : ℕ}
    (Q : ℕ → Prop) :
    Transport.ExactTranslation
      (fun x : FiberPoint p H => x.toPrefixCoordinates)
      (fun x : FiberPoint p H => Q (affineConst x.word))
      (fun C : PrefixCoordinates p => Q C.affineBudget) := by
  intro x
  change
    Q (affineConst x.word) ↔
      Q x.toPrefixCoordinates.affineBudget
  rw [x.affineConst_eq_prefixAffineBudget]

end FiberPoint

namespace PrefixPolytopePoint

/--
臨界上限制約つき整数点の meet。
各 cut で小さい方を取るため、critical roof 以下という条件は自動的に保たれる。
-/
def meet
    {p : ℕ}
    (A B : PrefixPolytopePoint p) : PrefixPolytopePoint p :=
  { coordinates := PrefixCoordinates.meet A.coordinates B.coordinates
    belowCritical := by
      intro i
      exact le_trans (min_le_left _ _) (A.belowCritical i) }

/--
臨界上限制約つき整数点の join。
両方が critical roof 以下なら、各 cut の最大値も critical roof 以下に残る。
-/
def join
    {p : ℕ}
    (A B : PrefixPolytopePoint p) : PrefixPolytopePoint p :=
  { coordinates := PrefixCoordinates.join A.coordinates B.coordinates
    belowCritical := by
      intro i
      exact max_le (A.belowCritical i) (B.belowCritical i) }

@[simp] theorem meet_coordinates
    {p : ℕ}
    (A B : PrefixPolytopePoint p) :
    (meet A B).coordinates = PrefixCoordinates.meet A.coordinates B.coordinates := rfl

@[simp] theorem join_coordinates
    {p : ℕ}
    (A B : PrefixPolytopePoint p) :
    (join A B).coordinates = PrefixCoordinates.join A.coordinates B.coordinates := rfl

/-- 臨界上限制約つき整数点が持つ affine 値。 -/
def affineValue
    {p : ℕ}
    (P : PrefixPolytopePoint p) : ℕ :=
  P.coordinates.affineBudget

/-- 臨界上限制約つき整数点でも affine 値の4項保存則が exact に成り立つ。 -/
theorem affineValue_meet_add_join
    {p : ℕ}
    (A B : PrefixPolytopePoint p) :
    (meet A B).affineValue + (join A B).affineValue =
      A.affineValue + B.affineValue := by
  simpa [affineValue, meet, join] using
    PrefixCoordinates.affineBudget_meet_add_join A.coordinates B.coordinates

/--
整数点を任意の contracting terminal depth に実現した fixed-chord word。
整数点から word 全体を直接復元することを目的とせず、
後続の制約を word 側へ戻す標準の実現写像として使う。
-/
def toFiberPoint
    {p : ℕ}
    (P : PrefixPolytopePoint p)
    (H : ℕ)
    (hp : 0 < p)
    (hContract : ContractingChord p H) : FiberPoint p H :=
  P.toCriticalSubshape.toFiberPoint H hp hContract

/-- 上の標準実現は FirstCrossing。 -/
theorem toFiberPoint_firstCrossing
    {p : ℕ}
    (P : PrefixPolytopePoint p)
    (H : ℕ)
    (hp : 0 < p)
    (hContract : ContractingChord p H) :
    FirstCrossing (P.toFiberPoint H hp hContract).word := by
  exact P.toCriticalSubshape.toFiberPoint_firstCrossing H hp hContract

/--
整数点の affine 値は、任意の contracting depth に実現した word の
`affineConst` と exact に一致する。
-/
theorem affineConst_toFiberPoint_eq_affineValue
    {p : ℕ}
    (P : PrefixPolytopePoint p)
    (H : ℕ)
    (hp : 0 < p)
    (hContract : ContractingChord p H) :
    affineConst (P.toFiberPoint H hp hContract).word = P.affineValue := by
  rw [affineConst_eq_base_add_weightedArea]
  unfold toFiberPoint
  rw [P.toCriticalSubshape.toFiberPoint_toFerrersShape H hp hContract]
  rfl

/--
整数点の meet/join 4項保存則を、任意の contracting depth の
4つの FirstCrossing word にそのまま戻す。

したがって今後、整数側でこの4項等式と両立しない条件が得られれば、
対応する FirstCrossing word 族も存在できない。
-/
theorem affineConst_meet_add_join
    {p H : ℕ}
    (A B : PrefixPolytopePoint p)
    (hp : 0 < p)
    (hContract : ContractingChord p H) :
    affineConst ((meet A B).toFiberPoint H hp hContract).word +
        affineConst ((join A B).toFiberPoint H hp hContract).word =
      affineConst (A.toFiberPoint H hp hContract).word +
        affineConst (B.toFiberPoint H hp hContract).word := by
  rw [affineConst_toFiberPoint_eq_affineValue (meet A B) H hp hContract,
      affineConst_toFiberPoint_eq_affineValue (join A B) H hp hContract,
      affineConst_toFiberPoint_eq_affineValue A H hp hContract,
      affineConst_toFiberPoint_eq_affineValue B H hp hContract]
  exact affineValue_meet_add_join A B

end PrefixPolytopePoint

end RecordFerrers
end Collatz2
