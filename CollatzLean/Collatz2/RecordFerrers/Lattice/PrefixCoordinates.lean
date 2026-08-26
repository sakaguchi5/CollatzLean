import CollatzLean.Collatz2.RecordFerrers.Transport.InformationLedger

/-!
# Record–Ferrers RF-B2: 累積和整数座標

Ferrers 図形の各 column 高さを「prefix の累積整数座標」として独立化する。
この段階では外部の多面体理論を仮定せず、Ferrers 図形との exact な往復だけを閉じる。

隣接位置の差 `rise` も定義し、後で非負増分座標へ移すための局所分解を用意する。
-/

namespace Collatz2
namespace RecordFerrers

/--
`p` 個の cut における累積整数座標。
値は非減少なので、隣接差は常に非負の増分として読める。
-/
structure PrefixCoordinates (p : ℕ) where
  cumulative : Fin p → ℕ
  mono : Monotone cumulative

namespace PrefixCoordinates

@[ext] theorem ext
    {p : ℕ}
    {A B : PrefixCoordinates p}
    (h : ∀ i : Fin p, A.cumulative i = B.cumulative i) :
    A = B := by
  cases A with
  | mk a ha =>
      cases B with
      | mk b hb =>
          have hab : a = b := funext h
          subst b
          rfl

/-- 累積座標から Ferrers 図形を戻す。 -/
def toFerrersShape
    {p : ℕ}
    (C : PrefixCoordinates p) : FerrersShape p :=
  { column := C.cumulative
    mono := C.mono }

@[simp] theorem toFerrersShape_column
    {p : ℕ}
    (C : PrefixCoordinates p)
    (i : Fin p) :
    C.toFerrersShape.column i = C.cumulative i := rfl

/-- 二位置の間に増えた高さ。 -/
def rise
    {p : ℕ}
    (C : PrefixCoordinates p)
    (i j : Fin p) : ℕ :=
  C.cumulative j - C.cumulative i

/-- 前の累積値に増分を足すと後ろの累積値を exact に回収する。 -/
theorem cumulative_add_rise_eq
    {p : ℕ}
    (C : PrefixCoordinates p)
    {i j : Fin p}
    (hij : i ≤ j) :
    C.cumulative i + C.rise i j = C.cumulative j := by
  have hle : C.cumulative i ≤ C.cumulative j :=
    C.mono hij
  unfold rise
  omega

end PrefixCoordinates

namespace FerrersShape

/-- Ferrers 図形を累積整数座標として読む。 -/
def toPrefixCoordinates
    {p : ℕ}
    (S : FerrersShape p) : PrefixCoordinates p :=
  { cumulative := S.column
    mono := S.mono }

@[simp] theorem toPrefixCoordinates_cumulative
    {p : ℕ}
    (S : FerrersShape p)
    (i : Fin p) :
    S.toPrefixCoordinates.cumulative i = S.column i := rfl

/-- Ferrers 図形と累積整数座標は情報を失わず exact に同値。 -/
def equivPrefixCoordinates
    (p : ℕ) :
    FerrersShape p ≃ PrefixCoordinates p where
  toFun := fun S => S.toPrefixCoordinates
  invFun := fun C => C.toFerrersShape
  left_inv := by
    intro S
    apply FerrersShape.ext
    intro i
    rfl
  right_inv := by
    intro C
    apply PrefixCoordinates.ext
    intro i
    rfl

/-- 累積座標化は Ferrers 図形そのものを決定する情報である。 -/
theorem prefixCoordinates_determine_shape
    {p : ℕ} :
    Transport.DeterminesValue
      (fun S : FerrersShape p => S.toPrefixCoordinates)
      (fun S : FerrersShape p => S) := by
  intro A B h
  apply FerrersShape.ext
  intro i
  exact congrArg (fun C : PrefixCoordinates p => C.cumulative i) h

end FerrersShape

end RecordFerrers
end Collatz2
