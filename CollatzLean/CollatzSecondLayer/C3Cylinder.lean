import CollatzLean.CollatzSecondLayer.FirstCrossing

/-!
# polynomial-small canonical C3 cylinder

first-crossing列から特殊C3解析へ渡す有限cylinderデータを定義する。
center評価による多項式上界そのものは上流bridgeとして明示する。
-/

namespace CollatzSecondLayer

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

/-- moving anchorから切り出した一つのfirst-crossing cylinder。 -/
structure FirstCrossingCylinder (O : OddOrbit) where
  limit : MovingLimitData O
  sequenceIndex : ℕ
  length : ℕ
  firstCrossing :
    FirstCrossingAt O (limit.minima.index sequenceIndex) length

namespace FirstCrossingCylinder

/-- cylinderの指数語。 -/
def word {O : OddOrbit} (C : FirstCrossingCylinder O) : ExpWord :=
  O.segmentWord (C.limit.minima.index C.sequenceIndex) C.length

/-- cylinderの開始値。 -/
def start {O : OddOrbit} (C : FirstCrossingCylinder O) : ℕ :=
  O.value (C.limit.minima.index C.sequenceIndex)

/-- cylinderの終点。 -/
def finish {O : OddOrbit} (C : FirstCrossingCylinder O) : ℕ :=
  O.value (C.limit.minima.index C.sequenceIndex + C.length)

/-- cylinderは実際の有限実行である。 -/
theorem run {O : OddOrbit} (C : FirstCrossingCylinder O) :
    Runs C.word C.start C.finish := by
  exact O.runs_segment _ _

/-- future-minimum性により終点は開始値以上である。 -/
theorem terminal_ge_start {O : OddOrbit} (C : FirstCrossingCylinder O) :
    C.start ≤ C.finish := by
  exact C.limit.minima.futureMinimum C.sequenceIndex _ (by omega)

/-- cylinder語は非空である。 -/
theorem word_ne_nil {O : OddOrbit} (C : FirstCrossingCylinder O) :
    C.word ≠ [] := C.firstCrossing.nonempty

end FirstCrossingCylinder

/--
canonical代表そのものが実軌道の開始値になっているfirst-crossing cylinder。
`start_lt_modulus` はcenter評価と多項式上界から最終的に導く条件である。
-/
structure CanonicalC3Cylinder (O : OddOrbit) extends FirstCrossingCylinder O where
  start_lt_modulus :
    toFirstCrossingCylinder.start <
      residueModulus toFirstCrossingCylinder.word

namespace CanonicalC3Cylinder

/-- 法より小さい実開始値はcanonical最小代表そのものである。 -/
theorem start_eq_canonicalStart
    {O : OddOrbit} (C : CanonicalC3Cylinder O) :
    C.toFirstCrossingCylinder.start =
      canonicalStart C.toFirstCrossingCylinder.word := by
  let B := C.toFirstCrossingCylinder
  have hendOdd : Odd B.finish :=
    B.run.end_odd_of_ne_nil B.word_ne_nil
  have hmod := natural_start_mod_eq_canonicalStart
      B.run.realizes hendOdd
  have hreduce :
      B.start % residueModulus B.word = B.start :=
    Nat.mod_eq_of_lt C.start_lt_modulus
  rw [hreduce] at hmod
  exact hmod

end CanonicalC3Cylinder


/--
軌道や無限列を参照せずに保存できる、
一つのcanonical C3 cylinderの有限証人。
-/
structure CanonicalC3Witness where
  word : ExpWord
  start : ℕ
  finish : ℕ
  run : Runs word start finish
  firstCrossing : FirstCrossing word
  terminal_ge_start : start ≤ finish
  start_eq_canonicalStart : start = canonicalStart word

/-- actual cylinderから有限証人だけを切り出す。 -/
def CanonicalC3Cylinder.snapshot
    {O : OddOrbit} (C : CanonicalC3Cylinder O) : CanonicalC3Witness where
  word := C.toFirstCrossingCylinder.word
  start := C.toFirstCrossingCylinder.start
  finish := C.toFirstCrossingCylinder.finish
  run := C.toFirstCrossingCylinder.run
  firstCrossing := C.toFirstCrossingCylinder.firstCrossing
  terminal_ge_start := C.toFirstCrossingCylinder.terminal_ge_start
  start_eq_canonicalStart := C.start_eq_canonicalStart

/-- 長さと開始値に対する一様な多項式上界。 -/
def PolynomiallySmallCylinders
    {O : OddOrbit} (C : ℕ → CanonicalC3Cylinder O) : Prop :=
  ∃ K A : ℕ, ∀ j : ℕ,
    (C j).toFirstCrossingCylinder.start ≤
      K * ((C j).toFirstCrossingCylinder.length + 1) ^ A

/-- 長さが無限大へ進むpolynomial-small canonical C3 cylinder列。 -/
structure C3CylinderSequence (O : OddOrbit) where
  cylinder : ℕ → CanonicalC3Cylinder O
  lengths_tend_to_infinity :
    ∀ M : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      M < (cylinder j).toFirstCrossingCylinder.length
  polynomialSmall : PolynomiallySmallCylinders cylinder

/--
first-crossing列をcanonical・多項式小cylinder列へ昇格させるbridge。
これは二対数下界とcenter評価を形式化する場所である。
-/
def CylinderUpgradePrinciple : Prop :=
  ∀ O : OddOrbit, FirstCrossingSequenceData O →
    Nonempty (C3CylinderSequence O)

end CollatzSecondLayer
