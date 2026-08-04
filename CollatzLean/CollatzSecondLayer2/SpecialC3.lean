import CollatzLean.CollatzSecondLayer2.FirstCrossing
import CollatzLean.CollatzSecondLayer2.CaptureWindow
import CollatzLean.CollatzFirstLayer.CanonicalReplay

/-!
# zero-sync Special C3

capture正規化が最初のdeferred carryへ到達した時点で必要となる有限構造を、
移動q-window上に直接定義する。旧SecondLayerのterminal packetには依存しない。
-/

namespace CollatzSecondLayer2

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

/--
actual q-window上のzero-sync Special C3項。

* 下側指数は差深さとexactに一致する
* 上側では少なくとも1ビットcarryが持ち越される
* q-wordの開始・終点はcanonical代表
* 一つ下のcanonical predecessor shadowは負
-/
structure SpecialC3At (O : OddOrbit) (i q : ℕ) where
  length_pos : 0 < q
  difference : OddOrbit.WindowDifferenceData O i q
  lowerExact :
    ExactTwoFactor
      (3 * O.value i + 1)
      difference.depth
      (O.value (i + 1))
  upperDeferred :
    ∃ c : ℕ,
      3 * O.value (i + q) + 1 =
        2 ^ (difference.depth + 1) * c
  canonicalStart_eq :
    O.value i = canonicalStart (O.segmentWord i q)
  canonicalEnd_eq :
    O.value (i + q) = canonicalEnd (O.segmentWord i q)
  negativePredecessorShadow :
    predecessorShadow (O.segmentWord i q) < 0

namespace SpecialC3At

/-- Special C3項では下側actual指数は差深さに等しい。 -/
theorem lowerExponent_eq_depth
    {O : OddOrbit} {i q : ℕ}
    (S : SpecialC3At O i q) :
    O.exponent i = S.difference.depth := by
  have hactual :
      ExactTwoFactor
        (3 * O.value i + 1)
        (O.exponent i)
        (O.value (i + 1)) :=
    ⟨(O.step i).symm, O.value_odd (i + 1)⟩
  exact exactTwoFactor_exponent_unique hactual S.lowerExact

/-- Special C3項のq-windowはactual runである。 -/
theorem run
    {O : OddOrbit} {i q : ℕ}
    (_S : SpecialC3At O i q) :
    Runs (O.segmentWord i q) (O.value i) (O.value (i + q)) :=
  O.runs_segment i q

end SpecialC3At

/-- deferred windowとcanonical-negative条件からSpecial C3項を構成する。 -/
def specialC3At_of_deferred
    {O : OddOrbit} {i q : ℕ}
    (D : OddOrbit.DeferredWindowAt O i q)
    (hq : 0 < q)
    (hstart : O.value i = canonicalStart (O.segmentWord i q))
    (hend : O.value (i + q) = canonicalEnd (O.segmentWord i q))
    (hshadow : predecessorShadow (O.segmentWord i q) < 0) :
    SpecialC3At O i q := by
  have hlower :
      3 * O.value i + 1 =
        2 ^ D.depth * O.value (i + 1) := by
    rw [D.deferred]
    exact (O.step i).symm
  let C :=
    first_carry_equal_data
      D.difference
      D.oddPart_odd
      hlower
      (O.value_odd (i + 1))
  exact
    { length_pos := hq
      difference := D.toWindowDifferenceData
      lowerExact := ⟨hlower, O.value_odd (i + 1)⟩
      upperDeferred := ⟨C.quotient, C.equation⟩
      canonicalStart_eq := hstart
      canonicalEnd_eq := hend
      negativePredecessorShadow := hshadow }



/-- moving first-crossing列の部分列上に現れる漸近Special C3 refinement。 -/
structure SpecialC3SequenceData
    {O : OddOrbit} (F : MovingFirstCrossingData O) where
  select : ℕ → ℕ
  select_strict : StrictMono select
  offset : ℕ → ℕ
  length : ℕ → ℕ
  insideCrossing : ∀ j : ℕ,
    offset j + length j ≤ F.crossingLength (select j)
  special : ∀ j : ℕ,
    SpecialC3At O
      (F.minima.index (select j) + offset j)
      (length j)
  lengths_tend_to_infinity :
    ∀ M : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j → M < length j

/-- 指定moving first-crossing列がSpecial C3 refinementを持つ。 -/
def HasSpecialC3From
    {O : OddOrbit} (F : MovingFirstCrossingData O) : Prop :=
  Nonempty (SpecialC3SequenceData F)

/-- 指定軌道上のmoving first-crossing列の一つがSpecial C3 refinementを持つ。 -/
def HasSpecialC3On (O : OddOrbit) : Prop :=
  ∃ F : MovingFirstCrossingData O, HasSpecialC3From F

/-- 非有界odd-only軌道上にSpecial C3 refinementが存在する。 -/
def HasSpecialC3 : Prop :=
  ∃ O : OddOrbit, O.Unbounded ∧ HasSpecialC3On O

end CollatzSecondLayer2
