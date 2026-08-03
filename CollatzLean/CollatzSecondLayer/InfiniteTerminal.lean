import CollatzLean.CollatzSecondLayer.C3Cylinder
import CollatzLean.CollatzFirstLayer.Terminal

/-!
# 無限terminal抽出

polynomial-small canonical C3 cylinder列から、terminal pairを無限部分列として
抽出するためのデータを定義する。

有限Listへ落とさず、元cylinderの添字、語、開始値、終点、長さの発散を
列全体にわたって保持する。
-/

namespace CollatzSecondLayer

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

/-- 第一層のterminal suffix定理を適用できる有限terminal pair。 -/
structure TerminalPairData where
  A : ExpWord
  R : ExpWord
  X : ℕ
  YA : ℕ
  YAR : ℕ
  lambdaA : ℕ
  lambdaAR : ℕ
  uA : ℕ
  uAR : ℕ
  gap : ℕ
  runA : Runs A X YA
  runR : Runs R YA YAR
  realizesA : Realizes A X YA
  realizesAR : Realizes (A ++ R) X YAR
  returnA : IsReturn X YA lambdaA uA
  returnAR : IsReturn X YAR lambdaAR uAR
  alpha_gap :
    alpha (A ++ R) lambdaAR = alpha A lambdaA + gap
  gap_pos : 0 < gap
  total_twoSteps_pos : 0 < twoSteps (A ++ R)
  detA_ne : determinant A ≠ 0
  detR_ne : determinant R ≠ 0

namespace TerminalPairData

/-- 保存された実行証明から `A` の実現式を再取得する。 -/
theorem realizesA_of_run (T : TerminalPairData) :
    Realizes T.A T.X T.YA :=
  T.runA.realizes

/-- 保存された連続実行から `A ++ R` の実現式を再取得する。 -/
theorem realizesAR_of_runs (T : TerminalPairData) :
    Realizes (T.A ++ T.R) T.X T.YAR := by
  exact realizes_append T.runA.realizes T.runR.realizes

/-- terminal pairのomegaはanchor深さの2冪と奇数核へ分解される。 -/
theorem oddKernel (T : TerminalPairData) :
    ∃ kappa : ℤ, Odd kappa ∧
      omega T.A T.R = (2 : ℤ) ^ T.lambdaA * kappa := by
  exact terminal_suffix_factorization
    T.realizesA T.realizesAR T.returnA T.returnAR
    T.alpha_gap T.gap_pos T.total_twoSteps_pos

/-- terminal pairのcenter差分解。 -/
theorem centerDifference (T : TerminalPairData) :
    ∃ kappa : ℤ, Odd kappa ∧
      center T.A - center T.R =
        (((2 : ℚ) ^ T.lambdaA) * (kappa : ℚ)) /
          ((determinant T.A : ℚ) * (determinant T.R : ℚ)) := by
  exact terminal_center_difference
    T.realizesA T.realizesAR T.returnA T.returnAR
    T.alpha_gap T.gap_pos T.total_twoSteps_pos
    T.detA_ne T.detR_ne

end TerminalPairData

/--
canonical C3 cylinder列から抽出された無限terminal部分列。

`sourceIndex` は元列の狭義単調な添字であり、各terminal pairはそのcylinderの
全語、開始値、終点に一致する。さらに、抽出後も元cylinder長が無限大へ進む。
-/
structure InfiniteTerminalExtraction
    {O : OddOrbit} (S : C3CylinderSequence O) where
  sourceIndex : ℕ → ℕ
  sourceIndex_strict : StrictMono sourceIndex
  pair : ℕ → TerminalPairData
  sourceRelation : ∀ n : ℕ,
    (pair n).A ++ (pair n).R =
      (S.cylinder (sourceIndex n)).snapshot.word
  sourceStart : ∀ n : ℕ,
    (pair n).X =
      (S.cylinder (sourceIndex n)).snapshot.start
  sourceFinish : ∀ n : ℕ,
    (pair n).YAR =
      (S.cylinder (sourceIndex n)).snapshot.finish
  sourceLengths_tend_to_infinity :
    ∀ M : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      M < (S.cylinder (sourceIndex j)).toFirstCrossingCylinder.length

/-- 無限terminal部分列を抽出できないことが実在する。 -/
def HasInfiniteTerminalExtractionObstruction : Prop :=
  ∃ O : OddOrbit, ∃ S : C3CylinderSequence O,
    ¬ Nonempty (InfiniteTerminalExtraction S)

/--
一つのC3 cylinder列について、無限terminal抽出が得られるか、
その抽出不能性が第二の例外として実在する。
-/
theorem infiniteTerminalExtraction_split
    {O : OddOrbit} (S : C3CylinderSequence O) :
    HasInfiniteTerminalExtractionObstruction ∨
      Nonempty (InfiniteTerminalExtraction S) := by
  classical
  by_cases h : Nonempty (InfiniteTerminalExtraction S)
  · exact Or.inr h
  · exact Or.inl ⟨O, S, h⟩

end CollatzSecondLayer
