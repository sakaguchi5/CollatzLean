import CollatzLean.CollatzSecondLayer.C3Cylinder
import CollatzLean.CollatzFirstLayer.Terminal

/-!
# terminal pairと抽出障害

polynomial-small C3列から、第一層のterminal・center解析へ渡す有限pairを定義する。
抽出できない場合は、第二の明示的な例外として保存する。
-/

namespace CollatzSecondLayer

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

/-- 第一層のterminal suffix定理を適用できる有限データ。 -/
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

/-- C3 cylinder列から抽出された有限terminal chain。 -/
structure TerminalChainData {O : OddOrbit} (S : C3CylinderSequence O) where
  pair : List TerminalPairData
  pair_nonempty : pair ≠ []
  sourceIndex : List ℕ
  index_length : sourceIndex.length = pair.length
  /-- 各pairが元cylinder列に由来することを表す抽出証明。 -/
  extracted : Prop
  extracted_proof : extracted

/-- あるC3列から必要なterminal chainを抽出できない例外。 -/
def HasTerminalExtractionObstruction : Prop :=
  ∃ O : OddOrbit, ∃ S : C3CylinderSequence O,
    ¬ Nonempty (TerminalChainData S)

/-- terminal chainを抽出できるか、抽出障害が実在する。 -/
theorem terminalExtraction_split
    {O : OddOrbit} (S : C3CylinderSequence O) :
    HasTerminalExtractionObstruction ∨
      Nonempty (TerminalChainData S) := by
  classical
  by_cases h : Nonempty (TerminalChainData S)
  · exact Or.inr h
  · exact Or.inl ⟨O, S, h⟩

end CollatzSecondLayer
