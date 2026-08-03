import CollatzLean.CollatzSecondLayer.C3Cylinder
import CollatzLean.CollatzFirstLayer.Terminal

/-!
# terminal pairと抽出障害

polynomial-small C3列から、第一層のterminal・center解析へ渡す有限pairを定義する。
各pairについて、元cylinderの添字・語・開始値・終点を型のフィールドとして保存する。
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
  /-- `A` は実際のodd-only有限実行である。 -/
  runA : Runs A X YA
  /-- `R` は `A` の終点から続く実際のodd-only有限実行である。 -/
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

/-- 保存された実行証明から `A` のアフィン実現を再取得できる。 -/
theorem realizesA_of_run (T : TerminalPairData) :
    Realizes T.A T.X T.YA :=
  T.runA.realizes

/-- 保存された二つの実行証明から `A ++ R` のアフィン実現を再取得できる。 -/
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
一つのterminal pairと、そのpairを抽出した元cylinderを束ねる有限entry。

以前の任意の `extracted : Prop` と異なり、語・開始値・終点の一致を
具体的な等式として保持するため、無関係なpairをchainへ混入できない。
-/
structure TerminalChainEntry
    {O : OddOrbit} (S : C3CylinderSequence O) where
  pair : TerminalPairData
  sourceIndex : ℕ
  sourceRelation :
    pair.A ++ pair.R =
      (S.cylinder sourceIndex).snapshot.word
  sourceStart :
    pair.X =
      (S.cylinder sourceIndex).snapshot.start
  sourceFinish :
    pair.YAR =
      (S.cylinder sourceIndex).snapshot.finish

/-- C3 cylinder列から抽出された、由来情報付き有限terminal chain。 -/
structure TerminalChainData {O : OddOrbit} (S : C3CylinderSequence O) where
  entry : List (TerminalChainEntry S)
  entry_nonempty : entry ≠ []

namespace TerminalChainData

/-- chainに保存されたterminal pairの一覧。 -/
def pair {O : OddOrbit} {S : C3CylinderSequence O}
    (T : TerminalChainData S) : List TerminalPairData :=
  T.entry.map (fun E => E.pair)

/-- chainに保存された元cylinder添字の一覧。 -/
def sourceIndex {O : OddOrbit} {S : C3CylinderSequence O}
    (T : TerminalChainData S) : List ℕ :=
  T.entry.map (fun E => E.sourceIndex)

/-- entryが非空ならpair一覧も非空である。 -/
theorem pair_nonempty {O : OddOrbit} {S : C3CylinderSequence O}
    (T : TerminalChainData S) : T.pair ≠ [] := by
  intro hnil
  cases hentry : T.entry with
  | nil => exact T.entry_nonempty hentry
  | cons E Es => simpa [pair, hentry] using hnil

/-- pair一覧と元cylinder添字一覧の長さは一致する。 -/
theorem index_length {O : OddOrbit} {S : C3CylinderSequence O}
    (T : TerminalChainData S) :
    T.sourceIndex.length = T.pair.length := by
  simp [sourceIndex, pair]

end TerminalChainData

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
