import CollatzLean.CollatzSecondLayer3.FutureMinimumTerminalDichotomy
import CollatzLean.CollatzSupport.CofinalSelection

/-!
# future-minimum生成deep lower-replay tower

Generic deep lower-replay towerへ忘却する前に、次の三層を分離する。

1. `FutureMinimumDeepLowerReplayTowerData`
   future-minimum、非有界性、各長さのfirst-deferred normalizationを完全に保持する。
2. `CoherentDeepLowerReplayTowerData`
   共通anchor、全十分大きな長さ、terminal time、first-deferred最小性、
   replay quotientだけを保持する。
3. `GenericDeepLowerReplayTowerData`
   source-independentな局所deep lower replayと長さ発散だけを保持する。
-/

namespace CollatzSecondLayer3

open CollatzSupport
open CollatzCore
open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

/-- cutoff以後の全正長を列挙する標準長さ。 -/
def futureTailLength (cutoff j : ℕ) : ℕ :=
  cutoff + j + 1

/-- 標準長さは正。 -/
theorem futureTailLength_pos (cutoff j : ℕ) :
    0 < futureTailLength cutoff j := by
  unfold futureTailLength
  omega

/-- deferred terminalをprepared packetへ持ち上げる。 -/
noncomputable def deferredPreparedPacket
    {O : OddOrbit} {start length : ℕ}
    (E : O.DeferredWindowAt start length)
    (hlength : 0 < length) :
    O.PreparedWindowPacket start length :=
  { toWindowDifferenceData := E.toWindowDifferenceData
    length_pos := hlength
    depth_le_nextExponent := by
      rw [E.deferred] }

/-- deferred terminalのcanonical replay quotient。 -/
noncomputable def deferredReplayQuotient
    {O : OddOrbit} {start length : ℕ}
    (E : O.DeferredWindowAt start length)
    (hlength : 0 < length) : ℕ :=
  (deferredPreparedPacket E hlength).replayCoordinate.quotient

/-- positive quotientを持つdeferred terminalからdeep lower replayを構成する。 -/
noncomputable def genericDeepLowerReplayAt_of_deferred_quotient_pos
    {O : OddOrbit} {start length : ℕ}
    (E : O.DeferredWindowAt start length)
    (hlength : 0 < length)
    (hquotient : 0 < deferredReplayQuotient E hlength) :
    GenericDeepLowerReplayAt O start length := by
  let P := deferredPreparedPacket E hlength
  let C := P.replayCoordinate
  have hquotient' : 0 < C.quotient := by
    change
      0 < (deferredPreparedPacket E hlength).replayCoordinate.quotient
    exact hquotient
  have hlower := C.lowerNaturalRunReplay P.run hquotient'
  have hvalid : Valid (O.segmentWord start length) :=
    (O.runs_segment start length).valid
  have hlengthSteps :
      length ≤ twoSteps (O.segmentWord start length) := by
    have h := oddSteps_le_twoSteps hvalid
    simpa [oddSteps] using h
  have hmodulus :
      2 ^ (length + 1) ≤ residueModulus (O.segmentWord start length) := by
    unfold residueModulus
    exact Nat.pow_le_pow_right (by omega) (by omega)
  exact
    { lowerReplay := hlower
      modulus_deep := hmodulus }

/-- quotient 0のdeferred terminalはSpecial C3である。 -/
noncomputable def specialC3At_of_deferred_quotient_eq_zero
    {O : OddOrbit} {start length : ℕ}
    (E : O.DeferredWindowAt start length)
    (hlength : 0 < length)
    (hzero : deferredReplayQuotient E hlength = 0) :
    SpecialC3At O start length := by
  let P := deferredPreparedPacket E hlength
  let C := P.replayCoordinate
  have hzero' : C.quotient = 0 := by
    change
      (deferredPreparedPacket E hlength).replayCoordinate.quotient = 0
    exact hzero
  have hstart :
      O.value start = canonicalStart (O.segmentWord start length) := by
    exact C.start_eq_canonical_of_quotient_eq_zero hzero'
  have hend :
      O.value (start + length) =
        canonicalEnd (O.segmentWord start length) := by
    have h := C.finish_eq
    rw [hzero'] at h
    simpa using h
  have hrun₀ := P.run
  rw [hstart, hend] at hrun₀
  have hrun :
      Runs
        (O.segmentWord start length)
        (canonicalStart (O.segmentWord start length))
        (canonicalEnd (O.segmentWord start length)) := by
    exact hrun₀
  have hshadow : predecessorShadow (O.segmentWord start length) < 0 :=
    Runs.predecessorShadow_neg_of_canonical_run hrun
  exact specialC3At_of_deferred E hlength hstart hend hshadow

/-- Special C3でないdeferred terminalのquotientは正。 -/
theorem deferredReplayQuotient_pos_of_not_special
    {O : OddOrbit} {start length : ℕ}
    (E : O.DeferredWindowAt start length)
    (hlength : 0 < length)
    (hnot : ¬ Nonempty (SpecialC3At O start length)) :
    0 < deferredReplayQuotient E hlength := by
  by_contra hnonpos
  have hzero : deferredReplayQuotient E hlength = 0 := by
    omega
  exact hnot ⟨specialC3At_of_deferred_quotient_eq_zero E hlength hzero⟩

/-- first-deferred normalization terminalのreplay quotient。 -/
noncomputable def finiteNormalizationReplayQuotient
    {O : OddOrbit} {start length : ℕ}
    {D₀ : O.WindowDifferenceData start length}
    (F : O.FiniteCaptureNormalizationData D₀)
    (hlength : 0 < length) : ℕ :=
  deferredReplayQuotient F.terminal hlength

/-- Special C3でないfirst-deferred terminalのquotientは正。 -/
theorem finiteNormalizationReplayQuotient_pos_of_not_special
    {O : OddOrbit} {start length : ℕ}
    {D₀ : O.WindowDifferenceData start length}
    (F : O.FiniteCaptureNormalizationData D₀)
    (hlength : 0 < length)
    (hnot :
      ¬ Nonempty
        (SpecialC3At O (start + F.terminalTime) length)) :
    0 < finiteNormalizationReplayQuotient F hlength := by
  exact deferredReplayQuotient_pos_of_not_special F.terminal hlength hnot

/--
第1層。future-minimumから各長さのfirst-deferredまでの生成履歴を完全保存する。
`normalization j`自身がterminal time、terminal以前のcapture/synchronized、
terminal deferredを保持する。
-/
structure FutureMinimumDeepLowerReplayTowerData (O : OddOrbit) where
  unbounded : O.Unbounded
  anchor : ℕ
  futureMinimum : O.FutureMinimumAt anchor
  cutoff : ℕ
  normalization : ∀ j : ℕ,
    O.FiniteCaptureNormalizationData
      (futureMinimumWindowDifference
        O unbounded anchor (futureTailLength cutoff j)
        futureMinimum (futureTailLength_pos cutoff j))
  quotient_pos : ∀ j : ℕ,
    0 < finiteNormalizationReplayQuotient
      (normalization j) (futureTailLength_pos cutoff j)

namespace FutureMinimumDeepLowerReplayTowerData

/-- 第1層towerのj番目の長さ。 -/
def length {O : OddOrbit}
    (R : FutureMinimumDeepLowerReplayTowerData O) (j : ℕ) : ℕ :=
  futureTailLength R.cutoff j

/-- 第1層towerのj番目のterminal time。 -/
def terminalTime {O : OddOrbit}
    (R : FutureMinimumDeepLowerReplayTowerData O) (j : ℕ) : ℕ :=
  (R.normalization j).terminalTime

/-- 第1層towerのj番目のterminal開始位置。 -/
def start {O : OddOrbit}
    (R : FutureMinimumDeepLowerReplayTowerData O) (j : ℕ) : ℕ :=
  R.anchor + R.terminalTime j

/-- 第1層towerのj番目のreplay quotient。 -/
noncomputable def quotient {O : OddOrbit}
    (R : FutureMinimumDeepLowerReplayTowerData O) (j : ℕ) : ℕ :=
  finiteNormalizationReplayQuotient
    (R.normalization j) (futureTailLength_pos R.cutoff j)

/-- 第1層の各terminalはdeep lower replay。 -/
noncomputable def deep {O : OddOrbit}
    (R : FutureMinimumDeepLowerReplayTowerData O) (j : ℕ) :
    GenericDeepLowerReplayAt O (R.start j) (R.length j) := by
  exact genericDeepLowerReplayAt_of_deferred_quotient_pos
    (R.normalization j).terminal
    (futureTailLength_pos R.cutoff j)
    (R.quotient_pos j)

end FutureMinimumDeepLowerReplayTowerData

/--
第2層。生成に使ったfuture-minimum構造体を忘れ、排除に必要な数学情報だけを保持する。
全長さ`cutoff + j + 1`、共通anchor、terminal time、first-deferred最小性、
terminal quotientを保存する。
-/
structure CoherentDeepLowerReplayTowerData (O : OddOrbit) where
  anchor : ℕ
  cutoff : ℕ
  terminalTime : ℕ → ℕ
  before : ∀ j t : ℕ, t < terminalTime j →
    Nonempty
      (O.CapturedWindowAt
          (anchor + t) (futureTailLength cutoff j) ⊕
       O.SynchronizedWindowAt
          (anchor + t) (futureTailLength cutoff j))
  terminal : ∀ j : ℕ,
    O.DeferredWindowAt
      (anchor + terminalTime j) (futureTailLength cutoff j)
  quotient : ℕ → ℕ
  quotient_eq : ∀ j : ℕ,
    quotient j =
      deferredReplayQuotient
        (terminal j) (futureTailLength_pos cutoff j)
  quotient_pos : ∀ j : ℕ, 0 < quotient j

namespace CoherentDeepLowerReplayTowerData

/-- 第2層towerのj番目の長さ。 -/
def length {O : OddOrbit}
    (R : CoherentDeepLowerReplayTowerData O) (j : ℕ) : ℕ :=
  futureTailLength R.cutoff j

/-- 第2層towerのj番目のterminal開始位置。 -/
def start {O : OddOrbit}
    (R : CoherentDeepLowerReplayTowerData O) (j : ℕ) : ℕ :=
  R.anchor + R.terminalTime j

/-- 第2層の各terminalはdeep lower replay。 -/
noncomputable def deep {O : OddOrbit}
    (R : CoherentDeepLowerReplayTowerData O) (j : ℕ) :
    GenericDeepLowerReplayAt O (R.start j) (R.length j) := by
  have hquotient :
      0 < deferredReplayQuotient
        (R.terminal j) (futureTailLength_pos R.cutoff j) := by
    rw [← R.quotient_eq j]
    exact R.quotient_pos j
  exact genericDeepLowerReplayAt_of_deferred_quotient_pos
    (R.terminal j)
    (futureTailLength_pos R.cutoff j)
    hquotient

/-- 第2層から第3層generic towerへの忘却。 -/
noncomputable def toGeneric {O : OddOrbit}
    (R : CoherentDeepLowerReplayTowerData O) :
    GenericDeepLowerReplayTowerData O where
  start := fun j => R.start j
  length := fun j => R.length j
  deep := fun j => R.deep j
  lengths_tend_to_infinity := by
    intro M
    refine ⟨M, ?_⟩
    intro j hj
    unfold length futureTailLength
    omega

end CoherentDeepLowerReplayTowerData

namespace FutureMinimumDeepLowerReplayTowerData

/-- 第1層から第2層への履歴縮約。 -/
noncomputable def toCoherent {O : OddOrbit}
    (R : FutureMinimumDeepLowerReplayTowerData O) :
    CoherentDeepLowerReplayTowerData O where
  anchor := R.anchor
  cutoff := R.cutoff
  terminalTime := fun j => R.terminalTime j
  before := by
    intro j t ht
    exact (R.normalization j).before t ht
  terminal := fun j => (R.normalization j).terminal
  quotient := fun j => R.quotient j
  quotient_eq := fun _ => rfl
  quotient_pos := R.quotient_pos

/-- 第1層から第3層への合成忘却。 -/
noncomputable def toGeneric {O : OddOrbit}
    (R : FutureMinimumDeepLowerReplayTowerData O) :
    GenericDeepLowerReplayTowerData O :=
  R.toCoherent.toGeneric

end FutureMinimumDeepLowerReplayTowerData

/--
一つのfuture-minimumから、generic Special C3または生成履歴付きdeep lower-replayを抽出する。
Special C3がcofinalでなければ、あるcutoff以後の全長さが第1層towerを成す。
-/
theorem futureMinimum_generated_obstruction_dichotomy
    (O : OddOrbit)
    (hU : O.Unbounded)
    (anchor : ℕ)
    (hmin : O.FutureMinimumAt anchor) :
    Nonempty (GenericSpecialC3TowerData O) ∨
      Nonempty (FutureMinimumDeepLowerReplayTowerData O) := by
  classical
  let IsSpecial : ℕ → Prop :=
    fun j =>
      Nonempty
        (SpecialC3At O
          (futureMinimumTerminalStart
            O hU anchor (j + 1) hmin (by omega))
          (j + 1))
  by_cases hSpecial : Cofinally IsSpecial
  · let select₁ : ℕ → ℕ := Cofinally.select IsSpecial hSpecial
    have hselect₁Special : ∀ j : ℕ, IsSpecial (select₁ j) := by
      intro j
      exact Cofinally.select_spec IsSpecial hSpecial j
    let Bound : ℕ → ℕ → ℕ → Prop :=
      fun K A j =>
        O.value
            (futureMinimumTerminalStart
                O hU anchor (select₁ j + 1) hmin (by omega) +
              (select₁ j + 1)) ≤
          K * ((select₁ j + 1) + 1) ^ A
    by_cases hPolynomial :
        ∃ K A : ℕ, Cofinally (Bound K A)
    · obtain ⟨K, A, hBound⟩ := hPolynomial
      let select₂ : ℕ → ℕ :=
        Cofinally.select (Bound K A) hBound
      left
      refine ⟨{
        start := fun j =>
          futureMinimumTerminalStart
            O hU anchor (select₁ (select₂ j) + 1) hmin (by omega)
        length := fun j => select₁ (select₂ j) + 1
        special := ?_
        lengths_tend_to_infinity := ?_
        growth := .polynomial K A ?_
      }⟩
      · intro j
        exact Classical.choice (hselect₁Special (select₂ j))
      · intro M
        refine ⟨M, ?_⟩
        intro j hj
        have h₂ : j ≤ select₂ j :=
          Cofinally.select_ge (Bound K A) hBound j
        have h₁ : select₂ j ≤ select₁ (select₂ j) :=
          Cofinally.select_ge IsSpecial hSpecial (select₂ j)
        omega
      · intro j
        change Bound K A (select₂ j)
        exact Cofinally.select_spec (Bound K A) hBound j
    · left
      refine ⟨{
        start := fun j =>
          futureMinimumTerminalStart
            O hU anchor (select₁ j + 1) hmin (by omega)
        length := fun j => select₁ j + 1
        special := fun j => Classical.choice (hselect₁Special j)
        lengths_tend_to_infinity := ?_
        growth := .superPolynomial ?_
      }⟩
      · intro M
        refine ⟨M, ?_⟩
        intro j hj
        have hs : j ≤ select₁ j :=
          Cofinally.select_ge IsSpecial hSpecial j
        omega
      · intro K A
        have hnot : ¬ Cofinally (Bound K A) := by
          intro h
          exact hPolynomial ⟨K, A, h⟩
        obtain ⟨J, hJ⟩ :=
          Cofinally.eventually_not_of_not (Bound K A) hnot
        refine ⟨J, ?_⟩
        intro j hj
        have hn := hJ j hj
        dsimp [Bound] at hn ⊢
        omega
  · obtain ⟨N, hN⟩ :=
      Cofinally.eventually_not_of_not IsSpecial hSpecial
    right
    refine ⟨{
      unbounded := hU
      anchor := anchor
      futureMinimum := hmin
      cutoff := N
      normalization := fun j =>
        futureMinimumFirstDeferredData
          O hU anchor (futureTailLength N j) hmin
          (futureTailLength_pos N j)
      quotient_pos := ?_
    }⟩
    intro j
    let F :=
      futureMinimumFirstDeferredData
        O hU anchor (futureTailLength N j) hmin
        (futureTailLength_pos N j)
    apply finiteNormalizationReplayQuotient_pos_of_not_special F
      (futureTailLength_pos N j)
    have hn := hN (N + j) (by omega)
    simpa [IsSpecial, futureTailLength, futureMinimumTerminalStart, F,
      Nat.add_assoc] using hn

/-- 第1層を第2層へ縮約した最終二分岐。 -/
theorem futureMinimum_coherent_obstruction_dichotomy
    (O : OddOrbit)
    (hU : O.Unbounded)
    (anchor : ℕ)
    (hmin : O.FutureMinimumAt anchor) :
    Nonempty (GenericSpecialC3TowerData O) ∨
      Nonempty (CoherentDeepLowerReplayTowerData O) := by
  rcases futureMinimum_generated_obstruction_dichotomy O hU anchor hmin with
    hSpecial | hDeep
  · exact Or.inl hSpecial
  · rcases hDeep with ⟨D⟩
    exact Or.inr ⟨D.toCoherent⟩

/-- 第1層、第2層を経由して従来のgeneric二分岐へ忘却する。 -/
theorem futureMinimum_generic_obstruction_dichotomy_via_history
    (O : OddOrbit)
    (hU : O.Unbounded)
    (anchor : ℕ)
    (hmin : O.FutureMinimumAt anchor) :
    Nonempty (GenericSpecialC3TowerData O) ∨
      Nonempty (GenericDeepLowerReplayTowerData O) := by
  rcases futureMinimum_generated_obstruction_dichotomy O hU anchor hmin with
    hSpecial | hDeep
  · exact Or.inl hSpecial
  · rcases hDeep with ⟨D⟩
    exact Or.inr ⟨D.toGeneric⟩

end CollatzSecondLayer3
