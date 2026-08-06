import CollatzLean.CollatzSecondLayer3.FutureMinimumDeepLowerReplay
import CollatzLean.CollatzFirstLayer.ShadowReanchoring

import Mathlib.Tactic.Linarith

/-!
# future-minimum生成Special C3 towerとnegative shadow re-anchoring

Generic Special C3 towerへ忘却する前に、次の情報を保存する。

* 共通future-minimum anchor
* 各選択長のfirst-deferred normalization全体
* terminal以前のcapture/synchronized履歴
* terminal deferredとSpecial C3証明
* negative predecessor centerと最初のcanonical re-anchoring
* endpoint growth profile

actual orbit上のconnectorとre-anchored shadow pathの最終比較は、このファイルでは行わない。
-/

namespace CollatzCore.SpecialC3At

open CollatzSupport
open CollatzCore
open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

/-- Special C3 wordの奇数ステップ数はwindow長に等しい。 -/
theorem word_oddSteps_eq
    {O : OddOrbit} {start length : ℕ}
    (_S : SpecialC3At O start length) :
    oddSteps (O.segmentWord start length) = length := by
  simp [oddSteps]

/-- Special C3 endpointは`2 * 3^length`より小さい。 -/
theorem endpoint_lt_two_mul_threePow
    {O : OddOrbit} {start length : ℕ}
    (S : SpecialC3At O start length) :
    O.value (start + length) < 2 * 3 ^ length := by
  have hs := S.negativePredecessorShadow
  unfold predecessorShadow at hs
  rw [← S.canonicalEnd_eq, S.word_oddSteps_eq] at hs
  have hz :
      (O.value (start + length) : ℤ) <
        2 * (3 : ℤ) ^ length := by
    omega
  exact_mod_cast hz

/-- Special C3 predecessor shadowの正の大きさ。 -/
def shadowMagnitude
    {O : OddOrbit} {start length : ℕ}
    (_S : SpecialC3At O start length) : ℕ :=
  2 * 3 ^ length - O.value (start + length)

/-- predecessor shadow magnitudeは正。 -/
theorem shadowMagnitude_pos
    {O : OddOrbit} {start length : ℕ}
    (S : SpecialC3At O start length) :
    0 < S.shadowMagnitude := by
  unfold shadowMagnitude
  exact Nat.sub_pos_of_lt S.endpoint_lt_two_mul_threePow

/-- predecessor shadowをmagnitudeでexactに表す。 -/
theorem predecessorShadow_eq_neg_shadowMagnitude
    {O : OddOrbit} {start length : ℕ}
    (S : SpecialC3At O start length) :
    predecessorShadow (O.segmentWord start length) =
      -(S.shadowMagnitude : ℤ) := by
  have hlt := S.endpoint_lt_two_mul_threePow
  have hmagZ :
      (S.shadowMagnitude : ℤ) =
        2 * (3 : ℤ) ^ length -
          (O.value (start + length) : ℤ) := by
    unfold shadowMagnitude
    rw [Nat.cast_sub (Nat.le_of_lt hlt)]
    push_cast
    ring
  unfold predecessorShadow
  rw [← S.canonicalEnd_eq]
  rw [S.word_oddSteps_eq]
  rw [hmagZ]
  ring

/-- upper deferred equationに現れるquotient。 -/
noncomputable def upperCarryQuotient
    {O : OddOrbit} {start length : ℕ}
    (S : SpecialC3At O start length) : ℕ :=
  Classical.choose S.upperDeferred

/-- upper deferred quotientの定義方程式。 -/
theorem upperCarryQuotient_equation
    {O : OddOrbit} {start length : ℕ}
    (S : SpecialC3At O start length) :
    3 * O.value (start + length) + 1 =
      2 ^ (S.difference.depth + 1) * S.upperCarryQuotient :=
  Classical.choose_spec S.upperDeferred

/-- Special C3の差深さは正。 -/
theorem depth_pos
    {O : OddOrbit} {start length : ℕ}
    (S : SpecialC3At O start length) :
    0 < S.difference.depth := by
  rw [← S.lowerExponent_eq_depth]
  exact O.exponent_pos start

/-- Special C3 shadowの最初のsigned step後のmagnitude。 -/
noncomputable def firstShadowMagnitude
    {O : OddOrbit} {start length : ℕ}
    (S : SpecialC3At O start length) : ℕ :=
  3 ^ (length + 1) -
    2 ^ S.difference.depth * S.upperCarryQuotient

/-- first shadow magnitudeの減算は真の減算である。 -/
theorem upperCarryTerm_lt_threePow
    {O : OddOrbit} {start length : ℕ}
    (S : SpecialC3At O start length) :
    2 ^ S.difference.depth * S.upperCarryQuotient <
      3 ^ (length + 1) := by
  have hendpoint := S.endpoint_lt_two_mul_threePow
  have hupper := S.upperCarryQuotient_equation
  have hupper' :
      3 * O.value (start + length) + 1 =
        2 *
          (2 ^ S.difference.depth * S.upperCarryQuotient) := by
    rw [hupper, pow_succ]
    ring
  rw [pow_succ]
  nlinarith

/-- first shadow magnitudeは正。 -/
theorem firstShadowMagnitude_pos
    {O : OddOrbit} {start length : ℕ}
    (S : SpecialC3At O start length) :
    0 < S.firstShadowMagnitude := by
  unfold firstShadowMagnitude
  exact Nat.sub_pos_of_lt S.upperCarryTerm_lt_threePow

/-- first shadow magnitudeは奇数。 -/
theorem firstShadowMagnitude_odd
    {O : OddOrbit} {start length : ℕ}
    (S : SpecialC3At O start length) :
    Odd S.firstShadowMagnitude := by
  have odd_three_pow : ∀ n : ℕ, Odd (3 ^ n) := by
    intro n
    induction n with
    | zero =>
        exact ⟨0, by norm_num⟩
    | succ n ih =>
        rcases ih with ⟨a, ha⟩
        refine ⟨3 * a + 1, ?_⟩
        rw [pow_succ, ha]
        ring
  rcases odd_three_pow (length + 1) with ⟨a, ha⟩
  have hdepth : 0 < S.difference.depth := S.depth_pos
  obtain ⟨r, hr⟩ : ∃ r : ℕ, S.difference.depth = r + 1 :=
    ⟨S.difference.depth - 1, by omega⟩
  let b : ℕ := 2 ^ r * S.upperCarryQuotient
  have hterm :
      2 ^ S.difference.depth * S.upperCarryQuotient = 2 * b := by
    rw [hr, pow_succ]
    dsimp [b]
    ring
  have hlt := S.upperCarryTerm_lt_threePow
  rw [hterm, ha] at hlt
  have hba : b ≤ a := by
    omega
  refine ⟨a - b, ?_⟩
  unfold firstShadowMagnitude
  rw [hterm, ha]
  omega

/-- Special C3 predecessor shadowの最初のstepはexactに1ビットである。 -/
theorem firstShadowStep_equation
    {O : OddOrbit} {start length : ℕ}
    (S : SpecialC3At O start length) :
    2 * S.firstShadowMagnitude + 1 =
      3 * S.shadowMagnitude := by
  have hCurrent :
      O.value (start + length) + S.shadowMagnitude =
        2 * 3 ^ length := by
    unfold shadowMagnitude
    have hlt := S.endpoint_lt_two_mul_threePow
    omega
  have hNext :
      2 ^ S.difference.depth * S.upperCarryQuotient +
          S.firstShadowMagnitude =
        3 ^ (length + 1) := by
    unfold firstShadowMagnitude
    have hlt := S.upperCarryTerm_lt_threePow
    omega
  have hNext' :
      2 ^ S.difference.depth * S.upperCarryQuotient +
          S.firstShadowMagnitude =
        3 * 3 ^ length := by
    simpa [pow_succ, Nat.mul_comm] using hNext
  have hupper := S.upperCarryQuotient_equation
  have hupper' :
      3 * O.value (start + length) + 1 =
        2 *
          (2 ^ S.difference.depth *
            S.upperCarryQuotient) := by
    rw [hupper, pow_succ]
    ring
  omega

/-- Special C3から得られる最初のnegative shadow exact step。 -/
noncomputable def firstNegativeShadowStep
    {O : OddOrbit} {start length : ℕ}
    (S : SpecialC3At O start length) :
    NegativeShadowStepData (O.segmentWord start length) where
  currentMagnitude := S.shadowMagnitude
  current_pos := S.shadowMagnitude_pos
  currentShadow_eq := S.predecessorShadow_eq_neg_shadowMagnitude
  exponent := 1
  exponent_pos := by omega
  nextMagnitude := S.firstShadowMagnitude
  next_pos := S.firstShadowMagnitude_pos
  next_odd := S.firstShadowMagnitude_odd
  stepEquation := by
    simpa using S.firstShadowStep_equation

/-- Special C3から最初のcanonical re-anchoringを構成する。 -/
noncomputable def firstReanchoring
    {O : OddOrbit} {start length : ℕ}
    (S : SpecialC3At O start length) :
    ShadowReanchoringStepData
      (O.segmentWord start length) S.firstNegativeShadowStep := by
  have hrun := S.run
  rw [S.canonicalStart_eq, S.canonicalEnd_eq] at hrun
  exact reanchorNegativeShadowStep hrun S.firstNegativeShadowStep

end CollatzCore.SpecialC3At

namespace CollatzSecondLayer3

open CollatzSupport
open CollatzCore
open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

/--
第1層。future-minimumから選択長ごとのfirst-deferredまでの生成履歴を保存する。
-/
structure FutureMinimumSpecialC3TowerData (O : OddOrbit) where
  unbounded : O.Unbounded
  anchor : ℕ
  futureMinimum : O.FutureMinimumAt anchor
  select : ℕ → ℕ
  select_strict : StrictMono select
  normalization : ∀ j : ℕ,
    O.FiniteCaptureNormalizationData
      (futureMinimumWindowDifference
        O unbounded anchor (select j + 1)
        futureMinimum (by omega))
  special : ∀ j : ℕ,
    SpecialC3At O
      (anchor + (normalization j).terminalTime)
      (select j + 1)
  lengths_tend_to_infinity :
    ∀ M : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j → M < select j + 1
  growth :
    GenericSpecialC3GrowthProfile O
      (fun j => anchor + (normalization j).terminalTime)
      (fun j => select j + 1)

namespace FutureMinimumSpecialC3TowerData

/-- source-preserving towerのj番目の長さ。 -/
def length {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O) (j : ℕ) : ℕ :=
  R.select j + 1

/-- source-preserving towerのj番目のterminal time。 -/
def terminalTime {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O) (j : ℕ) : ℕ :=
  (R.normalization j).terminalTime

/-- source-preserving towerのj番目のterminal開始位置。 -/
def start {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O) (j : ℕ) : ℕ :=
  R.anchor + R.terminalTime j

/-- source-preserving towerのj番目のterminal word。 -/
def word {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O) (j : ℕ) : ExpWord :=
  O.segmentWord (R.start j) (R.length j)

/-- source-preserving towerのj番目のnegative predecessor center。 -/
def center {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O) (j : ℕ) : ℤ :=
  predecessorStart (R.word j)

/-- 各Special C3 seedの最初のcanonical re-anchoring。 -/
noncomputable def firstReanchoring {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O) (j : ℕ) :
    ShadowReanchoringStepData
      (R.word j) (R.special j).firstNegativeShadowStep := by
  simpa [word, start, length, terminalTime] using
    (R.special j).firstReanchoring

end FutureMinimumSpecialC3TowerData

/--
第2層。future-minimum依存型を忘れ、共通anchor、first-deferred履歴、
Special C3、growth profileを保存する。
-/
structure CoherentSpecialC3TowerData (O : OddOrbit) where
  anchor : ℕ
  sourceLength : ℕ → ℕ
  terminalTime : ℕ → ℕ
  before : ∀ j t : ℕ, t < terminalTime j →
    Nonempty
      (O.CapturedWindowAt
          (anchor + t) (sourceLength j) ⊕
       O.SynchronizedWindowAt
          (anchor + t) (sourceLength j))
  terminal : ∀ j : ℕ,
    O.DeferredWindowAt
      (anchor + terminalTime j) (sourceLength j)
  special : ∀ j : ℕ,
    SpecialC3At O
      (anchor + terminalTime j) (sourceLength j)
  lengths_tend_to_infinity :
    ∀ M : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j → M < sourceLength j
  growth :
    GenericSpecialC3GrowthProfile O
      (fun j => anchor + terminalTime j)
      sourceLength

namespace CoherentSpecialC3TowerData

/-- coherent towerのj番目の開始位置。 -/
def start {O : OddOrbit}
    (R : CoherentSpecialC3TowerData O) (j : ℕ) : ℕ :=
  R.anchor + R.terminalTime j

/-- coherent towerのj番目のword。 -/
def word {O : OddOrbit}
    (R : CoherentSpecialC3TowerData O) (j : ℕ) : ExpWord :=
  O.segmentWord (R.start j) (R.sourceLength j)

/-- coherent towerのnegative predecessor center。 -/
def center {O : OddOrbit}
    (R : CoherentSpecialC3TowerData O) (j : ℕ) : ℤ :=
  predecessorStart (R.word j)

/-- coherent towerの各seedに最初のre-anchoringを付加する。 -/
noncomputable def firstReanchoring {O : OddOrbit}
    (R : CoherentSpecialC3TowerData O) (j : ℕ) :
    ShadowReanchoringStepData
      (R.word j) (R.special j).firstNegativeShadowStep := by
  simpa [word, start] using (R.special j).firstReanchoring

/-- coherent towerから従来のgeneric towerへの忘却。 -/
noncomputable def toGeneric {O : OddOrbit}
    (R : CoherentSpecialC3TowerData O) :
    GenericSpecialC3TowerData O where
  start := fun j => R.start j
  length := R.sourceLength
  special := fun j => R.special j
  lengths_tend_to_infinity := R.lengths_tend_to_infinity
  growth := by
    simpa [start] using R.growth

end CoherentSpecialC3TowerData

namespace FutureMinimumSpecialC3TowerData

/-- 第1層から第2層への履歴縮約。 -/
noncomputable def toCoherent {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O) :
    CoherentSpecialC3TowerData O where
  anchor := R.anchor
  sourceLength := fun j => R.length j
  terminalTime := fun j => R.terminalTime j
  before := by
    intro j t ht
    exact (R.normalization j).before t ht
  terminal := fun j => (R.normalization j).terminal
  special := fun j => by
    simpa [start, length, terminalTime] using R.special j
  lengths_tend_to_infinity := by
    simpa [length] using R.lengths_tend_to_infinity
  growth := by
    simpa [start, length, terminalTime] using R.growth

/-- 第1層からgeneric towerへの合成忘却。 -/
noncomputable def toGeneric {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O) :
    GenericSpecialC3TowerData O :=
  R.toCoherent.toGeneric

end FutureMinimumSpecialC3TowerData

/--
一つのfuture-minimumから、生成履歴付きSpecial C3 towerまたは
生成履歴付きdeep lower-replay towerを抽出する。
-/
theorem futureMinimum_source_preserving_obstruction_dichotomy
    (O : OddOrbit)
    (hU : O.Unbounded)
    (anchor : ℕ)
    (hmin : O.FutureMinimumAt anchor) :
    Nonempty (FutureMinimumSpecialC3TowerData O) ∨
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
      let select : ℕ → ℕ :=
        fun j => select₁ (select₂ j)
      let N : ∀ j : ℕ,
          O.FiniteCaptureNormalizationData
            (futureMinimumWindowDifference
              O hU anchor (select j + 1) hmin (by omega)) :=
        fun j =>
          futureMinimumFirstDeferredData
            O hU anchor (select j + 1) hmin (by omega)
      left
      refine ⟨{
        unbounded := hU
        anchor := anchor
        futureMinimum := hmin
        select := select
        select_strict := ?_
        normalization := N
        special := ?_
        lengths_tend_to_infinity := ?_
        growth := .polynomial K A ?_
      }⟩
      · exact
          (Cofinally.select_strict IsSpecial hSpecial).comp
            (Cofinally.select_strict (Bound K A) hBound)
      · intro j
        have hs :=
          Classical.choice
            (hselect₁Special (select₂ j))
        simpa [select, N, futureMinimumTerminalStart] using hs
      · intro M
        refine ⟨M, ?_⟩
        intro j hj
        have h₂ : j ≤ select₂ j :=
          Cofinally.select_ge (Bound K A) hBound j
        have h₁ : select₂ j ≤ select₁ (select₂ j) :=
          Cofinally.select_ge IsSpecial hSpecial (select₂ j)
        dsimp [select]
        omega
      · intro j
        change Bound K A (select₂ j)
        exact
          Cofinally.select_spec
            (Bound K A)
            hBound
            j
    · let select : ℕ → ℕ := select₁
      let N : ∀ j : ℕ,
          O.FiniteCaptureNormalizationData
            (futureMinimumWindowDifference
              O hU anchor (select j + 1) hmin (by omega)) :=
        fun j =>
          futureMinimumFirstDeferredData
            O hU anchor (select j + 1) hmin (by omega)
      left
      refine ⟨{
        unbounded := hU
        anchor := anchor
        futureMinimum := hmin
        select := select
        select_strict :=
          Cofinally.select_strict IsSpecial hSpecial
        normalization := N
        special := ?_
        lengths_tend_to_infinity := ?_
        growth := .superPolynomial ?_
      }⟩
      · intro j
        have hs :=
          Classical.choice (hselect₁Special j)
        simpa [select, N, futureMinimumTerminalStart] using hs
      · intro M
        refine ⟨M, ?_⟩
        intro j hj
        have hs : j ≤ select₁ j :=
          Cofinally.select_ge IsSpecial hSpecial j
        dsimp [select]
        omega
      · intro K A
        have hnot : ¬ Cofinally (Bound K A) := by
          intro h
          exact hPolynomial ⟨K, A, h⟩
        obtain ⟨J, hJ⟩ :=
          Cofinally.eventually_not_of_not
            (Bound K A)
            hnot
        refine ⟨J, ?_⟩
        intro j hj
        have hn := hJ j hj
        dsimp [Bound, select, N] at hn ⊢
        simp only [futureMinimumTerminalStart] at hn ⊢
        omega
  · obtain ⟨N₀, hN₀⟩ :=
      Cofinally.eventually_not_of_not
        IsSpecial
        hSpecial
    right
    refine ⟨{
      unbounded := hU
      anchor := anchor
      futureMinimum := hmin
      cutoff := N₀
      normalization := fun j =>
        futureMinimumFirstDeferredData
          O hU anchor (futureTailLength N₀ j) hmin
          (futureTailLength_pos N₀ j)
      quotient_pos := ?_
    }⟩
    intro j
    let F :=
      futureMinimumFirstDeferredData
        O hU anchor (futureTailLength N₀ j) hmin
        (futureTailLength_pos N₀ j)
    apply
      finiteNormalizationReplayQuotient_pos_of_not_special
        F
        (futureTailLength_pos N₀ j)
    have hn := hN₀ (N₀ + j) (by omega)
    simpa [
      IsSpecial,
      futureTailLength,
      futureMinimumTerminalStart,
      F,
      Nat.add_assoc
    ] using hn

/-- source-preserving二分岐をcoherent二分岐へ縮約する。 -/
theorem futureMinimum_coherent_source_obstruction_dichotomy
    (O : OddOrbit)
    (hU : O.Unbounded)
    (anchor : ℕ)
    (hmin : O.FutureMinimumAt anchor) :
    Nonempty (CoherentSpecialC3TowerData O) ∨
      Nonempty (CoherentDeepLowerReplayTowerData O) := by
  rcases
      futureMinimum_source_preserving_obstruction_dichotomy
        O hU anchor hmin with
    hSpecial | hDeep
  · rcases hSpecial with ⟨S⟩
    exact Or.inl ⟨S.toCoherent⟩
  · rcases hDeep with ⟨D⟩
    exact Or.inr ⟨D.toCoherent⟩

/-- source-preserving層を経由して従来のgeneric二分岐へ忘却する。 -/
theorem futureMinimum_generic_obstruction_dichotomy_via_full_history
    (O : OddOrbit)
    (hU : O.Unbounded)
    (anchor : ℕ)
    (hmin : O.FutureMinimumAt anchor) :
    Nonempty (GenericSpecialC3TowerData O) ∨
      Nonempty (GenericDeepLowerReplayTowerData O) := by
  rcases
      futureMinimum_source_preserving_obstruction_dichotomy
        O hU anchor hmin with
    hSpecial | hDeep
  · rcases hSpecial with ⟨S⟩
    exact Or.inl ⟨S.toGeneric⟩
  · rcases hDeep with ⟨D⟩
    exact Or.inr ⟨D.toGeneric⟩

end CollatzSecondLayer3
