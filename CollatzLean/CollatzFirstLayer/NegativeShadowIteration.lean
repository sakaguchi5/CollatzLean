import CollatzLean.CollatzFirstLayer.ShadowReanchoring
import CollatzLean.CollatzFirstLayer.FirstCarry

import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Ring

/-!
# negative shadow re-anchoringの自動反復

正の自然数を2冪と奇数部分へ完全分解し、正の奇数shadow magnitude `s`から

`3 * s - 1 = 2^e * s'`

を満たす次の指数と奇数magnitudeを自動構成する。
既存の一段re-anchoringへ接続し、任意有限深さで取り出せる無限towerを構成する。
-/

namespace CollatzFirstLayer

/-- 正の自然数は2冪と奇数部分へ完全分解できる。 -/
theorem exactTwoFactor_exists_of_pos :
    ∀ n : ℕ, 0 < n →
      ∃ d u : ℕ, ExactTwoFactor n d u := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn
      rcases Nat.even_or_odd n with hEven | hOdd
      · rcases hEven with ⟨m, hm⟩
        have hmPos : 0 < m := by omega
        have hmLt : m < n := by omega
        obtain ⟨d, u, hFactor⟩ := ih m hmLt hmPos
        rcases hFactor with ⟨hEq, hOddU⟩
        refine ⟨d + 1, u, ?_, hOddU⟩
        calc
          n = m + m := hm
          _ = 2 * m := by ring
          _ = 2 * (2 ^ d * u) := by rw [hEq]
          _ = 2 ^ (d + 1) * u := by
            rw [pow_succ]
            ring
      · refine ⟨0, n, ?_, hOdd⟩
        simp

/-- 正の自然数の選択された完全2進分解。 -/
structure PositiveExactTwoFactorData (n : ℕ) where
  exponent : ℕ
  oddPart : ℕ
  factorization : ExactTwoFactor n exponent oddPart

/-- 正の自然数には完全2進分解データが存在する。 -/
theorem nonempty_positiveExactTwoFactorData
    (n : ℕ) (hn : 0 < n) :
    Nonempty (PositiveExactTwoFactorData n) := by
  obtain ⟨d, u, hFactor⟩ :=
    exactTwoFactor_exists_of_pos n hn
  exact ⟨⟨d, u, hFactor⟩⟩

/-- 正の自然数の完全2進分解を一つ選ぶ。 -/
noncomputable def positiveExactTwoFactorData
    (n : ℕ) (hn : 0 < n) :
    PositiveExactTwoFactorData n :=
  Classical.choice (nonempty_positiveExactTwoFactorData n hn)

namespace ExpWord

/-- 奇数magnitudeに対する`3 * s - 1`は偶数。 -/
private theorem three_mul_sub_one_even
    {s : ℕ} (hsOdd : Odd s) :
    Even (3 * s - 1) := by
  rcases hsOdd with ⟨k, hk⟩
  refine ⟨3 * k + 1, ?_⟩
  omega

/--
正の奇数negative shadowから、次のexact shadow stepを自動構成する。
-/
noncomputable def automaticNegativeShadowStep
    {w : ExpWord} {s : ℕ}
    (hsPos : 0 < s)
    (hsOdd : Odd s)
    (hShadow : predecessorShadow w = -(s : ℤ)) :
    NegativeShadowStepData w := by
  let F : PositiveExactTwoFactorData (3 * s - 1) :=
    positiveExactTwoFactorData (3 * s - 1) (by omega)
  have hEven : Even (3 * s - 1) :=
    three_mul_sub_one_even hsOdd
  have hExponentPos : 0 < F.exponent := by
    by_contra hnot
    have hzero : F.exponent = 0 := by omega
    have hOddWhole : Odd (3 * s - 1) := by
      have hEq := F.factorization.1
      have hOddPart := F.factorization.2
      rw [hzero] at hEq
      simp at hEq
      simp only [hEq]
      exact hOddPart
    exact odd_even_false_nat hOddWhole hEven
  refine
    { currentMagnitude := s
      current_pos := hsPos
      currentShadow_eq := hShadow
      exponent := F.exponent
      exponent_pos := hExponentPos
      nextMagnitude := F.oddPart
      next_pos := ?_
      next_odd := F.factorization.2
      stepEquation := ?_ }
  · rcases F.factorization.2 with ⟨k, hk⟩
    rw [hk]
    omega
  · have hEq := F.factorization.1
    omega

/--
反復re-anchoringの一時点。

`rootCenter`は全反復で保存され、`word`はcanonical actual runを持ち、
`predecessorShadow word`は負の`magnitude`である。
-/
structure NegativeShadowReanchoringState where
  rootCenter : ℤ
  word : ExpWord
  magnitude : ℕ
  magnitude_pos : 0 < magnitude
  magnitude_odd : Odd magnitude
  run : Runs word (canonicalStart word) (canonicalEnd word)
  center_eq : predecessorStart word = rootCenter
  shadow_eq : predecessorShadow word = -(magnitude : ℤ)

namespace NegativeShadowReanchoringState

/-- 現状態から自動生成される次のnegative shadow step。 -/
noncomputable def stepData
    (S : NegativeShadowReanchoringState) :
    NegativeShadowStepData S.word :=
  automaticNegativeShadowStep
    S.magnitude_pos S.magnitude_odd S.shadow_eq

/-- 一段canonical re-anchoringした次状態。 -/
noncomputable def next
    (S : NegativeShadowReanchoringState) :
    NegativeShadowReanchoringState := by
  let A := S.stepData
  let E := reanchorNegativeShadowStep S.run A
  have hRun :
      Runs
        (S.word ++ [A.exponent])
        (canonicalStart (S.word ++ [A.exponent]))
        (canonicalEnd (S.word ++ [A.exponent])) := by
    have h := E.runs
    rw [E.start_eq_canonical, E.finish_eq_canonical] at h
    exact h
  exact
    { rootCenter := S.rootCenter
      word := S.word ++ [A.exponent]
      magnitude := A.nextMagnitude
      magnitude_pos := A.next_pos
      magnitude_odd := A.next_odd
      run := hRun
      center_eq := E.predecessorStart_eq.trans S.center_eq
      shadow_eq := E.predecessorShadow_eq }

@[simp] theorem next_rootCenter
    (S : NegativeShadowReanchoringState) :
    S.next.rootCenter = S.rootCenter := by
  rfl

@[simp] theorem next_word
    (S : NegativeShadowReanchoringState) :
    S.next.word = S.word ++ [S.stepData.exponent] := by
  rfl

@[simp] theorem next_magnitude
    (S : NegativeShadowReanchoringState) :
    S.next.magnitude = S.stepData.nextMagnitude := by
  rfl

/-- 状態を自然数回反復する。 -/
noncomputable def iterate
    (S : NegativeShadowReanchoringState) :
    ℕ → NegativeShadowReanchoringState
  | 0 => S
  | n + 1 => (iterate S n).next

@[simp] theorem iterate_zero
    (S : NegativeShadowReanchoringState) :
    S.iterate 0 = S := by
  rfl

@[simp] theorem iterate_succ
    (S : NegativeShadowReanchoringState) (n : ℕ) :
    S.iterate (n + 1) = (S.iterate n).next := by
  rfl

/-- root centerは全反復で保存される。 -/
theorem iterate_rootCenter
    (S : NegativeShadowReanchoringState) (n : ℕ) :
    (S.iterate n).rootCenter = S.rootCenter := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [iterate_succ, next_rootCenter, ih]

end NegativeShadowReanchoringState

/--
一つのsource wordから始まる無限negative shadow re-anchoring tower。
-/
structure NegativeShadowReanchoringTowerData
    (sourceWord : ExpWord) where
  seed : NegativeShadowReanchoringState
  seed_word : seed.word = sourceWord
  seed_center : seed.rootCenter = predecessorStart sourceWord

namespace NegativeShadowReanchoringTowerData

/-- canonical wordと負の奇数shadowからtowerを構成する。 -/
def ofCanonicalNegativeShadow
    {w : ExpWord} {s : ℕ}
    (hRun : Runs w (canonicalStart w) (canonicalEnd w))
    (hsPos : 0 < s)
    (hsOdd : Odd s)
    (hShadow : predecessorShadow w = -(s : ℤ)) :
    NegativeShadowReanchoringTowerData w where
  seed :=
    { rootCenter := predecessorStart w
      word := w
      magnitude := s
      magnitude_pos := hsPos
      magnitude_odd := hsOdd
      run := hRun
      center_eq := rfl
      shadow_eq := hShadow }
  seed_word := rfl
  seed_center := rfl

/-- towerのn段目の状態。 -/
noncomputable def state
    {w : ExpWord}
    (T : NegativeShadowReanchoringTowerData w)
    (n : ℕ) : NegativeShadowReanchoringState :=
  T.seed.iterate n

/-- towerのn段目のword。 -/
noncomputable def word
    {w : ExpWord}
    (T : NegativeShadowReanchoringTowerData w)
    (n : ℕ) : ExpWord :=
  (T.state n).word

/-- towerのn段目のshadow magnitude。 -/
noncomputable def magnitude
    {w : ExpWord}
    (T : NegativeShadowReanchoringTowerData w)
    (n : ℕ) : ℕ :=
  (T.state n).magnitude

/-- towerのn段目から次へ進むshadow exponent。 -/
noncomputable def exponent
    {w : ExpWord}
    (T : NegativeShadowReanchoringTowerData w)
    (n : ℕ) : ℕ :=
  (T.state n).stepData.exponent

/-- source wordへappendされる最初のn個のshadow exponent word。 -/
noncomputable def extensionWord
    {w : ExpWord}
    (T : NegativeShadowReanchoringTowerData w) :
    ℕ → ExpWord
  | 0 => []
  | n + 1 => T.extensionWord n ++ [T.exponent n]

@[simp] theorem word_zero
    {w : ExpWord}
    (T : NegativeShadowReanchoringTowerData w) :
    T.word 0 = w := by
  change T.seed.word = w
  exact T.seed_word

@[simp] theorem word_succ
    {w : ExpWord}
    (T : NegativeShadowReanchoringTowerData w)
    (n : ℕ) :
    T.word (n + 1) = T.word n ++ [T.exponent n] := by
  rfl

/-- 最初のn個のshadow exponent wordの長さはn。 -/
theorem extensionWord_length
    {w : ExpWord}
    (T : NegativeShadowReanchoringTowerData w) :
    ∀ n : ℕ, (T.extensionWord n).length = n := by
  intro n
  induction n with
  | zero => simp [extensionWord]
  | succ n ih =>
      simp [extensionWord, ih]

/-- n段目から次へ進むshadow exponentは正。 -/
theorem exponent_pos
    {w : ExpWord}
    (T : NegativeShadowReanchoringTowerData w)
    (n : ℕ) :
    0 < T.exponent n :=
  (T.state n).stepData.exponent_pos

/-- n段目のwordはsource wordへ有限shadow exponent wordをappendしたもの。 -/
theorem word_eq_source_append_extensionWord
    {w : ExpWord}
    (T : NegativeShadowReanchoringTowerData w) :
    ∀ n : ℕ,
      T.word n = w ++ T.extensionWord n := by
  intro n
  induction n with
  | zero =>
      simp [extensionWord]
  | succ n ih =>
      rw [word_succ, ih]
      simp [extensionWord, List.append_assoc]

/-- n段目のword長はsource word長にnを加えたもの。 -/
theorem word_length
    {w : ExpWord}
    (T : NegativeShadowReanchoringTowerData w)
    (n : ℕ) :
    (T.word n).length = w.length + n := by
  rw [T.word_eq_source_append_extensionWord n, List.length_append]
  rw [T.extensionWord_length n]

/-- 全段のpredecessor startはsource centerに一致する。 -/
theorem predecessorStart_word_eq_source
    {w : ExpWord}
    (T : NegativeShadowReanchoringTowerData w)
    (n : ℕ) :
    predecessorStart (T.word n) = predecessorStart w := by
  calc
    predecessorStart (T.word n)
        = (T.state n).rootCenter := (T.state n).center_eq
    _ = T.seed.rootCenter := by
      exact NegativeShadowReanchoringState.iterate_rootCenter T.seed n
    _ = predecessorStart w := T.seed_center

/-- 全段のpredecessor shadowは負のmagnitude。 -/
theorem predecessorShadow_word_eq
    {w : ExpWord}
    (T : NegativeShadowReanchoringTowerData w)
    (n : ℕ) :
    predecessorShadow (T.word n) = -(T.magnitude n : ℤ) :=
  (T.state n).shadow_eq

/-- towerのmagnitudeは常に正。 -/
theorem magnitude_pos
    {w : ExpWord}
    (T : NegativeShadowReanchoringTowerData w)
    (n : ℕ) :
    0 < T.magnitude n :=
  (T.state n).magnitude_pos

/-- towerのmagnitudeは常に奇数。 -/
theorem magnitude_odd
    {w : ExpWord}
    (T : NegativeShadowReanchoringTowerData w)
    (n : ℕ) :
    Odd (T.magnitude n) :=
  (T.state n).magnitude_odd


/-- 各段のshadow step equation。 -/
theorem stepEquation
    {w : ExpWord}
    (T : NegativeShadowReanchoringTowerData w)
    (n : ℕ) :
    2 ^ T.exponent n * T.magnitude (n + 1) + 1 =
      3 * T.magnitude n := by
  have hnext :
      T.magnitude (n + 1) =
        (T.state n).stepData.nextMagnitude := by
    change
      ((T.state n).next).magnitude =
        (T.state n).stepData.nextMagnitude
    rfl
  have hcurrent :
      T.magnitude n =
        (T.state n).stepData.currentMagnitude := by
    change
      (T.state n).magnitude =
        (T.state n).stepData.currentMagnitude
    unfold NegativeShadowReanchoringState.stepData
    unfold automaticNegativeShadowStep
    rfl
  rw [hnext, hcurrent]
  simpa [exponent] using
    (T.state n).stepData.stepEquation

end NegativeShadowReanchoringTowerData

end ExpWord
end CollatzFirstLayer
