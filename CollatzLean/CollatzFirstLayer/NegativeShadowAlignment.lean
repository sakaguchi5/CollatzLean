import CollatzLean.CollatzFirstLayer.NegativeShadowIteration

/-!
# negative shadow magnitudeの2進alignment伝播

negative shadow dynamics

`2^e * s' + 1 = 3 * s`

に対し、二つのmagnitudeが深さ`m`まで2進的に一致し、
一方の次指数`e`が`m`未満なら、他方の次指数もexactに`e`となる。
さらに次magnitudeは深さ`m-e`まで一致する。

これを反復し、初期magnitude alignmentから有限shadow exponent prefix一致を得る。
-/

namespace CollatzFirstLayer
namespace ExpWord

/--
`b`が`a`より上側にあり、差が`2^m`の倍数であること。
方向付きにすることで自然数差分だけで反復できる。
-/
def OrderedMagnitudeAlignedToDepth (a b m : ℕ) : Prop :=
  ∃ k : ℕ, b = a + 2 ^ m * k

/-- 自身とは任意深さで方向付きalignmentを持つ。 -/
theorem orderedMagnitudeAlignedToDepth_refl
    (a m : ℕ) :
    OrderedMagnitudeAlignedToDepth a a m := by
  exact ⟨0, by simp only [mul_zero, add_zero]⟩

/-- 深い方向付きalignmentは浅いalignmentを含む。 -/
theorem orderedMagnitudeAlignedToDepth_mono
    {a b m n : ℕ}
    (hmn : m ≤ n)
    (h : OrderedMagnitudeAlignedToDepth a b n) :
    OrderedMagnitudeAlignedToDepth a b m := by
  rcases h with ⟨k, hk⟩
  refine ⟨2 ^ (n - m) * k, ?_⟩
  have hn : n = m + (n - m) := by omega
  rw [hn, pow_add] at hk
  calc
    b = a + (2 ^ m * 2 ^ (n - m)) * k := hk
    _ = a + 2 ^ m * (2 ^ (n - m) * k) := by ring

/--
一段のnegative shadow dynamicsにおけるalignment伝播。

二つのstep equationがあり、`b-a`が`2^m`の倍数で、
最初の指数`e₁`が`m`未満なら、二つの指数は一致する。
次magnitudeの差は`2^(m-e₁)`の倍数となる。
-/
theorem oddShadowStep_ordered_alignment
    {a b a' b' e₁ e₂ m : ℕ}
    (haOdd : Odd a')
    (hbOdd : Odd b')
    (hA : 2 ^ e₁ * a' + 1 = 3 * a)
    (hB : 2 ^ e₂ * b' + 1 = 3 * b)
    (hAlign : OrderedMagnitudeAlignedToDepth a b m)
    (he : e₁ < m) :
    e₁ = e₂ ∧
      OrderedMagnitudeAlignedToDepth a' b' (m - e₁) := by
  rcases hAlign with ⟨k, hk⟩
  let r : ℕ := m - e₁
  have hrPos : 0 < r := by
    dsimp [r]
    omega
  have hm : m = e₁ + r := by
    dsimp [r]
    omega
  let candidate : ℕ := a' + 3 * 2 ^ r * k
  have hCandidateOdd : Odd candidate := by
    rcases haOdd with ⟨u, hu⟩
    obtain ⟨r₀, hr₀⟩ : ∃ r₀ : ℕ, r = r₀ + 1 :=
      ⟨r - 1, by omega⟩
    refine ⟨u + 3 * 2 ^ r₀ * k, ?_⟩
    dsimp [candidate]
    rw [hu, hr₀, pow_succ]
    ring
  have hCandidatePlus :
      2 ^ e₁ * candidate + 1 = 3 * b := by
    dsimp [candidate]
    rw [hk, hm, pow_add]
    calc
      2 ^ e₁ * (a' + 3 * 2 ^ r * k) + 1
          = (2 ^ e₁ * a' + 1) +
              3 * (2 ^ e₁ * 2 ^ r) * k := by ring
      _ = 3 * a + 3 * (2 ^ e₁ * 2 ^ r) * k := by rw [hA]
      _ = 3 * (a + (2 ^ e₁ * 2 ^ r) * k) := by ring
  have hCandidateFactor :
      ExactTwoFactor (3 * b - 1) e₁ candidate := by
    refine ⟨?_, hCandidateOdd⟩
    omega
  have hActualFactor :
      ExactTwoFactor (3 * b - 1) e₂ b' := by
    refine ⟨?_, hbOdd⟩
    omega
  have hUnique :=
    exactTwoFactor_unique hCandidateFactor hActualFactor
  have hExponent : e₁ = e₂ := hUnique.1
  have hPart : candidate = b' := hUnique.2
  refine ⟨hExponent, ?_⟩
  refine ⟨3 * k, ?_⟩
  rw [← hPart]
  dsimp [candidate, r]
  ring

namespace NegativeShadowReanchoringTowerData

/--
二つのre-anchoring towerの現在magnitudeが深さ`m`まで方向付きalignmentを持ち、
一方の次指数が`m`未満なら、次指数が一致しalignmentが残余深さへ伝播する。
-/
theorem step_ordered_alignment
    {w₁ w₂ : ExpWord}
    (T : NegativeShadowReanchoringTowerData w₁)
    (U : NegativeShadowReanchoringTowerData w₂)
    (n m : ℕ)
    (hAlign :
      OrderedMagnitudeAlignedToDepth
        (T.magnitude n) (U.magnitude n) m)
    (he : T.exponent n < m) :
    T.exponent n = U.exponent n ∧
      OrderedMagnitudeAlignedToDepth
        (T.magnitude (n + 1))
        (U.magnitude (n + 1))
        (m - T.exponent n) := by
  exact
    oddShadowStep_ordered_alignment
      (T.magnitude_odd (n + 1))
      (U.magnitude_odd (n + 1))
      (T.stepEquation n)
      (U.stepEquation n)
      hAlign
      he

/-- shadow extension wordが消費した総2進depth。 -/
noncomputable def extensionTwoSteps
    {w : ExpWord}
    (T : NegativeShadowReanchoringTowerData w)
    (n : ℕ) : ℕ :=
  twoSteps (T.extensionWord n)

@[simp] theorem extensionTwoSteps_zero
    {w : ExpWord}
    (T : NegativeShadowReanchoringTowerData w) :
    T.extensionTwoSteps 0 = 0 := by
  simp [extensionTwoSteps, extensionWord, twoSteps]

/-- extension depthの一段加算式。 -/
theorem extensionTwoSteps_succ
    {w : ExpWord}
    (T : NegativeShadowReanchoringTowerData w)
    (n : ℕ) :
    T.extensionTwoSteps (n + 1) =
      T.extensionTwoSteps n + T.exponent n := by
  unfold extensionTwoSteps
  rw [extensionWord]
  rw [twoSteps_append]
  simp [twoSteps]


/-- extension depthは反復深さに対して単調非減少。 -/
theorem extensionTwoSteps_mono
    {w : ExpWord}
    (T : NegativeShadowReanchoringTowerData w) :
    Monotone T.extensionTwoSteps := by
  intro a b hab
  obtain ⟨d, hd⟩ : ∃ d : ℕ, b = a + d :=
    ⟨b - a, by omega⟩
  subst b
  induction d with
  | zero => simp
  | succ d ih =>
      have hstep := T.extensionTwoSteps_succ (a + d)
      have hindex : a + (d + 1) = (a + d) + 1 := by omega
      rw [hindex, hstep]
      omega

/--
初期magnitudeが深さ`M`までalignedなら、T側の累積shadow depthが`M`未満の間、
二つのshadow exponent prefixはexactに一致する。
同時に現在magnitudeの残余alignmentも保存する。
-/
theorem extensionWord_eq_and_residualAlignment
    {w₁ w₂ : ExpWord}
    (T : NegativeShadowReanchoringTowerData w₁)
    (U : NegativeShadowReanchoringTowerData w₂)
    (M : ℕ)
    (hInitial :
      OrderedMagnitudeAlignedToDepth
        (T.magnitude 0) (U.magnitude 0) M) :
    ∀ n : ℕ,
      T.extensionTwoSteps n < M →
        T.extensionWord n = U.extensionWord n ∧
          OrderedMagnitudeAlignedToDepth
            (T.magnitude n)
            (U.magnitude n)
            (M - T.extensionTwoSteps n) := by
  intro n
  induction n with
| zero =>
    intro _
    constructor
    · simp [extensionWord]
    · simpa [extensionTwoSteps, extensionWord, twoSteps] using hInitial
  | succ n ih =>
      intro hDepth
      have hStepDepth := T.extensionTwoSteps_succ n
      have hPrefixDepth : T.extensionTwoSteps n < M := by
        omega
      obtain ⟨hWord, hAlign⟩ := ih hPrefixDepth
      have hExponentLt :
          T.exponent n < M - T.extensionTwoSteps n := by
        omega
      obtain ⟨hExponent, hNextAlign⟩ :=
        T.step_ordered_alignment U n
          (M - T.extensionTwoSteps n)
          hAlign hExponentLt
      constructor
      · simp only [extensionWord]
        rw [hWord, hExponent]
      · have hResidual :
            (M - T.extensionTwoSteps n) - T.exponent n =
              M - T.extensionTwoSteps (n + 1) := by
          rw [hStepDepth]
          omega
        simpa [hResidual] using hNextAlign

/-- 初期alignmentとdepth余裕から有限shadow exponent word一致を得る。 -/
theorem extensionWord_eq_of_ordered_alignment
    {w₁ w₂ : ExpWord}
    (T : NegativeShadowReanchoringTowerData w₁)
    (U : NegativeShadowReanchoringTowerData w₂)
    (M n : ℕ)
    (hInitial :
      OrderedMagnitudeAlignedToDepth
        (T.magnitude 0) (U.magnitude 0) M)
    (hDepth : T.extensionTwoSteps n < M) :
    T.extensionWord n = U.extensionWord n :=
  (T.extensionWord_eq_and_residualAlignment U M hInitial n hDepth).1


/--
初期alignmentがあり、`n+1`段までの累積depthが`M`未満なら、
n番目の次shadow指数は二towerで一致する。
-/
theorem exponent_eq_of_ordered_alignment
    {w₁ w₂ : ExpWord}
    (T : NegativeShadowReanchoringTowerData w₁)
    (U : NegativeShadowReanchoringTowerData w₂)
    (M n : ℕ)
    (hInitial :
      OrderedMagnitudeAlignedToDepth
        (T.magnitude 0) (U.magnitude 0) M)
    (hDepth : T.extensionTwoSteps (n + 1) < M) :
    T.exponent n = U.exponent n := by
  have hStepDepth := T.extensionTwoSteps_succ n
  have hPrefixDepth : T.extensionTwoSteps n < M := by
    omega
  have hData :=
    T.extensionWord_eq_and_residualAlignment U M hInitial n hPrefixDepth
  have hExponentLt :
      T.exponent n < M - T.extensionTwoSteps n := by
    omega
  exact
    (T.step_ordered_alignment U n
      (M - T.extensionTwoSteps n)
      hData.2 hExponentLt).1


end NegativeShadowReanchoringTowerData
end ExpWord
end CollatzFirstLayer
