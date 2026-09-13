import CollatzLean.Collatz3.Bridge.CriticalUnionTail
import CollatzLean.Collatz3.Bridge.CriticalInfiniteDensityExact
import CollatzLean.Collatz3.Bridge.CriticalFixedWidthDensity
import CollatzLean.Collatz3.Bridge.FullFirstCrossingDensity

import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Collatz3 Bridge: 全幅 actual critical-start union の exact natural density

前段までで次が得られている。

* fixed width `m` の minimal critical starts の density は `N_m / M_m`。
* fixed width `m` の full first-crossing starts の density は `N_m / 2^H_m`。
* それぞれの全 width density mass の無限和は exact に `1/4`, `1/2`。
* width `m > L` の actual start は depth `H_L` の survivor residue union に含まれる。
* survivor residue union は modulo `2^H_L` の exactly `S_(H_L)` 本の合同類であり、
  `S_n / 2^n -> 0`。

ここでは無限和と cutoff limit を直接交換しない。

widths `1,...,L` の有限 union を下側近似とし、残りの high-width tail を
survivor residue union で上から覆う。固定 `L` で `X -> ∞` を取り、その後
`L -> ∞` を取る二段階 squeeze により、全幅 union 自身の自然密度を exact に求める。

結論は

* `density {x | IsAnyActualCriticalStart x} = 1/4`
* `density {x | IsAnyFullActualCriticalStart x} = 1/2`

である。

これは coefficient first-crossing start の密度定理であり、Collatz 軌道の actual value が
必ず初期値以下へ降下することや、1へ収束することを主張しない。
-/

namespace Collatz3
namespace Bridge

open Filter Topology
open scoped BigOperators

/-! ## survivor residue union の arbitrary-cutoff density -/

/-- cutoff inclusion。 -/
def survivorResidueStartBelowMap
    {n : ℕ}
    {hn : 0 < n}
    {B C : ℕ}
    (hBC : B ≤ C) :
    SurvivorResidueStartBelow n hn B →
      SurvivorResidueStartBelow n hn C :=
  fun x => ⟨x.1, lt_of_lt_of_le x.2.1 hBC, x.2.2⟩

/-- cutoff inclusion は単射。 -/
theorem survivorResidueStartBelowMap_injective
    {n : ℕ}
    {hn : 0 < n}
    {B C : ℕ}
    (hBC : B ≤ C) :
    Function.Injective
      (survivorResidueStartBelowMap (n := n) (hn := hn) hBC) := by
  intro a b h
  apply Subtype.ext
  simpa [survivorResidueStartBelowMap] using
    congrArg
      (fun x : SurvivorResidueStartBelow n hn C => x.1) h

/-- survivor residue count は cutoff に関して単調。 -/
theorem survivorResidueStartCount_mono
    {n : ℕ}
    {hn : 0 < n}
    {B C : ℕ}
    (hBC : B ≤ C) :
    survivorResidueStartCount n hn B ≤
      survivorResidueStartCount n hn C := by
  let : Finite (SurvivorResidueStartBelow n hn C) :=
    survivorResidueStartBelow_finite n hn C
  exact
    Nat.card_le_card_of_injective
      (survivorResidueStartBelowMap (n := n) (hn := hn) hBC)
      (survivorResidueStartBelowMap_injective
        (n := n) (hn := hn) hBC)

/-- floor `2^n` block は cutoff 以下。 -/
theorem twoPow_mul_div_le
    (n X : ℕ) :
    2 ^ n * (X / 2 ^ n) ≤ X := by
  have h := Nat.mod_add_div X (2 ^ n)
  omega

/-- cutoff は次の `2^n` block より小さい。 -/
theorem lt_twoPow_mul_div_add_one
    (n X : ℕ) :
    X < 2 ^ n * (X / 2 ^ n + 1) := by
  let M := 2 ^ n
  have hM : 0 < M := Arithmetic.twoPow_pos n
  have hmod : X % M < M := Nat.mod_lt X hM
  have hdiv : X % M + M * (X / M) = X := Nat.mod_add_div X M
  calc
    X = X % M + M * (X / M) := hdiv.symm
    _ < M + M * (X / M) := Nat.add_lt_add_right hmod _
    _ = M * (X / M + 1) := by ring

/-- arbitrary cutoff survivor count の block sandwich。 -/
theorem survivorResidueStartCount_sandwich
    {n X : ℕ}
    (hn : 0 < n) :
    survivorParityCount n * (X / 2 ^ n) ≤
        survivorResidueStartCount n hn X ∧
      survivorResidueStartCount n hn X ≤
        survivorParityCount n * (X / 2 ^ n + 1) := by
  let q := X / 2 ^ n
  constructor
  · calc
      survivorParityCount n * q
          = survivorResidueStartCount n hn (2 ^ n * q) :=
            (survivorResidueStartCount_block_eq hn q).symm
      _ ≤ survivorResidueStartCount n hn X :=
        survivorResidueStartCount_mono
          (n := n) (hn := hn)
          (twoPow_mul_div_le n X)
  · calc
      survivorResidueStartCount n hn X
          ≤ survivorResidueStartCount n hn (2 ^ n * (q + 1)) :=
        survivorResidueStartCount_mono
          (n := n) (hn := hn)
          (le_of_lt (lt_twoPow_mul_div_add_one n X))
      _ = survivorParityCount n * (q + 1) :=
        survivorResidueStartCount_block_eq hn (q + 1)

/-- survivor residue count の cross-multiplied discrepancy。 -/
theorem survivorResidueStartCount_cross_discrepancy
    {n X : ℕ}
    (hn : 0 < n) :
    2 ^ n * survivorResidueStartCount n hn X ≤
        survivorParityCount n * X +
          2 ^ n * survivorParityCount n ∧
      survivorParityCount n * X ≤
        2 ^ n * survivorResidueStartCount n hn X +
          2 ^ n * survivorParityCount n := by
  let M := 2 ^ n
  let S := survivorParityCount n
  let C := survivorResidueStartCount n hn X
  let q := X / M
  have hSand := survivorResidueStartCount_sandwich (n := n) (X := X) hn
  have hLower : S * q ≤ C := by simpa [M, S, C, q] using hSand.1
  have hUpper : C ≤ S * (q + 1) := by simpa [M, S, C, q] using hSand.2
  have hBlockLower : M * q ≤ X := by
    simpa [M, q] using twoPow_mul_div_le n X
  have hBlockUpper : X ≤ M * (q + 1) := by
    exact le_of_lt (by
      simpa [M, q] using lt_twoPow_mul_div_add_one n X)
  constructor
  · calc
      M * C ≤ M * (S * (q + 1)) := Nat.mul_le_mul_left M hUpper
      _ = S * (M * q) + M * S := by ring
      _ ≤ S * X + M * S :=
        Nat.add_le_add_right (Nat.mul_le_mul_left S hBlockLower) _
  · calc
      S * X ≤ S * (M * (q + 1)) := Nat.mul_le_mul_left S hBlockUpper
      _ = M * (S * q) + M * S := by ring
      _ ≤ M * C + M * S :=
        Nat.add_le_add_right (Nat.mul_le_mul_left M hLower) _

/-- `X` 未満の survivor residue starts の割合。 -/
noncomputable def survivorResidueStartRatio
    (n : ℕ)
    (hn : 0 < n)
    (X : ℕ) : ℝ :=
  (survivorResidueStartCount n hn X : ℝ) / (X : ℝ)

/-- fixed depth の survivor residue union は density `S_n / 2^n` を持つ。 -/
theorem survivorResidueStartRatio_tendsto
    {n : ℕ}
    (hn : 0 < n) :
    Tendsto
      (survivorResidueStartRatio n hn)
      atTop
      (𝓝 (survivorParityRatio n)) := by
  unfold survivorResidueStartRatio survivorParityRatio
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    tendsto_ratio_of_nat_cross_discrepancy
      (2 ^ n)
      (survivorParityCount n)
      (Arithmetic.twoPow_pos n)
      (survivorResidueStartCount n hn)
      (fun X =>
        survivorResidueStartCount_cross_discrepancy
          (n := n) (X := X) hn)

/-! ## minimal critical-start 全幅 union の bounded counting -/

/-- 全幅 minimal critical starts のうち `B` 未満。 -/
abbrev AnyActualCriticalStartBelow (B : ℕ) :=
  {x : ℕ // x < B ∧ IsAnyActualCriticalStart x}

/-- bounded global minimal-start type は有限。 -/
theorem anyActualCriticalStartBelow_finite
    (B : ℕ) :
    Finite (AnyActualCriticalStartBelow B) := by
  exact
    Finite.of_injective
      (fun x : AnyActualCriticalStartBelow B =>
        (⟨x.1, x.2.1⟩ : Fin B))
      (by
        intro a b h
        apply Subtype.ext
        exact congrArg Fin.val h)

/-- 全幅 minimal critical starts の bounded count。 -/
noncomputable def anyActualCriticalStartCount (B : ℕ) : ℕ :=
  Nat.card (AnyActualCriticalStartBelow B)

/-- widths `1,...,L` の bounded count。 -/
noncomputable def positiveWidthCriticalStartCount
    (L B : ℕ) : ℕ :=
  ∑ i : Fin L, actualCriticalStartCount (i.1 + 1) B

/-- width-tagged finite family から全幅 union へ tag を忘れる。 -/
def positiveWidthCriticalStartToAnyBelow
    (L B : ℕ) :
    PositiveWidthCriticalStartsBelow L B →
      AnyActualCriticalStartBelow B :=
  fun T =>
    ⟨T.2.1, T.2.2.1, ⟨T.1.1 + 1, T.2.2.2⟩⟩

/-- width uniqueness により tag を忘れても単射。 -/
theorem positiveWidthCriticalStartToAnyBelow_injective
    (L B : ℕ) :
    Function.Injective (positiveWidthCriticalStartToAnyBelow L B) := by
  intro A B'
  rcases A with ⟨i, x⟩
  rcases B' with ⟨j, y⟩
  intro h
  have hxy : x.1 = y.1 := congrArg Subtype.val h
  have hyAtX : IsActualCriticalStart (j.1 + 1) x.1 := by
    rw [hxy]
    exact y.2.2
  have hWidth : i.1 + 1 = j.1 + 1 :=
    actualCriticalStart_width_unique x.2.2 hyAtX
  have hij : i = j := by
    apply Fin.ext
    omega
  subst j
  have hSub : x = y := by
    apply Subtype.ext
    exact hxy
  subst y
  rfl

/-- finite widths は global union の下側部分集合。 -/
theorem positiveWidthCriticalStartCount_le_any
    (L B : ℕ) :
    positiveWidthCriticalStartCount L B ≤
      anyActualCriticalStartCount B := by
  let : Finite (AnyActualCriticalStartBelow B) :=
    anyActualCriticalStartBelow_finite B
  have hCard :
      Nat.card (PositiveWidthCriticalStartsBelow L B) ≤
        Nat.card (AnyActualCriticalStartBelow B) :=
    Nat.card_le_card_of_injective
      (positiveWidthCriticalStartToAnyBelow L B)
      (positiveWidthCriticalStartToAnyBelow_injective L B)
  rw [positiveWidthCriticalStartsBelow_card] at hCard
  simpa [positiveWidthCriticalStartCount, anyActualCriticalStartCount] using hCard

/-- actual critical start の幅は正。 -/
theorem width_pos_of_actualCriticalStart
    {m x : ℕ}
    (h : IsActualCriticalStart m x) :
    0 < m := by
  rcases h with ⟨W, y, hRun⟩
  have hPos : 0 < Word.oddSteps W.1 :=
    (criticalWordToFullFirstCrossingWord W).2.2.2.oddSteps_pos
  rw [W.2.oddSteps_eq] at hPos
  exact hPos

/-- finite/tail sum の underlying start。単射性を値だけで読むための補助写像。 -/
def criticalFiniteOrSurvivorVal
    {L B : ℕ}
    (_hL : 0 < L) :
    (PositiveWidthCriticalStartsBelow L B ⊕
      SurvivorResidueStartBelow
        (Critical.criticalTwoDepth L)
        (criticalTwoDepth_pos L)
        B) → ℕ
  | Sum.inl T => T.2.1
  | Sum.inr T => T.1

/--
全幅 bounded start を、width `≤L` の有限部分か depth `H_L` survivor tail に分類する。
-/
noncomputable def anyCriticalStartBelowToFiniteOrSurvivor
    (L : ℕ)
    (hL : 0 < L)
    (B : ℕ) :
    AnyActualCriticalStartBelow B →
      (PositiveWidthCriticalStartsBelow L B ⊕
        SurvivorResidueStartBelow
          (Critical.criticalTwoDepth L)
          (criticalTwoDepth_pos L)
          B) := by
  classical
  intro X
  let m := Classical.choose X.2.2
  have hmStart : IsActualCriticalStart m X.1 :=
    Classical.choose_spec X.2.2
  have hmPos : 0 < m := width_pos_of_actualCriticalStart hmStart
  by_cases hmL : m ≤ L
  · let i : Fin L := ⟨m - 1, by omega⟩
    have hi : i.1 + 1 = m := by
      dsimp [i]
      omega
    exact Sum.inl
      ⟨i, ⟨X.1, X.2.1, by simpa [hi] using hmStart⟩⟩
  · have hLm : L < m := Nat.lt_of_not_ge hmL
    exact Sum.inr
      ⟨X.1, X.2.1,
        actualCriticalStart_tail_isSurvivorResidueStart
          hL hLm hmStart⟩

/-- 上の分類写像は underlying start を保存する。 -/
theorem criticalFiniteOrSurvivorVal_map
    (L : ℕ)
    (hL : 0 < L)
    (B : ℕ)
    (X : AnyActualCriticalStartBelow B) :
    criticalFiniteOrSurvivorVal hL
      (anyCriticalStartBelowToFiniteOrSurvivor L hL B X) = X.1 := by
  classical
  let m := Classical.choose X.2.2
  by_cases hmL : m ≤ L
  · simp [anyCriticalStartBelowToFiniteOrSurvivor,
      criticalFiniteOrSurvivorVal, m, hmL]
  · simp [anyCriticalStartBelowToFiniteOrSurvivor,
      criticalFiniteOrSurvivorVal, m, hmL]

/-- underlying start を保存するので分類写像は単射。 -/
theorem anyCriticalStartBelowToFiniteOrSurvivor_injective
    (L : ℕ)
    (hL : 0 < L)
    (B : ℕ) :
    Function.Injective
      (anyCriticalStartBelowToFiniteOrSurvivor L hL B) := by
  intro A B' h
  apply Subtype.ext
  have hVal := congrArg (criticalFiniteOrSurvivorVal hL) h
  rw [criticalFiniteOrSurvivorVal_map,
      criticalFiniteOrSurvivorVal_map] at hVal
  exact hVal

/-- global minimal-start count の finite-width + survivor-tail upper bound。 -/
theorem anyActualCriticalStartCount_le_finite_add_survivor
    (L : ℕ)
    (hL : 0 < L)
    (B : ℕ) :
    anyActualCriticalStartCount B ≤
      positiveWidthCriticalStartCount L B +
        survivorResidueStartCount
          (Critical.criticalTwoDepth L)
          (criticalTwoDepth_pos L)
          B := by
  let : Finite (AnyActualCriticalStartBelow B) :=
    anyActualCriticalStartBelow_finite B
  let : ∀ i : Fin L,
      Finite (ActualCriticalStartBelow (i.1 + 1) B) :=
    fun i => actualCriticalStartBelow_finite (i.1 + 1) B
  let : Finite (PositiveWidthCriticalStartsBelow L B) := inferInstance
  let : Finite
      (SurvivorResidueStartBelow
        (Critical.criticalTwoDepth L)
        (criticalTwoDepth_pos L)
        B) :=
    survivorResidueStartBelow_finite
      (Critical.criticalTwoDepth L) (criticalTwoDepth_pos L) B
  have hCard :
      Nat.card (AnyActualCriticalStartBelow B) ≤
        Nat.card
          (PositiveWidthCriticalStartsBelow L B ⊕
            SurvivorResidueStartBelow
              (Critical.criticalTwoDepth L)
              (criticalTwoDepth_pos L)
              B) :=
    Nat.card_le_card_of_injective
      (anyCriticalStartBelowToFiniteOrSurvivor L hL B)
      (anyCriticalStartBelowToFiniteOrSurvivor_injective L hL B)
  rw [Nat.card_sum, positiveWidthCriticalStartsBelow_card] at hCard
  simpa [anyActualCriticalStartCount, positiveWidthCriticalStartCount,
    survivorResidueStartCount] using hCard

/-- 全幅 minimal start count の finite/tail sandwich。 -/
theorem anyActualCriticalStartCount_sandwich
    (L : ℕ)
    (hL : 0 < L)
    (B : ℕ) :
    positiveWidthCriticalStartCount L B ≤
        anyActualCriticalStartCount B ∧
      anyActualCriticalStartCount B ≤
        positiveWidthCriticalStartCount L B +
          survivorResidueStartCount
            (Critical.criticalTwoDepth L)
            (criticalTwoDepth_pos L)
            B :=
  ⟨positiveWidthCriticalStartCount_le_any L B,
    anyActualCriticalStartCount_le_finite_add_survivor L hL B⟩

/-! ## full first-crossing 全幅 union の bounded counting -/

/-- terminal overshoot を許した全幅 first-crossing start。 -/
def IsAnyFullActualCriticalStart (x : ℕ) : Prop :=
  ∃ m : ℕ, IsFullActualCriticalStart m x

/-- bounded full union。 -/
abbrev AnyFullActualCriticalStartBelow (B : ℕ) :=
  {x : ℕ // x < B ∧ IsAnyFullActualCriticalStart x}

/-- bounded full union は有限。 -/
theorem anyFullActualCriticalStartBelow_finite
    (B : ℕ) :
    Finite (AnyFullActualCriticalStartBelow B) := by
  exact
    Finite.of_injective
      (fun x : AnyFullActualCriticalStartBelow B =>
        (⟨x.1, x.2.1⟩ : Fin B))
      (by
        intro a b h
        apply Subtype.ext
        exact congrArg Fin.val h)

/-- full union bounded count。 -/
noncomputable def anyFullActualCriticalStartCount (B : ℕ) : ℕ :=
  Nat.card (AnyFullActualCriticalStartBelow B)

/-- widths `1,...,L` の bounded full-start count。 -/
noncomputable def positiveWidthFullCriticalStartCount
    (L B : ℕ) : ℕ :=
  ∑ i : Fin L, fullActualCriticalStartCount (i.1 + 1) B

/-- finite full widths から global full union へ tag を忘れる。 -/
def positiveWidthFullStartToAnyBelow
    (L B : ℕ) :
    PositiveWidthFullCriticalStartsBelow L B →
      AnyFullActualCriticalStartBelow B :=
  fun T =>
    ⟨T.2.1, T.2.2.1, ⟨T.1.1 + 1, T.2.2.2⟩⟩

/-- full width uniqueness により tag を忘れても単射。 -/
theorem positiveWidthFullStartToAnyBelow_injective
    (L B : ℕ) :
    Function.Injective (positiveWidthFullStartToAnyBelow L B) := by
  intro A B'
  rcases A with ⟨i, x⟩
  rcases B' with ⟨j, y⟩
  intro h
  have hxy : x.1 = y.1 := congrArg Subtype.val h
  have hyAtX : IsFullActualCriticalStart (j.1 + 1) x.1 := by
    rw [hxy]
    exact y.2.2
  have hWidth : i.1 + 1 = j.1 + 1 :=
    fullActualCriticalStart_width_unique x.2.2 hyAtX
  have hij : i = j := by
    apply Fin.ext
    omega
  subst j
  have hSub : x = y := by
    apply Subtype.ext
    exact hxy
  subst y
  rfl

/-- finite full widths are below the global full union。 -/
theorem positiveWidthFullCriticalStartCount_le_any
    (L B : ℕ) :
    positiveWidthFullCriticalStartCount L B ≤
      anyFullActualCriticalStartCount B := by
  let : Finite (AnyFullActualCriticalStartBelow B) :=
    anyFullActualCriticalStartBelow_finite B
  have hCard :
      Nat.card (PositiveWidthFullCriticalStartsBelow L B) ≤
        Nat.card (AnyFullActualCriticalStartBelow B) :=
    Nat.card_le_card_of_injective
      (positiveWidthFullStartToAnyBelow L B)
      (positiveWidthFullStartToAnyBelow_injective L B)
  rw [positiveWidthFullCriticalStartsBelow_card] at hCard
  simpa [positiveWidthFullCriticalStartCount,
    anyFullActualCriticalStartCount] using hCard

/-- full actual first-crossing start の幅は正。 -/
theorem width_pos_of_fullActualCriticalStart
    {m x : ℕ}
    (h : IsFullActualCriticalStart m x) :
    0 < m := by
  rcases h with ⟨W, y, hRun⟩
  have hPos : 0 < Word.oddSteps W.1 := W.2.2.2.oddSteps_pos
  rw [W.2.oddSteps_eq] at hPos
  exact hPos

/-- full finite/tail sum の underlying start。 -/
def fullFiniteOrSurvivorVal
    {L B : ℕ}
    (_hL : 0 < L) :
    (PositiveWidthFullCriticalStartsBelow L B ⊕
      SurvivorResidueStartBelow
        (Critical.criticalTwoDepth L)
        (criticalTwoDepth_pos L)
        B) → ℕ
  | Sum.inl T => T.2.1
  | Sum.inr T => T.1

/-- global full bounded start を finite widths / survivor tail に分類。 -/
noncomputable def anyFullStartBelowToFiniteOrSurvivor
    (L : ℕ)
    (hL : 0 < L)
    (B : ℕ) :
    AnyFullActualCriticalStartBelow B →
      (PositiveWidthFullCriticalStartsBelow L B ⊕
        SurvivorResidueStartBelow
          (Critical.criticalTwoDepth L)
          (criticalTwoDepth_pos L)
          B) := by
  classical
  intro X
  let m := Classical.choose X.2.2
  have hmStart : IsFullActualCriticalStart m X.1 :=
    Classical.choose_spec X.2.2
  have hmPos : 0 < m := width_pos_of_fullActualCriticalStart hmStart
  by_cases hmL : m ≤ L
  · let i : Fin L := ⟨m - 1, by omega⟩
    have hi : i.1 + 1 = m := by
      dsimp [i]
      omega
    exact Sum.inl
      ⟨i, ⟨X.1, X.2.1, by simpa [hi] using hmStart⟩⟩
  · have hLm : L < m := Nat.lt_of_not_ge hmL
    exact Sum.inr
      ⟨X.1, X.2.1,
        fullActualCriticalStart_tail_isSurvivorResidueStart
          hL hLm hmStart⟩

/-- full 分類写像は underlying start を保存。 -/
theorem fullFiniteOrSurvivorVal_map
    (L : ℕ)
    (hL : 0 < L)
    (B : ℕ)
    (X : AnyFullActualCriticalStartBelow B) :
    fullFiniteOrSurvivorVal hL
      (anyFullStartBelowToFiniteOrSurvivor L hL B X) = X.1 := by
  classical
  let m := Classical.choose X.2.2
  by_cases hmL : m ≤ L
  · simp [anyFullStartBelowToFiniteOrSurvivor,
      fullFiniteOrSurvivorVal, m, hmL]
  · simp [anyFullStartBelowToFiniteOrSurvivor,
      fullFiniteOrSurvivorVal, m, hmL]

/-- full 分類写像は単射。 -/
theorem anyFullStartBelowToFiniteOrSurvivor_injective
    (L : ℕ)
    (hL : 0 < L)
    (B : ℕ) :
    Function.Injective
      (anyFullStartBelowToFiniteOrSurvivor L hL B) := by
  intro A B' h
  apply Subtype.ext
  have hVal := congrArg (fullFiniteOrSurvivorVal hL) h
  rw [fullFiniteOrSurvivorVal_map,
      fullFiniteOrSurvivorVal_map] at hVal
  exact hVal

/-- global full count の finite + survivor upper bound。 -/
theorem anyFullActualCriticalStartCount_le_finite_add_survivor
    (L : ℕ)
    (hL : 0 < L)
    (B : ℕ) :
    anyFullActualCriticalStartCount B ≤
      positiveWidthFullCriticalStartCount L B +
        survivorResidueStartCount
          (Critical.criticalTwoDepth L)
          (criticalTwoDepth_pos L)
          B := by
  let : Finite (AnyFullActualCriticalStartBelow B) :=
    anyFullActualCriticalStartBelow_finite B
  let : ∀ i : Fin L,
      Finite (FullActualCriticalStartBelow (i.1 + 1) B) :=
    fun i => fullActualCriticalStartBelow_finite (i.1 + 1) B
  let : Finite (PositiveWidthFullCriticalStartsBelow L B) := inferInstance
  let : Finite
      (SurvivorResidueStartBelow
        (Critical.criticalTwoDepth L)
        (criticalTwoDepth_pos L)
        B) :=
    survivorResidueStartBelow_finite
      (Critical.criticalTwoDepth L) (criticalTwoDepth_pos L) B
  have hCard :
      Nat.card (AnyFullActualCriticalStartBelow B) ≤
        Nat.card
          (PositiveWidthFullCriticalStartsBelow L B ⊕
            SurvivorResidueStartBelow
              (Critical.criticalTwoDepth L)
              (criticalTwoDepth_pos L)
              B) :=
    Nat.card_le_card_of_injective
      (anyFullStartBelowToFiniteOrSurvivor L hL B)
      (anyFullStartBelowToFiniteOrSurvivor_injective L hL B)
  rw [Nat.card_sum, positiveWidthFullCriticalStartsBelow_card] at hCard
  simpa [anyFullActualCriticalStartCount,
    positiveWidthFullCriticalStartCount,
    survivorResidueStartCount] using hCard

/-- global full count の finite/tail sandwich。 -/
theorem anyFullActualCriticalStartCount_sandwich
    (L : ℕ)
    (hL : 0 < L)
    (B : ℕ) :
    positiveWidthFullCriticalStartCount L B ≤
        anyFullActualCriticalStartCount B ∧
      anyFullActualCriticalStartCount B ≤
        positiveWidthFullCriticalStartCount L B +
          survivorResidueStartCount
            (Critical.criticalTwoDepth L)
            (criticalTwoDepth_pos L)
            B :=
  ⟨positiveWidthFullCriticalStartCount_le_any L B,
    anyFullActualCriticalStartCount_le_finite_add_survivor L hL B⟩

/-! ## ratios と fixed-L limits -/

/-- finite minimal-width family の bounded ratio。 -/
noncomputable def positiveWidthCriticalStartRatio
    (L B : ℕ) : ℝ :=
  (positiveWidthCriticalStartCount L B : ℝ) / (B : ℝ)

/-- finite minimal-width family の density sum。 -/
noncomputable def positiveWidthCriticalStartDensity
    (L : ℕ) : ℝ :=
  ∑ i : Fin L, fixedWidthCriticalStartDensity (i.1 + 1)

/-- finite full-width family の bounded ratio。 -/
noncomputable def positiveWidthFullCriticalStartRatio
    (L B : ℕ) : ℝ :=
  (positiveWidthFullCriticalStartCount L B : ℝ) / (B : ℝ)

/-- finite full-width family の density sum。 -/
noncomputable def positiveWidthFullCriticalStartDensity
    (L : ℕ) : ℝ :=
  ∑ i : Fin L, fullFixedWidthCriticalStartDensity (i.1 + 1)

/-- global minimal union ratio。 -/
noncomputable def anyActualCriticalStartRatio (B : ℕ) : ℝ :=
  (anyActualCriticalStartCount B : ℝ) / (B : ℝ)

/-- global full union ratio。 -/
noncomputable def anyFullActualCriticalStartRatio (B : ℕ) : ℝ :=
  (anyFullActualCriticalStartCount B : ℝ) / (B : ℝ)

/-- finite minimal ratio は fixed-width ratios の和。 -/
theorem positiveWidthCriticalStartRatio_eq_sum
    (L B : ℕ) :
    positiveWidthCriticalStartRatio L B =
      ∑ i : Fin L, fixedWidthCriticalStartRatio (i.1 + 1) B := by
  unfold positiveWidthCriticalStartRatio positiveWidthCriticalStartCount
    fixedWidthCriticalStartRatio
  push_cast
  rw [Finset.sum_div]

/-- finite full ratio は fixed-width full ratios の和。 -/
theorem positiveWidthFullCriticalStartRatio_eq_sum
    (L B : ℕ) :
    positiveWidthFullCriticalStartRatio L B =
      ∑ i : Fin L, fullFixedWidthCriticalStartRatio (i.1 + 1) B := by
  unfold positiveWidthFullCriticalStartRatio positiveWidthFullCriticalStartCount
    fullFixedWidthCriticalStartRatio
  push_cast
  rw [Finset.sum_div]

/-- fixed `L` では finite minimal union ratio が density sum へ収束。 -/
theorem positiveWidthCriticalStartRatio_tendsto
    (L : ℕ) :
    Tendsto
      (positiveWidthCriticalStartRatio L)
      atTop
      (𝓝 (positiveWidthCriticalStartDensity L)) := by
  have hSum :
      Tendsto
        (fun B : ℕ =>
          ∑ i ∈ (Finset.univ : Finset (Fin L)),
            fixedWidthCriticalStartRatio (i.1 + 1) B)
        atTop
        (𝓝
          (∑ i ∈ (Finset.univ : Finset (Fin L)),
            fixedWidthCriticalStartDensity (i.1 + 1))) := by
    apply tendsto_finsetSum
    intro i hi
    exact fixedWidthCriticalStartRatio_tendsto (Nat.succ_pos i.1)
  have hRatio :
      (fun B : ℕ => positiveWidthCriticalStartRatio L B) =
        (fun B : ℕ =>
          ∑ i ∈ (Finset.univ : Finset (Fin L)),
            fixedWidthCriticalStartRatio (i.1 + 1) B) := by
    funext B
    exact positiveWidthCriticalStartRatio_eq_sum L B
  have hDensity :
      positiveWidthCriticalStartDensity L =
        ∑ i ∈ (Finset.univ : Finset (Fin L)),
          fixedWidthCriticalStartDensity (i.1 + 1) := by
    rfl
  change
    Tendsto
      (fun B : ℕ => positiveWidthCriticalStartRatio L B)
      atTop
      (𝓝 (positiveWidthCriticalStartDensity L))
  rw [hRatio, hDensity]
  exact hSum

/-- fixed `L` では finite full union ratio が density sum へ収束。 -/
theorem positiveWidthFullCriticalStartRatio_tendsto
    (L : ℕ) :
    Tendsto
      (positiveWidthFullCriticalStartRatio L)
      atTop
      (𝓝 (positiveWidthFullCriticalStartDensity L)) := by
  have hSum :
      Tendsto
        (fun B : ℕ =>
          ∑ i ∈ (Finset.univ : Finset (Fin L)),
            fullFixedWidthCriticalStartRatio (i.1 + 1) B)
        atTop
        (𝓝
          (∑ i ∈ (Finset.univ : Finset (Fin L)),
            fullFixedWidthCriticalStartDensity (i.1 + 1))) := by
    apply tendsto_finsetSum
    intro i hi
    exact fullFixedWidthCriticalStartRatio_tendsto (Nat.succ_pos i.1)
  have hRatio :
      (fun B : ℕ => positiveWidthFullCriticalStartRatio L B) =
        (fun B : ℕ =>
          ∑ i ∈ (Finset.univ : Finset (Fin L)),
            fullFixedWidthCriticalStartRatio (i.1 + 1) B) := by
    funext B
    exact positiveWidthFullCriticalStartRatio_eq_sum L B
  have hDensity :
      positiveWidthFullCriticalStartDensity L =
        ∑ i ∈ (Finset.univ : Finset (Fin L)),
          fullFixedWidthCriticalStartDensity (i.1 + 1) := by
    rfl
  change
    Tendsto
      (fun B : ℕ => positiveWidthFullCriticalStartRatio L B)
      atTop
      (𝓝 (positiveWidthFullCriticalStartDensity L))
  rw [hRatio, hDensity]
  exact hSum

/-- minimal global ratio の fixed-L sandwich。 -/
theorem anyActualCriticalStartRatio_sandwich
    (L : ℕ)
    (hL : 0 < L)
    (B : ℕ) :
    positiveWidthCriticalStartRatio L B ≤
        anyActualCriticalStartRatio B ∧
      anyActualCriticalStartRatio B ≤
        positiveWidthCriticalStartRatio L B +
          survivorResidueStartRatio
            (Critical.criticalTwoDepth L)
            (criticalTwoDepth_pos L)
            B := by
  have hNat := anyActualCriticalStartCount_sandwich L hL B
  have hLower :
      (positiveWidthCriticalStartCount L B : ℝ) ≤
        (anyActualCriticalStartCount B : ℝ) := by
    exact_mod_cast hNat.1
  have hUpper :
      (anyActualCriticalStartCount B : ℝ) ≤
        (positiveWidthCriticalStartCount L B : ℝ) +
          (survivorResidueStartCount
            (Critical.criticalTwoDepth L)
            (criticalTwoDepth_pos L)
            B : ℝ) := by
    exact_mod_cast hNat.2
  have hB : (0 : ℝ) ≤ (B : ℝ) := by positivity
  constructor
  · unfold positiveWidthCriticalStartRatio anyActualCriticalStartRatio
    exact div_le_div_of_nonneg_right hLower hB
  · unfold anyActualCriticalStartRatio positiveWidthCriticalStartRatio
      survivorResidueStartRatio
    calc
      (anyActualCriticalStartCount B : ℝ) / (B : ℝ)
          ≤
          ((positiveWidthCriticalStartCount L B : ℝ) +
            (survivorResidueStartCount
              (Critical.criticalTwoDepth L)
              (criticalTwoDepth_pos L)
              B : ℝ)) / (B : ℝ) :=
        div_le_div_of_nonneg_right hUpper hB
      _ =
          (positiveWidthCriticalStartCount L B : ℝ) / (B : ℝ) +
            (survivorResidueStartCount
              (Critical.criticalTwoDepth L)
              (criticalTwoDepth_pos L)
              B : ℝ) / (B : ℝ) := by rw [add_div]

/-- full global ratio の fixed-L sandwich。 -/
theorem anyFullActualCriticalStartRatio_sandwich
    (L : ℕ)
    (hL : 0 < L)
    (B : ℕ) :
    positiveWidthFullCriticalStartRatio L B ≤
        anyFullActualCriticalStartRatio B ∧
      anyFullActualCriticalStartRatio B ≤
        positiveWidthFullCriticalStartRatio L B +
          survivorResidueStartRatio
            (Critical.criticalTwoDepth L)
            (criticalTwoDepth_pos L)
            B := by
  have hNat := anyFullActualCriticalStartCount_sandwich L hL B
  have hLower :
      (positiveWidthFullCriticalStartCount L B : ℝ) ≤
        (anyFullActualCriticalStartCount B : ℝ) := by
    exact_mod_cast hNat.1
  have hUpper :
      (anyFullActualCriticalStartCount B : ℝ) ≤
        (positiveWidthFullCriticalStartCount L B : ℝ) +
          (survivorResidueStartCount
            (Critical.criticalTwoDepth L)
            (criticalTwoDepth_pos L)
            B : ℝ) := by
    exact_mod_cast hNat.2
  have hB : (0 : ℝ) ≤ (B : ℝ) := by positivity
  constructor
  · unfold positiveWidthFullCriticalStartRatio anyFullActualCriticalStartRatio
    exact div_le_div_of_nonneg_right hLower hB
  · unfold anyFullActualCriticalStartRatio positiveWidthFullCriticalStartRatio
      survivorResidueStartRatio
    calc
      (anyFullActualCriticalStartCount B : ℝ) / (B : ℝ)
          ≤
          ((positiveWidthFullCriticalStartCount L B : ℝ) +
            (survivorResidueStartCount
              (Critical.criticalTwoDepth L)
              (criticalTwoDepth_pos L)
              B : ℝ)) / (B : ℝ) :=
        div_le_div_of_nonneg_right hUpper hB
      _ =
          (positiveWidthFullCriticalStartCount L B : ℝ) / (B : ℝ) +
            (survivorResidueStartCount
              (Critical.criticalTwoDepth L)
              (criticalTwoDepth_pos L)
              B : ℝ) / (B : ℝ) := by rw [add_div]

/-! ## outer-width limits -/

/-- finite minimal density sums converge to `1/4`。 -/
theorem positiveWidthCriticalStartDensity_tendsto_quarter :
    Tendsto
      positiveWidthCriticalStartDensity
      atTop
      (𝓝 ((1 : ℝ) / 4)) := by
  have h := hasSum_criticalActualStartDensityMass.tendsto_sum_nat
  have hEq :
      (fun L : ℕ => positiveWidthCriticalStartDensity L) =
        (fun L : ℕ =>
          ∑ j ∈ Finset.range L, criticalActualStartDensityMass j) := by
    funext L
    unfold positiveWidthCriticalStartDensity
    calc
      (∑ i : Fin L, fixedWidthCriticalStartDensity (i.1 + 1)) =
          ∑ j ∈ Finset.range L,
            fixedWidthCriticalStartDensity (j + 1) := by
        exact
          Fin.sum_univ_eq_sum_range
            (fun j : ℕ => fixedWidthCriticalStartDensity (j + 1))
            L
      _ = ∑ j ∈ Finset.range L, criticalActualStartDensityMass j := by
        apply Finset.sum_congr rfl
        intro j hj
        rfl
  change
    Tendsto
      (fun L : ℕ => positiveWidthCriticalStartDensity L)
      atTop
      (𝓝 ((1 : ℝ) / 4))
  rw [hEq]
  exact h

/-- full fixed-width density mass は Kraft mass と一致。 -/
theorem fullFixedWidthCriticalStartDensity_eq_kraftMass
    (j : ℕ) :
    fullFixedWidthCriticalStartDensity (j + 1) =
      criticalPartitionKraftMass j := by
  unfold fullFixedWidthCriticalStartDensity criticalPartitionKraftMass
    fullCrossingStartModulus Arithmetic.twoPowModulus
  norm_num only [Nat.cast_pow, Nat.cast_ofNat]

/-- finite full density sums converge to `1/2`。 -/
theorem positiveWidthFullCriticalStartDensity_tendsto_half :
    Tendsto
      positiveWidthFullCriticalStartDensity
      atTop
      (𝓝 ((1 : ℝ) / 2)) := by
  have h := hasSum_criticalPartitionKraftMass.tendsto_sum_nat
  have hEq :
      (fun L : ℕ => positiveWidthFullCriticalStartDensity L) =
        (fun L : ℕ =>
          ∑ j ∈ Finset.range L, criticalPartitionKraftMass j) := by
    funext L
    unfold positiveWidthFullCriticalStartDensity
    calc
      (∑ i : Fin L, fullFixedWidthCriticalStartDensity (i.1 + 1)) =
          ∑ j ∈ Finset.range L,
            fullFixedWidthCriticalStartDensity (j + 1) := by
        exact
          Fin.sum_univ_eq_sum_range
            (fun j : ℕ => fullFixedWidthCriticalStartDensity (j + 1))
            L
      _ = ∑ j ∈ Finset.range L, criticalPartitionKraftMass j := by
        apply Finset.sum_congr rfl
        intro j hj
        exact fullFixedWidthCriticalStartDensity_eq_kraftMass j
  change
    Tendsto
      (fun L : ℕ => positiveWidthFullCriticalStartDensity L)
      atTop
      (𝓝 ((1 : ℝ) / 2))
  rw [hEq]
  exact h

/-- survivor ratio 自体も raw depth `n -> ∞` で 0 へ行く。 -/
theorem tendsto_survivorParityRatio_raw_zero :
    Tendsto survivorParityRatio atTop (𝓝 0) := by
  apply (tendsto_add_atTop_iff_nat 1).1
  simpa [Nat.add_comm] using tendsto_survivorParityRatio_zero

/-- critical depths `H_(L+1)` に沿った survivor mass も 0 へ行く。 -/
theorem tendsto_survivorParityRatio_criticalDepth_succ_zero :
    Tendsto
      (fun L : ℕ =>
        survivorParityRatio (Critical.criticalTwoDepth (L + 1)))
      atTop
      (𝓝 0) := by
  have hDepth :
      Tendsto
        (fun L : ℕ => Critical.criticalTwoDepth (L + 1))
        atTop atTop :=
    criticalTwoDepth_strictMono.tendsto_atTop.comp
      (tendsto_add_atTop_nat 1)
  exact tendsto_survivorParityRatio_raw_zero.comp hDepth

/-!
二段階 squeeze の一般補題。

各 outer parameter `k` で `lo k B ≤ f B ≤ hi k B` があり、`B -> ∞` で
それぞれ `loLim k`, `hiLim k` へ行く。さらに outer limit `k -> ∞` で両端が
同じ `a` に収束するなら `f B -> a`。
-/
theorem tendsto_of_two_scale_squeeze
    {f : ℕ → ℝ}
    {lo hi : ℕ → ℕ → ℝ}
    {loLim hiLim : ℕ → ℝ}
    {a : ℝ}
    (hLoInner : ∀ k : ℕ, Tendsto (lo k) atTop (𝓝 (loLim k)))
    (hHiInner : ∀ k : ℕ, Tendsto (hi k) atTop (𝓝 (hiLim k)))
    (hSand : ∀ k B : ℕ, lo k B ≤ f B ∧ f B ≤ hi k B)
    (hLoOuter : Tendsto loLim atTop (𝓝 a))
    (hHiOuter : Tendsto hiLim atTop (𝓝 a)) :
    Tendsto f atTop (𝓝 a) := by
  rw [Metric.tendsto_atTop] at hLoOuter hHiOuter ⊢
  intro ε hε
  have hε4 : 0 < ε / 4 := by linarith
  rcases hLoOuter (ε / 4) hε4 with ⟨K₁, hK₁⟩
  rcases hHiOuter (ε / 4) hε4 with ⟨K₂, hK₂⟩
  let K := max K₁ K₂
  have hLoLim : dist (loLim K) a < ε / 4 :=
    hK₁ K (le_max_left _ _)
  have hHiLim : dist (hiLim K) a < ε / 4 :=
    hK₂ K (le_max_right _ _)
  have hLoK := hLoInner K
  have hHiK := hHiInner K
  rw [Metric.tendsto_atTop] at hLoK hHiK
  rcases hLoK (ε / 4) hε4 with ⟨N₁, hN₁⟩
  rcases hHiK (ε / 4) hε4 with ⟨N₂, hN₂⟩
  refine ⟨max N₁ N₂, ?_⟩
  intro B hB
  have hLoB : dist (lo K B) (loLim K) < ε / 4 :=
    hN₁ B (le_trans (le_max_left _ _) hB)
  have hHiB : dist (hi K B) (hiLim K) < ε / 4 :=
    hN₂ B (le_trans (le_max_right _ _) hB)
  have hBounds := hSand K B
  rw [Real.dist_eq] at hLoLim hHiLim hLoB hHiB ⊢
  rw [abs_lt] at hLoLim hHiLim hLoB hHiB ⊢
  constructor <;> linarith [hBounds.1, hBounds.2]

/-! ## exact global natural densities -/

/-- 全幅 minimal critical-start union 自身の自然密度は exact に `1/4`。 -/
theorem anyActualCriticalStartRatio_tendsto_quarter :
    Tendsto
      anyActualCriticalStartRatio
      atTop
      (𝓝 ((1 : ℝ) / 4)) := by
  let lo : ℕ → ℕ → ℝ :=
    fun k B => positiveWidthCriticalStartRatio (k + 1) B
  let hi : ℕ → ℕ → ℝ :=
    fun k B =>
      positiveWidthCriticalStartRatio (k + 1) B +
        survivorResidueStartRatio
          (Critical.criticalTwoDepth (k + 1))
          (criticalTwoDepth_pos (k + 1))
          B
  let loLim : ℕ → ℝ :=
    fun k => positiveWidthCriticalStartDensity (k + 1)
  let hiLim : ℕ → ℝ :=
    fun k =>
      positiveWidthCriticalStartDensity (k + 1) +
        survivorParityRatio (Critical.criticalTwoDepth (k + 1))
  apply tendsto_of_two_scale_squeeze
      (f := anyActualCriticalStartRatio)
      (lo := lo) (hi := hi)
      (loLim := loLim) (hiLim := hiLim)
  · intro k
    exact positiveWidthCriticalStartRatio_tendsto (k + 1)
  · intro k
    exact
      (positiveWidthCriticalStartRatio_tendsto (k + 1)).add
        (survivorResidueStartRatio_tendsto
          (criticalTwoDepth_pos (k + 1)))
  · intro k B
    simpa [lo, hi] using
      anyActualCriticalStartRatio_sandwich
        (k + 1) (Nat.succ_pos k) B
  · exact
      positiveWidthCriticalStartDensity_tendsto_quarter.comp
        (tendsto_add_atTop_nat 1)
  · have h :=
      (positiveWidthCriticalStartDensity_tendsto_quarter.comp
        (tendsto_add_atTop_nat 1)).add
        tendsto_survivorParityRatio_criticalDepth_succ_zero
    simpa [hiLim] using h

/-- 全幅 full first-crossing union 自身の自然密度は exact に `1/2`。 -/
theorem anyFullActualCriticalStartRatio_tendsto_half :
    Tendsto
      anyFullActualCriticalStartRatio
      atTop
      (𝓝 ((1 : ℝ) / 2)) := by
  let lo : ℕ → ℕ → ℝ :=
    fun k B => positiveWidthFullCriticalStartRatio (k + 1) B
  let hi : ℕ → ℕ → ℝ :=
    fun k B =>
      positiveWidthFullCriticalStartRatio (k + 1) B +
        survivorResidueStartRatio
          (Critical.criticalTwoDepth (k + 1))
          (criticalTwoDepth_pos (k + 1))
          B
  let loLim : ℕ → ℝ :=
    fun k => positiveWidthFullCriticalStartDensity (k + 1)
  let hiLim : ℕ → ℝ :=
    fun k =>
      positiveWidthFullCriticalStartDensity (k + 1) +
        survivorParityRatio (Critical.criticalTwoDepth (k + 1))
  apply tendsto_of_two_scale_squeeze
      (f := anyFullActualCriticalStartRatio)
      (lo := lo) (hi := hi)
      (loLim := loLim) (hiLim := hiLim)
  · intro k
    exact positiveWidthFullCriticalStartRatio_tendsto (k + 1)
  · intro k
    exact
      (positiveWidthFullCriticalStartRatio_tendsto (k + 1)).add
        (survivorResidueStartRatio_tendsto
          (criticalTwoDepth_pos (k + 1)))
  · intro k B
    simpa [lo, hi] using
      anyFullActualCriticalStartRatio_sandwich
        (k + 1) (Nat.succ_pos k) B
  · exact
      positiveWidthFullCriticalStartDensity_tendsto_half.comp
        (tendsto_add_atTop_nat 1)
  · have h :=
      (positiveWidthFullCriticalStartDensity_tendsto_half.comp
        (tendsto_add_atTop_nat 1)).add
        tendsto_survivorParityRatio_criticalDepth_succ_zero
    simpa [hiLim] using h

end Bridge
end Collatz3
