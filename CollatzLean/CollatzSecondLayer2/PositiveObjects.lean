import CollatzLean.CollatzSecondLayer2.PositivePreparation
import CollatzLean.CollatzSecondLayer2.ExcursionCertificate
import CollatzLean.CollatzSecondLayer2.WeakPlateauCertificate


/-!
# 正の最終三対象

補集合をフィールドに持たず、それぞれ単独で研究・排除できる数学対象を定義する。
-/

namespace CollatzSecondLayer2

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

/-- fixed future-minimum tail上のone-sided meander。 -/
abbrev AnchoredOneSidedMeanderData := OneSidedMeanderData

/-- anchored one-sided meanderが存在すること。 -/
abbrev HasAnchoredOneSidedMeander := HasOneSidedMeander

/-- polynomial-small zero-sync Special C3 tower。 -/
structure PolynomialSpecialC3TowerData (O : OddOrbit) where
  crossing : MovingFirstCrossingData O
  select : ℕ → ℕ
  select_strict : StrictMono select
  offset : ℕ → ℕ
  special : ∀ j : ℕ,
    SpecialC3At O
      (crossing.minima.index (select j) + offset j)
      (crossing.crossingLength (select j))
  K : ℕ
  A : ℕ
  endpointBound : ∀ j : ℕ,
    O.value
        (crossing.minima.index (select j) + offset j +
          crossing.crossingLength (select j)) ≤
      K * (crossing.crossingLength (select j) + 1) ^ A
  lengths_tend_to_infinity :
    ∀ M : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      M < crossing.crossingLength (select j)

/-- persistent captureと同じfirst-crossing項に付随するcritical expansion tower。 -/
structure CaptureGeneratedCriticalExpansionTowerData (O : OddOrbit) where
  crossing : MovingFirstCrossingData O
  select : ℕ → ℕ
  select_strict : StrictMono select
  preparedOffset : ℕ → ℕ
  captured : ∀ j : ℕ,
    O.CapturedWindowAt
      (crossing.minima.index (select j) + preparedOffset j)
      (crossing.crossingLength (select j))
  excursion : ∀ j : ℕ,
    LargeExcursionCertificate O
      (crossing.minima.index (select j))
      (crossing.crossingLength (select j))
  lengths_tend_to_infinity :
    ∀ M : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      M < (excursion j).blockLength

/-- 指定軌道上のpolynomial Special C3 tower。 -/
def HasPolynomialSpecialC3TowerOn (O : OddOrbit) : Prop :=
  Nonempty (PolynomialSpecialC3TowerData O)

/-- 非有界軌道上のpolynomial Special C3 tower。 -/
def HasPolynomialSpecialC3Tower : Prop :=
  ∃ O : OddOrbit, O.Unbounded ∧ HasPolynomialSpecialC3TowerOn O

/-- 指定軌道上のcapture-generated critical expansion tower。 -/
def HasCaptureGeneratedCriticalExpansionTowerOn (O : OddOrbit) : Prop :=
  Nonempty (CaptureGeneratedCriticalExpansionTowerData O)

/-- 非有界軌道上のcapture-generated critical expansion tower。 -/
def HasCaptureGeneratedCriticalExpansionTower : Prop :=
  ∃ O : OddOrbit,
    O.Unbounded ∧ HasCaptureGeneratedCriticalExpansionTowerOn O

namespace PolynomialPreparedFullWindowFamily

/-- captureが任意に遠いfamily項で現れること。 -/
def HasPersistentCapture
    {O : OddOrbit} {F : MovingFirstCrossingData O}
    (P : PolynomialPreparedFullWindowFamily F) : Prop :=
  ∀ N : ℕ, ∃ j : ℕ,
    N ≤ j ∧
    Nonempty
      (O.CapturedWindowAt (P.start j) (F.crossingLength j))

/-- persistent captureでなければ十分後にcaptureは存在しない。 -/
theorem eventually_no_capture_of_not_persistent
    {O : OddOrbit} {F : MovingFirstCrossingData O}
    (P : PolynomialPreparedFullWindowFamily F)
    (h : ¬ P.HasPersistentCapture) :
    ∃ N : ℕ, ∀ j : ℕ, N ≤ j →
      ¬ Nonempty
        (O.CapturedWindowAt (P.start j) (F.crossingLength j)) := by
  classical
  unfold HasPersistentCapture at h
  push Not at h
  obtain ⟨N, hN⟩ := h
  refine ⟨N, ?_⟩
  intro j hj hcap
  rcases hcap with ⟨C⟩
  exact (hN j hj).false C

/-- persistent captureの位置を狭義単調に選ぶ。 -/
noncomputable def persistentCaptureSelect
    {O : OddOrbit} {F : MovingFirstCrossingData O}
    (P : PolynomialPreparedFullWindowFamily F)
    (h : P.HasPersistentCapture) : ℕ → ℕ
  | 0 => Classical.choose (h 0)
  | n + 1 =>
      Classical.choose (h (persistentCaptureSelect P h n + 1))

/-- 選択位置は要求した下限以上。 -/
theorem persistentCaptureSelect_ge
    {O : OddOrbit} {F : MovingFirstCrossingData O}
    (P : PolynomialPreparedFullWindowFamily F)
    (h : P.HasPersistentCapture) :
    ∀ n : ℕ,
      n ≤ P.persistentCaptureSelect h n := by
  intro n
  induction n with
  | zero => omega
  | succ n ih =>
      have hs := Classical.choose_spec
        (h (P.persistentCaptureSelect h n + 1))
      have hstep :
          P.persistentCaptureSelect h n + 1 ≤
            P.persistentCaptureSelect h (n + 1) := by
        simpa [persistentCaptureSelect] using hs.1
      omega

/-- capture選択列は狭義単調。 -/
theorem persistentCaptureSelect_strict
    {O : OddOrbit} {F : MovingFirstCrossingData O}
    (P : PolynomialPreparedFullWindowFamily F)
    (h : P.HasPersistentCapture) :
    StrictMono (P.persistentCaptureSelect h) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hs := Classical.choose_spec
    (h (P.persistentCaptureSelect h n + 1))
  have hle :
      P.persistentCaptureSelect h n + 1 ≤
        P.persistentCaptureSelect h (n + 1) := by
    simpa [persistentCaptureSelect] using hs.1
  omega

/-- 選択した各項はcapture。 -/
theorem persistentCaptureSelect_captured
    {O : OddOrbit} {F : MovingFirstCrossingData O}
    (P : PolynomialPreparedFullWindowFamily F)
    (h : P.HasPersistentCapture)
    (n : ℕ) :
    Nonempty
      (O.CapturedWindowAt
        (P.start (P.persistentCaptureSelect h n))
        (F.crossingLength (P.persistentCaptureSelect h n))) := by
  cases n with
  | zero =>
      simpa [persistentCaptureSelect] using
        (Classical.choose_spec (h 0)).2
  | succ n =>
      simpa [persistentCaptureSelect] using
        (Classical.choose_spec
          (h (P.persistentCaptureSelect h n + 1))).2

/-- persistent captureからcritical expansion towerを構成する。 -/
noncomputable def toCriticalExpansionTower
    {O : OddOrbit} {F : MovingFirstCrossingData O}
    (P : PolynomialPreparedFullWindowFamily F)
    (h : P.HasPersistentCapture) :
    CaptureGeneratedCriticalExpansionTowerData O := by
  classical
  let hexJ := F.lengths_tend_to_infinity 1
  let J₁ := Classical.choose hexJ
  have hJ₁ := Classical.choose_spec hexJ
  let raw := P.persistentCaptureSelect h
  let select : ℕ → ℕ := fun j => raw (J₁ + j)
  have hselect : StrictMono select := by
    intro a b hab
    exact P.persistentCaptureSelect_strict h
      (Nat.add_lt_add_left hab J₁)
  have hpgt : ∀ j : ℕ, 1 < F.crossingLength (select j) := by
    intro j
    apply hJ₁
    have hge : J₁ + j ≤ raw (J₁ + j) :=
      P.persistentCaptureSelect_ge h (J₁ + j)
    calc
      J₁ ≤ J₁ + j := Nat.le_add_right J₁ j
      _ ≤ select j := by
        simpa [select] using hge
  refine
    { crossing := F
      select := select
      select_strict := hselect
      preparedOffset := fun j => P.offset (select j)
      captured := ?_
      excursion := ?_
      lengths_tend_to_infinity := ?_ }
  · intro j
    let C := Classical.choice
      (P.persistentCaptureSelect_captured h (J₁ + j))
    simpa [select, raw, PolynomialPreparedFullWindowFamily.start] using C
  · intro j
    exact LargeExcursionCertificate.ofFirstCrossing
      (F.crossing (select j)) (hpgt j)
  · intro M
    obtain ⟨J, hJ⟩ :=
      F.lengths_tend_to_infinity (M + 1)
    refine ⟨max J J₁, ?_⟩
    intro j hj
    have hselge : J ≤ select j := by
      have hraw :=
        P.persistentCaptureSelect_ge h (J₁ + j)
      dsimp [select, raw]
      omega
    have hlen :
        M + 1 < F.crossingLength (select j) :=
      hJ (select j) hselge
    change M < F.crossingLength (select j) - 1
    omega
/--
標準prepared familyは、persistent captureまたはpolynomial Special C3 tower。
-/
theorem persistentCapture_or_polynomialSpecialC3
    {O : OddOrbit} {F : MovingFirstCrossingData O}
    (P : PolynomialPreparedFullWindowFamily F)
    (hPow : PolynomialBelowTwoPower) :
    P.HasPersistentCapture ∨
      Nonempty (PolynomialSpecialC3TowerData O) := by
  classical
  by_cases hPersistent : P.HasPersistentCapture
  · exact Or.inl hPersistent
  · right
    obtain ⟨Ncap, hNcap⟩ :=
      P.eventually_no_capture_of_not_persistent hPersistent
    obtain ⟨Nout, hNout⟩ := P.eventually_capture_or_specialC3 hPow
    let N := max Ncap Nout
    let select : ℕ → ℕ := fun j => N + j
    have hselect : StrictMono select := by
      intro a b hab
      exact Nat.add_lt_add_left hab N
    have hspecial : ∀ j : ℕ,
        SpecialC3At O
          (F.minima.index (select j) + P.offset (select j))
          (F.crossingLength (select j)) := by
      intro j
      have hjcap : Ncap ≤ select j := by
        dsimp [N, select]
        omega
      have hjout : Nout ≤ select j := by
        dsimp [N, select]
        omega
      let outcome := Classical.choice (hNout (select j) hjout)
      cases outcome with
      | inl C =>
          exact False.elim (hNcap (select j) hjcap ⟨C⟩)
      | inr S => exact S
    refine ⟨{
      crossing := F
      select := select
      select_strict := hselect
      offset := fun j => P.offset (select j)
      special := hspecial
      K := P.K
      A := P.A
      endpointBound := ?_
      lengths_tend_to_infinity := ?_
    }⟩
    · intro j
      exact P.endpointBound (select j)
    · intro M
      obtain ⟨J, hJ⟩ := F.lengths_tend_to_infinity M
      refine ⟨J, ?_⟩
      intro j hj
      exact hJ (select j) (by
        dsimp [select]
        omega)

end PolynomialPreparedFullWindowFamily
end CollatzSecondLayer2
