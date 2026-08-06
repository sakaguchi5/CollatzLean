import CollatzLean.CollatzSecondLayer3.AlternativeExclusion



/-!
# polynomial prepared refinementの無限分岐

moving first-crossing列の内部に構成された一様多項式小prepared window列を、
persistent captureまたはSpecial C3 refinementへ分ける。
-/

namespace CollatzSecondLayer3

open CollatzSupport
open CollatzCore

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

/-- moving first-crossing内部のpolynomial-small prepared refinement列。 -/
structure PolynomialPreparedRefinementSequence
    {O : OddOrbit} (F : MovingFirstCrossingData O) where
  select : ℕ → ℕ
  select_strict : StrictMono select
  offset : ℕ → ℕ
  length : ℕ → ℕ
  insideCrossing : ∀ j : ℕ,
    offset j + length j ≤ F.crossingLength (select j)
  start_strict : StrictMono
    (fun j => F.minima.index (select j) + offset j)
  packet : ∀ j : ℕ,
    O.PreparedWindowPacket
      (F.minima.index (select j) + offset j)
      (length j)
  K : ℕ
  A : ℕ
  endpointBound : ∀ j : ℕ,
    O.value
        (F.minima.index (select j) + offset j + length j) ≤
      K * (length j + 1) ^ A
  lengths_tend_to_infinity :
    ∀ M : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j → M < length j

namespace PolynomialPreparedRefinementSequence

/-- refinement列を一般のpolynomial prepared window列として忘却する。 -/
def toWindowSequence
    {O : OddOrbit} {F : MovingFirstCrossingData O}
    (R : PolynomialPreparedRefinementSequence F) :
    OddOrbit.PolynomialPreparedWindowSequence O where
  start := fun j => F.minima.index (R.select j) + R.offset j
  length := R.length
  start_strict := R.start_strict
  packet := R.packet
  K := R.K
  A := R.A
  endpointBound := R.endpointBound
  lengths_tend_to_infinity := R.lengths_tend_to_infinity

/-- captureが任意に遠い項で残ること。 -/
def HasPersistentCapture
    {O : OddOrbit} {F : MovingFirstCrossingData O}
    (R : PolynomialPreparedRefinementSequence F) : Prop :=
  ∀ N : ℕ, ∃ j : ℕ,
    N ≤ j ∧
    Nonempty
      (O.CapturedWindowAt
        (F.minima.index (R.select j) + R.offset j)
        (R.length j))

/-- persistent captureでなければ、ある位置以後captureは存在しない。 -/
theorem eventually_no_capture_of_not_persistent
    {O : OddOrbit} {F : MovingFirstCrossingData O}
    (R : PolynomialPreparedRefinementSequence F)
    (h : ¬ R.HasPersistentCapture) :
    ∃ N : ℕ, ∀ j : ℕ, N ≤ j →
      ¬ Nonempty
        (O.CapturedWindowAt
          (F.minima.index (R.select j) + R.offset j)
          (R.length j)) := by
  classical
  unfold HasPersistentCapture at h
  push Not at h
  obtain ⟨N, hN⟩ := h
  refine ⟨N, ?_⟩
  intro j hj hcap
  rcases hcap with ⟨C⟩
  exact (hN j hj).false C
/--
polynomial-small prepared refinementはpersistent captureまたはSpecial C3 refinement。
-/
theorem persistentCapture_or_specialC3
    {O : OddOrbit} {F : MovingFirstCrossingData O}
    (R : PolynomialPreparedRefinementSequence F) :
    R.HasPersistentCapture ∨ HasSpecialC3From F := by
  classical
  by_cases hPersistent : R.HasPersistentCapture
  · exact Or.inl hPersistent
  · right
    obtain ⟨Ncap, hNcap⟩ :=
      R.eventually_no_capture_of_not_persistent hPersistent
    obtain ⟨Nout, hNout⟩ :=
      R.toWindowSequence.eventually_capture_or_specialC3
    let N := max Ncap Nout
    let select' : ℕ → ℕ := fun j => R.select (N + j)
    let offset' : ℕ → ℕ := fun j => R.offset (N + j)
    let length' : ℕ → ℕ := fun j => R.length (N + j)
    have hselect : StrictMono select' := by
      intro a b hab
      exact R.select_strict (Nat.add_lt_add_left hab N)
    have hinside : ∀ j : ℕ,
        offset' j + length' j ≤ F.crossingLength (select' j) := by
      intro j
      exact R.insideCrossing (N + j)
    have hspecial : ∀ j : ℕ,
        SpecialC3At O
          (F.minima.index (select' j) + offset' j)
          (length' j) := by
      intro j
      have hjcap : Ncap ≤ N + j := by
        dsimp [N]
        omega
      have hjout : Nout ≤ N + j := by
        dsimp [N]
        omega
      let outcome :=
        Classical.choice (hNout (N + j) hjout)
      cases outcome with
      | inl hcap =>
          change
            O.CapturedWindowAt
              (F.minima.index (R.select (N + j)) + R.offset (N + j))
              (R.length (N + j))
            at hcap
          exact (hNcap (N + j) hjcap ⟨hcap⟩).elim
      | inr hspecial =>
          change
            SpecialC3At O
              (F.minima.index (R.select (N + j)) + R.offset (N + j))
              (R.length (N + j))
            at hspecial
          exact hspecial
    have htend :
        ∀ M : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j → M < length' j := by
      intro M
      obtain ⟨J, hJ⟩ := R.lengths_tend_to_infinity M
      refine ⟨J, ?_⟩
      intro j hj
      exact hJ (N + j) (by omega)
    exact ⟨{
      select := select'
      select_strict := hselect
      offset := offset'
      length := length'
      insideCrossing := hinside
      special := hspecial
      lengths_tend_to_infinity := htend
    }⟩

end PolynomialPreparedRefinementSequence
end CollatzSecondLayer3
