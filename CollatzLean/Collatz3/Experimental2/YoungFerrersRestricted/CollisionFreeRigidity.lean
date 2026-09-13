import CollatzLean.Collatz3.Experimental2.YoungFerrersRestricted.MultiCollisionPenalty


/-!
# Collatz3 Experimental2: internal collision-free rigidity

internal boundary collision が存在しない場合に何が exact に rigid になるかを切り出す。

重要なのは terminal slack と internal slack を混同しないことである。

* no internal collision
  -> すべての internal diagonal slack = 0
  -> すべての internal basis recurrence が equality case

までは無条件に言える。

一方 terminal slack が0とは限らないので、ここから直ちに basis area equality へは飛ばない。
残り得る defect は terminal 側へ集中する。
-/

namespace Collatz3
namespace Experimental2
namespace YoungFerrersRestricted

/-- internal level に simultaneous width/drop boundary collision が無い。 -/
def NoInternalBoundaryCollision
    (c : WidthDropCode) : Prop :=
  ∀ t : ℕ,
    0 < t →
    t < frobeniusDepth c →
    ¬ (WidthBoundaryAt c t ∧ DropHeightBoundaryAt c t)

/--
no internal collision なら各 internal diagonal slack は0。
-/
theorem internalDiagonalSlack_eq_zero_of_noInternalBoundaryCollision
    (c : WidthDropCode)
    (hPos : PositiveWidthDropCode c)
    (hNo : NoInternalBoundaryCollision c)
    (i : ℕ)
    (hDepth : i + 2 ≤ frobeniusDepth c) :
    internalDiagonalSlack c i = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro hSlack
  have hC :=
    (internalDiagonalSlack_pos_iff_boundaryCollision
      c hPos i hDepth).1 hSlack
  exact hNo (i + 1) (by omega) (by omega) hC

/--
逆に全 internal slack が0なら internal boundary collision は無い。
従って positive width/drop code では両条件は exact に同値。
-/
theorem noInternalBoundaryCollision_iff_all_internalDiagonalSlack_zero
    (c : WidthDropCode)
    (hPos : PositiveWidthDropCode c) :
    NoInternalBoundaryCollision c ↔
      ∀ i : ℕ,
        i + 2 ≤ frobeniusDepth c →
        internalDiagonalSlack c i = 0 := by
  constructor
  · intro hNo i hDepth
    exact
      internalDiagonalSlack_eq_zero_of_noInternalBoundaryCollision
        c hPos hNo i hDepth
  · intro hZero t ht htD hC
    have hDepth : (t - 1) + 2 ≤ frobeniusDepth c := by
      omega
    have htPred : (t - 1) + 1 = t := by omega
    have hC' :
        WidthBoundaryAt c ((t - 1) + 1) ∧
          DropHeightBoundaryAt c ((t - 1) + 1) := by
      simpa [htPred] using hC
    have hSlack : 0 < internalDiagonalSlack c (t - 1) :=
      (internalDiagonalSlack_pos_iff_boundaryCollision
        c hPos (t - 1) hDepth).2 hC'
    have hSlackZero := hZero (t - 1) hDepth
    omega

/--
internal slack が0なら、その段の arm recurrence は二つの equality branch のどちらかに exact に入る。

* arm 側 tight: `a_i = a_{i+1} + 1`
* leg 側 tight: `a_i = a_{i+1} + 1 + s_i - s_{i+1}`
-/
theorem frobeniusArm_tight_of_internalDiagonalSlack_eq_zero
    (c : WidthDropCode)
    (i : ℕ)
    (hDepth : i + 2 ≤ frobeniusDepth c)
    (hZero : internalDiagonalSlack c i = 0) :
    (frobeniusArmAt c i : ℤ) =
        (frobeniusArmAt c (i + 1) : ℤ) + 1 ∨
      (frobeniusArmAt c i : ℤ) =
        (frobeniusArmAt c (i + 1) : ℤ) + 1 +
          frobeniusRankAt c i - frobeniusRankAt c (i + 1) := by
  have hSlack :=
    stepBasisSlack_frobenius_eq_internalDiagonalSlack c i hDepth
  simp only [hZero, Nat.cast_zero] at hSlack
  by_cases hRank :
      frobeniusRankAt c i ≤ frobeniusRankAt c (i + 1)
  · left
    unfold stepBasisSlack at hSlack
    rw [ite_eq_left hRank] at hSlack
    omega
  · right
    unfold stepBasisSlack at hSlack
    rw [ite_eq_right hRank] at hSlack
    omega

/--
no internal collision から各 internal recurrence の exact tightness を直接読む公開 theorem。
-/
theorem frobeniusArm_tight_of_noInternalBoundaryCollision
    (c : WidthDropCode)
    (hPos : PositiveWidthDropCode c)
    (hNo : NoInternalBoundaryCollision c)
    (i : ℕ)
    (hDepth : i + 2 ≤ frobeniusDepth c) :
    (frobeniusArmAt c i : ℤ) =
        (frobeniusArmAt c (i + 1) : ℤ) + 1 ∨
      (frobeniusArmAt c i : ℤ) =
        (frobeniusArmAt c (i + 1) : ℤ) + 1 +
          frobeniusRankAt c i - frobeniusRankAt c (i + 1) := by
  apply frobeniusArm_tight_of_internalDiagonalSlack_eq_zero c i hDepth
  exact
    internalDiagonalSlack_eq_zero_of_noInternalBoundaryCollision
      c hPos hNo i hDepth

/--
no internal collision の global 版。すべての internal段が二択 equality recurrence に入る。
terminal equality は主張しない。
-/
theorem all_frobeniusArms_tight_of_noInternalBoundaryCollision
    (c : WidthDropCode)
    (hPos : PositiveWidthDropCode c)
    (hNo : NoInternalBoundaryCollision c) :
    ∀ i : ℕ,
      i + 2 ≤ frobeniusDepth c →
      ((frobeniusArmAt c i : ℤ) =
          (frobeniusArmAt c (i + 1) : ℤ) + 1 ∨
        (frobeniusArmAt c i : ℤ) =
          (frobeniusArmAt c (i + 1) : ℤ) + 1 +
            frobeniusRankAt c i - frobeniusRankAt c (i + 1)) := by
  intro i hDepth
  exact frobeniusArm_tight_of_noInternalBoundaryCollision
    c hPos hNo i hDepth

end YoungFerrersRestricted

namespace GenericRecordFerrers
namespace RecordFerrers

open YoungFerrersRestricted

/-- canonical RecordFerrers に internal boundary collision が無い。 -/
def NoInternalCanonicalCollision
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m) : Prop :=
  ∀ t : ℕ,
    0 < t →
    t < frobeniusDepth R.plateauWidthDropCode →
    ¬ R.HasCanonicalBoundaryCollision t

/--
canonical no-collision 条件を plateau code の generic no-collision 条件へ移す。
-/
theorem noInternalBoundaryCollision_plateauWidthDropCode
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m)
    (hNo : R.NoInternalCanonicalCollision) :
    NoInternalBoundaryCollision R.plateauWidthDropCode := by
  intro t ht htD hC
  apply hNo t ht htD
  exact (R.hasCanonicalBoundaryCollision_iff t).2 hC

/--
RecordFerrers で internal canonical collision が無ければ全 internal slack は0。
-/
theorem all_internalDiagonalSlack_zero_of_noInternalCanonicalCollision
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m)
    (hNo : R.NoInternalCanonicalCollision) :
    ∀ i : ℕ,
      i + 2 ≤ frobeniusDepth R.plateauWidthDropCode →
      internalDiagonalSlack R.plateauWidthDropCode i = 0 := by
  exact
    (noInternalBoundaryCollision_iff_all_internalDiagonalSlack_zero
      R.plateauWidthDropCode
      R.plateauWidthDropCode_positiveWidthDropCode).1
      (R.noInternalBoundaryCollision_plateauWidthDropCode hNo)

/--
RecordFerrers の collision-free branch で得られる global tight recurrence。

これは basis equality を主張せず、terminal slack を残したまま internal rigidity だけを公開する。
-/
theorem all_frobeniusArms_tight_of_noInternalCanonicalCollision
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m)
    (hNo : R.NoInternalCanonicalCollision) :
    ∀ i : ℕ,
      i + 2 ≤ frobeniusDepth R.plateauWidthDropCode →
      ((frobeniusArmAt R.plateauWidthDropCode i : ℤ) =
          (frobeniusArmAt R.plateauWidthDropCode (i + 1) : ℤ) + 1 ∨
        (frobeniusArmAt R.plateauWidthDropCode i : ℤ) =
          (frobeniusArmAt R.plateauWidthDropCode (i + 1) : ℤ) + 1 +
            frobeniusRankAt R.plateauWidthDropCode i -
              frobeniusRankAt R.plateauWidthDropCode (i + 1)) := by
  intro i hDepth
  exact
    frobeniusArm_tight_of_noInternalBoundaryCollision
      R.plateauWidthDropCode
      R.plateauWidthDropCode_positiveWidthDropCode
      (R.noInternalBoundaryCollision_plateauWidthDropCode hNo)
      i hDepth

end RecordFerrers
end GenericRecordFerrers
end Experimental2
end Collatz3
