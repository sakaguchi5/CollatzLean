import CollatzLean.Collatz3.Experimental2.YoungFerrersRestricted.FrobeniusCoordinates
import Mathlib.Tactic.Ring

/-!
# Collatz3 Experimental2: successive rank vector

Frobenius arm / leg から古典的 successive rank

  rank_i = arm_i - leg_i

を整数列として切り出す。
対角 cell が存在する範囲では、これは同時に

  rowLength_i - columnHeight_i

そのものである。
-/

namespace Collatz3
namespace Experimental2
namespace YoungFerrersRestricted

/-- 第 `i` 対角位置の successive rank。 -/
def frobeniusRankAt
    (c : WidthDropCode)
    (i : ℕ) : ℤ :=
  (frobeniusArmAt c i : ℤ) - (frobeniusLegAt c i : ℤ)

/-- `start` から `n` 個の successive rank を並べる。 -/
def successiveRankVectorFrom
    (c : WidthDropCode) : ℕ → ℕ → List ℤ
  | _start, 0 => []
  | start, n + 1 =>
      frobeniusRankAt c start ::
        successiveRankVectorFrom c (start + 1) n

/-- Young 図形の genuine successive rank vector。 -/
def successiveRankVector
    (c : WidthDropCode) : List ℤ :=
  successiveRankVectorFrom c 0 (frobeniusDepth c)

/-- arm を整数列へ持ち上げる。後段の basis recurrence は `ℤ` 上で扱う。 -/
def frobeniusArmsZFrom
    (c : WidthDropCode) : ℕ → ℕ → List ℤ
  | _start, 0 => []
  | start, n + 1 =>
      (frobeniusArmAt c start : ℤ) ::
        frobeniusArmsZFrom c (start + 1) n

/-- leg を整数列へ持ち上げる。 -/
def frobeniusLegsZFrom
    (c : WidthDropCode) : ℕ → ℕ → List ℤ
  | _start, 0 => []
  | start, n + 1 =>
      (frobeniusLegAt c start : ℤ) ::
        frobeniusLegsZFrom c (start + 1) n

/-- 全 arm の整数版。 -/
def frobeniusArmsZ (c : WidthDropCode) : List ℤ :=
  frobeniusArmsZFrom c 0 (frobeniusDepth c)

/-- 全 leg の整数版。 -/
def frobeniusLegsZ (c : WidthDropCode) : List ℤ :=
  frobeniusLegsZFrom c 0 (frobeniusDepth c)

@[simp] theorem successiveRankVectorFrom_length
    (c : WidthDropCode) :
    ∀ start n,
      (successiveRankVectorFrom c start n).length = n
  | _start, 0 => rfl
  | start, n + 1 => by
      simp [successiveRankVectorFrom,
        successiveRankVectorFrom_length c (start + 1) n]

@[simp] theorem frobeniusArmsZFrom_length
    (c : WidthDropCode) :
    ∀ start n,
      (frobeniusArmsZFrom c start n).length = n
  | _start, 0 => rfl
  | start, n + 1 => by
      simp [frobeniusArmsZFrom,
        frobeniusArmsZFrom_length c (start + 1) n]

@[simp] theorem frobeniusLegsZFrom_length
    (c : WidthDropCode) :
    ∀ start n,
      (frobeniusLegsZFrom c start n).length = n
  | _start, 0 => rfl
  | start, n + 1 => by
      simp [frobeniusLegsZFrom,
        frobeniusLegsZFrom_length c (start + 1) n]

@[simp] theorem successiveRankVector_length
    (c : WidthDropCode) :
    (successiveRankVector c).length = frobeniusDepth c := by
  simp [successiveRankVector]

@[simp] theorem frobeniusArmsZ_length
    (c : WidthDropCode) :
    (frobeniusArmsZ c).length = frobeniusDepth c := by
  simp [frobeniusArmsZ]

@[simp] theorem frobeniusLegsZ_length
    (c : WidthDropCode) :
    (frobeniusLegsZ c).length = frobeniusDepth c := by
  simp [frobeniusLegsZ]

/--
対角 cell が存在する位置では successive rank は
`row length - column height` と exact に一致する。
-/
theorem frobeniusRankAt_eq_row_sub_column
    (c : WidthDropCode)
    {i : ℕ}
    (hi : i < frobeniusDepth c) :
    frobeniusRankAt c i =
      (frobeniusRowLength c i : ℤ) -
        (frobeniusColumnHeight c i : ℤ) := by
  have hrow : i + 1 ≤ frobeniusRowLength c i := by
    exact Nat.succ_le_iff.mpr (frobeniusRow_diagonal c hi)
  have hcol : i + 1 ≤ frobeniusColumnHeight c i := by
    exact Nat.succ_le_iff.mpr (frobeniusColumn_diagonal c hi)
  unfold frobeniusRankAt frobeniusArmAt frobeniusLegAt
  rw [Nat.cast_sub hrow, Nat.cast_sub hcol]
  push_cast
  ring

/-- successive rank vector は arm-leg の componentwise 差として構成される。 -/
theorem successiveRankVectorFrom_eq_zipWith
    (c : WidthDropCode) :
    ∀ start n,
      successiveRankVectorFrom c start n =
        List.zipWith (fun a b : ℤ => a - b)
          (frobeniusArmsZFrom c start n)
          (frobeniusLegsZFrom c start n)
  | _start, 0 => rfl
  | start, n + 1 => by
      simp [successiveRankVectorFrom,
        frobeniusArmsZFrom, frobeniusLegsZFrom,
        frobeniusRankAt,
        successiveRankVectorFrom_eq_zipWith c (start + 1) n]

end YoungFerrersRestricted

namespace GenericRecordFerrers
namespace RecordFerrers

open YoungFerrersRestricted

/-- RecordFerrers rank-envelope の successive rank vector。 -/
def successiveRanks
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m) : List ℤ :=
  successiveRankVector R.plateauWidthDropCode

@[simp] theorem successiveRanks_length
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m) :
    R.successiveRanks.length = R.rankDurfeeSize := by
  unfold successiveRanks
  rw [successiveRankVector_length]
  exact R.rankDurfeeSize_eq_frobeniusDepth.symm

end RecordFerrers
end GenericRecordFerrers
end Experimental2
end Collatz3
