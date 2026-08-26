import CollatzLean.Collatz2.RecordFerrers.Record.Skeleton

/-!
# Record–Ferrers Phase A: record walls

record birth/death を「変形の種類」ではなく、fixed-chord deformation が
rank equality wall を横切る現象として扱う。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-- anchor `a` から cut `b` への signed rank difference。 -/
def rankGap
    {p H : ℕ}
    (x : FiberPoint p H)
    (a b : ℕ) : ℤ :=
  chordRankInt x.word b - chordRankInt x.word a

/-- cut `b` が anchor rank より上。 -/
def AboveAnchor
    {p H : ℕ}
    (x : FiberPoint p H)
    (a b : ℕ) : Prop :=
  0 < rankGap x a b

/-- cut `b` が anchor rank より下。 -/
def BelowAnchor
    {p H : ℕ}
    (x : FiberPoint p H)
    (a b : ℕ) : Prop :=
  rankGap x a b < 0

/-- rank equality wall。 -/
def OnRecordWall
    {p H : ℕ}
    (x : FiberPoint p H)
    (a b : ℕ) : Prop :=
  rankGap x a b = 0

/-- arbitrary fixed-chord deformation の rank-gap transport。 -/
theorem rankGap_transport
    {p H : ℕ}
    (u v : FiberPoint p H)
    (a b : ℕ) :
    rankGap v a b =
      rankGap u a b -
        (p : ℤ) *
          (profileDisplacement u v b - profileDisplacement u v a) := by
  unfold rankGap
  rw [chordRankInt_transport u v b,
      chordRankInt_transport u v a]
  ring

/-- wall condition は source gap と displacement difference の exact equality。 -/
theorem onRecordWall_iff
    {p H : ℕ}
    (u v : FiberPoint p H)
    (a b : ℕ) :
    OnRecordWall v a b ↔
      rankGap u a b =
        (p : ℤ) *
          (profileDisplacement u v b - profileDisplacement u v a) := by
  unfold OnRecordWall
  rw [rankGap_transport u v a b]
  constructor <;> intro h <;> linarith

/-- source anchor displacement が 0 なら target gap は `-p*s(b)` だけ動く。 -/
theorem rankGap_transport_of_anchor_fixed
    {p H : ℕ}
    (u v : FiberPoint p H)
    (a b : ℕ)
    (hAnchor : profileDisplacement u v a = 0) :
    rankGap v a b =
      rankGap u a b - (p : ℤ) * profileDisplacement u v b := by
  rw [rankGap_transport u v a b, hAnchor]
  ring

/-- fixed anchor の下向き wall crossing criterion。 -/
theorem belowAnchor_iff_of_anchor_fixed
    {p H : ℕ}
    (u v : FiberPoint p H)
    (a b : ℕ)
    (hAnchor : profileDisplacement u v a = 0) :
    BelowAnchor v a b ↔
      rankGap u a b < (p : ℤ) * profileDisplacement u v b := by
  unfold BelowAnchor
  rw [rankGap_transport_of_anchor_fixed u v a b hAnchor]
  constructor <;> intro h <;> linarith

/-- fixed anchor の上向き wall crossing criterion。 -/
theorem aboveAnchor_iff_of_anchor_fixed
    {p H : ℕ}
    (u v : FiberPoint p H)
    (a b : ℕ)
    (hAnchor : profileDisplacement u v a = 0) :
    AboveAnchor v a b ↔
      (p : ℤ) * profileDisplacement u v b < rankGap u a b := by
  unfold AboveAnchor
  rw [rankGap_transport_of_anchor_fixed u v a b hAnchor]
  constructor <;> intro h <;> linarith

/-- RecordBlock interior は rank-gap language で positive。 -/
theorem RecordBlock.aboveAnchor_interior
    {p H : ℕ}
    {x : FiberPoint p H}
    {start len j : ℕ}
    (B : RecordBlock x start len)
    (hjPos : 0 < j)
    (hjLt : j < len) :
    AboveAnchor x start (start + j) := by
  unfold AboveAnchor rankGap
  have h := B.interior_above j hjPos hjLt
  linarith

/-- RecordBlock endpoint は rank-gap language で negative。 -/
theorem RecordBlock.belowAnchor_terminal
    {p H : ℕ}
    {x : FiberPoint p H}
    {start len : ℕ}
    (B : RecordBlock x start len) :
    BelowAnchor x start (start + len) := by
  unfold BelowAnchor rankGap
  have h := B.terminal_below
  linarith

/-- source interior point が target で below に移れば record split wall を横切った。 -/
def SplitWallCrossing
    {p H : ℕ}
    (u v : FiberPoint p H)
    (anchor cut : ℕ) : Prop :=
  AboveAnchor u anchor cut ∧ BelowAnchor v anchor cut

/-- source below point が target で interior above に戻れば record merge wall を横切った。 -/
def MergeWallCrossing
    {p H : ℕ}
    (u v : FiberPoint p H)
    (anchor cut : ℕ) : Prop :=
  BelowAnchor u anchor cut ∧ AboveAnchor v anchor cut

end RecordFerrers
end Collatz2
