import CollatzLean.CollatzFirstLayer.DownwardReplay

/-!
# canonical replay座標の一段下降

一段lower runを取るとcanonical quotientが正確に1減る。
-/

namespace CollatzFirstLayer

open ExpWord

namespace ExpWord.CanonicalReplayCoordinate

/--
一段lower runにもcanonical replay座標を付ける。
そのquotientは元のquotientからexactに1減る。
-/
noncomputable def lowerRunReplayCoordinate
    {w : ExpWord} {X Y : ℕ}
    (C : CanonicalReplayCoordinate w X Y)
    (L : LowerNaturalRunReplayData w X Y)
    (hpos : 0 < C.quotient) :
    CanonicalReplayCoordinate w L.lowerStart L.lowerFinish := by
  let q := C.quotient - 1
  have hq : C.quotient = q + 1 := by
    dsimp [q]
    omega
  refine
    { quotient := q
      start_eq := ?_
      finish_eq := ?_ }
  · have hsum :
        canonicalStart w + residueModulus w * q + residueModulus w =
          L.lowerStart + residueModulus w := by
      calc
        canonicalStart w + residueModulus w * q + residueModulus w
            = canonicalStart w + residueModulus w * (q + 1) := by
                ring
        _ = canonicalStart w +
              residueModulus w * C.quotient := by
                rw [hq]
        _ = X := C.start_eq.symm
        _ = L.lowerStart + residueModulus w := L.start_step
    exact (Nat.add_right_cancel hsum).symm
  · let width := 2 * 3 ^ oddSteps w
    have hsum :
        canonicalEnd w + width * q + width =
          L.lowerFinish + width := by
      calc
        canonicalEnd w + width * q + width
            = canonicalEnd w + width * (q + 1) := by
                ring
        _ = canonicalEnd w + width * C.quotient := by
                rw [hq]
        _ = Y := by
                simpa [width] using C.finish_eq.symm
        _ = L.lowerFinish + width := by
                simpa [width] using L.finish_step
    exact (Nat.add_right_cancel hsum).symm

@[simp] theorem lowerRunReplayCoordinate_quotient
    {w : ExpWord} {X Y : ℕ}
    (C : CanonicalReplayCoordinate w X Y)
    (L : LowerNaturalRunReplayData w X Y)
    (hpos : 0 < C.quotient) :
    (lowerRunReplayCoordinate C L hpos).quotient =
      C.quotient - 1 := by
  rfl

/-- canonicalに選んだ一段lower runへ適用する短縮版。 -/
noncomputable def lowerNaturalRunReplayCoordinate
    {w : ExpWord} {X Y : ℕ}
    (C : CanonicalReplayCoordinate w X Y)
    (hRun : Runs w X Y)
    (hpos : 0 < C.quotient) :
    CanonicalReplayCoordinate w
      (C.lowerNaturalRunReplay hRun hpos).lowerStart
      (C.lowerNaturalRunReplay hRun hpos).lowerFinish :=
  lowerRunReplayCoordinate C (C.lowerNaturalRunReplay hRun hpos) hpos

@[simp] theorem lowerNaturalRunReplayCoordinate_quotient
    {w : ExpWord} {X Y : ℕ}
    (C : CanonicalReplayCoordinate w X Y)
    (hRun : Runs w X Y)
    (hpos : 0 < C.quotient) :
    (lowerNaturalRunReplayCoordinate C hRun hpos).quotient =
      C.quotient - 1 := by
  rfl

end ExpWord.CanonicalReplayCoordinate

end CollatzFirstLayer
