import CollatzLean.Collatz2.Canonical.Representative
import CollatzLean.Collatz2.Orbit.Runs

/-!
# Collatz2: replay coordinates derived from canonical residue geometry

ReplayCoordinate を primitive な branch data として置かない。
odd-endpoint realization の start が canonical representative と同じ residue class に属することから、
その自然数 quotient を一意な replay layer として読み取る。

`q = 0` はこの座標の最下層であり、次ファイルで contracting replay の extremal layer として導く。
-/

namespace Collatz2
namespace Word

/--
一つの affine realization を odd-endpoint residue modulus の自然数倍だけ上へ replay する。
-/
theorem Realizes.replay
    {w : Word} {x y : ℕ}
    (h : Realizes w x y)
    (q : ℕ) :
    Realizes w
      (x + residueModulus w * q)
      (y + 2 * 3 ^ oddSteps w * q) := by
  apply (realizes_iff w _ _).2
  have hEq := (realizes_iff w x y).1 h
  unfold residueModulus
  rw [pow_succ]
  calc
    2 ^ twoSteps w * (y + 2 * 3 ^ oddSteps w * q)
        =
        2 ^ twoSteps w * y +
          3 ^ oddSteps w * ((2 ^ twoSteps w * 2) * q) := by ring
    _ =
        (3 ^ oddSteps w * x + affineConst w) +
          3 ^ oddSteps w * ((2 ^ twoSteps w * 2) * q) := by rw [hEq]
    _ =
        3 ^ oddSteps w * (x + (2 ^ twoSteps w * 2) * q) +
          affineConst w := by ring

/-- 任意の odd-endpoint realization を canonical layer からの quotient で座標化する。 -/
structure ReplayCoordinate (w : Word) (X Y : ℕ) where
  quotient : ℕ
  start_eq : X = canonicalStart w + residueModulus w * quotient
  finish_eq : Y = canonicalEnd w + 2 * 3 ^ oddSteps w * quotient

namespace ReplayCoordinate

/-- odd-endpoint affine realization から replay coordinate を構成する。 -/
def ofRealization
    {w : Word} {X Y : ℕ}
    (h : Realizes w X Y)
    (hY : Odd Y) :
    ReplayCoordinate w X Y := by
  let q := X / residueModulus w
  have hmod : X % residueModulus w = canonicalStart w :=
    h.start_mod_eq_canonicalStart hY
  have hdecomp := Nat.mod_add_div X (residueModulus w)
  rw [hmod] at hdecomp
  have hstart :
      X = canonicalStart w + residueModulus w * q := by
    dsimp [q]
    simpa [Nat.mul_comm] using hdecomp.symm
  have hreplay :
      Realizes w
        (canonicalStart w + residueModulus w * q)
        (canonicalEnd w + 2 * 3 ^ oddSteps w * q) := by
    exact (canonicalEnd_realizes w).replay q
  have hEq := (realizes_iff w X Y).1 h
  have hReplayEq :=
    (realizes_iff w
      (canonicalStart w + residueModulus w * q)
      (canonicalEnd w + 2 * 3 ^ oddSteps w * q)).1 hreplay
  have hfinish :
      Y = canonicalEnd w + 2 * 3 ^ oddSteps w * q := by
    have hsame :
        2 ^ twoSteps w * Y =
          2 ^ twoSteps w *
            (canonicalEnd w + 2 * 3 ^ oddSteps w * q) := by
      calc
        2 ^ twoSteps w * Y
            = 3 ^ oddSteps w * X + affineConst w := hEq
        _ =
            3 ^ oddSteps w *
              (canonicalStart w + residueModulus w * q) + affineConst w := by
                rw [hstart]
        _ =
            2 ^ twoSteps w *
              (canonicalEnd w + 2 * 3 ^ oddSteps w * q) := hReplayEq.symm
    exact Nat.mul_left_cancel (Nat.pow_pos (by omega : 0 < (2 : ℕ))) hsame
  exact ⟨q, hstart, hfinish⟩

/--
非空 normalized odd-only run は endpoint odd を自身で保持するので、
追加の odd 仮定なしで replay coordinate を持つ。
-/
def ofRuns
    {w : Word} {X Y : ℕ}
    (h : Runs w X Y)
    (hne : w ≠ []) :
    ReplayCoordinate w X Y :=
  ofRealization h.realizes (h.end_odd_of_ne_nil hne)

/-- replay coordinate が表す start/end は実際に同じ word を affine realization する。 -/
theorem realizes
    {w : Word} {X Y : ℕ}
    (C : ReplayCoordinate w X Y) :
    Realizes w X Y := by
  let q : ℕ := C.quotient
  have hX :
      X = w.canonicalStart + w.residueModulus * q := by
    simpa [q] using C.start_eq
  have hY :
      Y =
        w.canonicalEnd +
          2 * 3 ^ w.oddSteps * q := by
    simpa [q] using C.finish_eq
  rw [hX, hY]
  exact (canonicalEnd_realizes w).replay q

/-- quotient が0なら start は canonical representative。 -/
theorem start_eq_canonical_of_quotient_eq_zero
    {w : Word} {X Y : ℕ}
    (C : ReplayCoordinate w X Y)
    (hzero : C.quotient = 0) :
    X = canonicalStart w := by
  rw [C.start_eq, hzero]
  simp

/-- start が canonical representative なら quotient は0。 -/
theorem quotient_eq_zero_of_start_eq_canonical
    {w : Word} {X Y : ℕ}
    (C : ReplayCoordinate w X Y)
    (hstart : X = canonicalStart w) :
    C.quotient = 0 := by
  have hsum :
      canonicalStart w =
        canonicalStart w + residueModulus w * C.quotient := by
    calc
      canonicalStart w = X := hstart.symm
      _ = canonicalStart w + residueModulus w * C.quotient := C.start_eq
  have hmul : residueModulus w * C.quotient = 0 := by omega
  have hmodPos : 0 < residueModulus w := residueModulus_pos w
  by_contra hq
  have hqPos : 0 < C.quotient := Nat.pos_of_ne_zero hq
  have : 0 < residueModulus w * C.quotient := Nat.mul_pos hmodPos hqPos
  omega

/-- `q = 0` と canonical start は exact に同値。 -/
theorem quotient_eq_zero_iff_start_eq_canonical
    {w : Word} {X Y : ℕ}
    (C : ReplayCoordinate w X Y) :
    C.quotient = 0 ↔ X = canonicalStart w := by
  constructor
  · exact C.start_eq_canonical_of_quotient_eq_zero
  · exact C.quotient_eq_zero_of_start_eq_canonical

/-- quotient が0なら endpoint も canonical endpoint。 -/
theorem finish_eq_canonical_of_quotient_eq_zero
    {w : Word} {X Y : ℕ}
    (C : ReplayCoordinate w X Y)
    (hzero : C.quotient = 0) :
    Y = canonicalEnd w := by
  rw [C.finish_eq, hzero]
  simp

end ReplayCoordinate
end Word
end Collatz2
