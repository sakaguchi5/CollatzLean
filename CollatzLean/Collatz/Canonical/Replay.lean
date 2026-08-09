import CollatzLean.Collatz.Canonical.Residue
import CollatzLean.Collatz.FiniteOrbit.Comparison
import CollatzLean.Collatz.Word.Replay

/-!
# canonical replay座標

canonical開始値に対応する奇数終点を構成し、任意の奇数終点実現を
canonical代表からのreplay回数で一意に座標化する。
negative-shadow固有の構造はここへ戻さない。
-/

namespace Collatz
namespace Word

/-- canonical開始値を法へ戻すとcanonical剰余類になる。 -/
theorem canonicalStart_cast (w : Collatz.Word) :
    ((w.canonicalStart : ℕ) : ZMod w.residueModulus) = w.canonicalClass := by
  haveI : NeZero w.residueModulus := ⟨by simp [residueModulus]⟩
  exact ZMod.natCast_zmod_val w.canonicalClass

/-- 奇数終点を持つ実現の開始値はcanonical開始値と同じ剰余を持つ。 -/
theorem Realizes.start_mod_eq_canonicalStart
    {w : Collatz.Word} {x y : ℕ}
    (h : w.Realizes x y) (hy : Odd y) :
    x % w.residueModulus = w.canonicalStart := by
  have hc := h.start_has_canonical_class hy
  have hv := congrArg ZMod.val hc
  simpa [canonicalStart, ZMod.val_natCast] using hv

/-- canonical開始値を代入したaffine式の分子。 -/
def canonicalNumerator (w : Collatz.Word) : ℕ :=
  3 ^ w.oddSteps * w.canonicalStart + w.affineConst

/-- canonical分子は`2^H`を法`2^(H+1)`で持つ。 -/
theorem canonicalNumerator_mod_residueModulus (w : Collatz.Word) :
    w.canonicalNumerator % w.residueModulus = 2 ^ w.twoSteps := by
  haveI : NeZero w.residueModulus := ⟨by simp [residueModulus]⟩
  have hcast :
      ((w.canonicalNumerator : ℕ) : ZMod w.residueModulus) =
        ((2 ^ w.twoSteps : ℕ) : ZMod w.residueModulus) := by
    calc
      ((w.canonicalNumerator : ℕ) : ZMod w.residueModulus)
          = (((3 ^ w.oddSteps : ℕ) : ZMod w.residueModulus) *
              ((w.canonicalStart : ℕ) : ZMod w.residueModulus)) +
            ((w.affineConst : ℕ) : ZMod w.residueModulus) := by
              simp [canonicalNumerator]
      _ = (((3 ^ w.oddSteps : ℕ) : ZMod w.residueModulus) *
              w.canonicalClass) +
            ((w.affineConst : ℕ) : ZMod w.residueModulus) := by
              rw [w.canonicalStart_cast]
      _ = ((2 ^ w.twoSteps : ℕ) : ZMod w.residueModulus) := w.canonicalClass_spec
  have hval := congrArg ZMod.val hcast
  have hpowlt : 2 ^ w.twoSteps < w.residueModulus := by
    unfold residueModulus
    exact Nat.pow_lt_pow_right (by omega) (Nat.lt_succ_self _)
  calc
    w.canonicalNumerator % w.residueModulus
        = (((w.canonicalNumerator : ℕ) : ZMod w.residueModulus)).val := by
            simp only [ZMod.val_natCast]
    _ = (((2 ^ w.twoSteps : ℕ) : ZMod w.residueModulus)).val := hval
    _ = (2 ^ w.twoSteps) % w.residueModulus := by simp only [ZMod.val_natCast]
    _ = 2 ^ w.twoSteps := Nat.mod_eq_of_lt hpowlt

/-- canonical開始値に対応する正の奇数終点。 -/
def canonicalEnd (w : Collatz.Word) : ℕ :=
  2 * (w.canonicalNumerator / w.residueModulus) + 1

/-- canonical開始値とcanonical終点はaffine実現式を満たす。 -/
theorem canonicalEnd_realizes (w : Collatz.Word) :
    w.Realizes w.canonicalStart w.canonicalEnd := by
  unfold Realizes
  change 2 ^ w.twoSteps * w.canonicalEnd = w.canonicalNumerator
  have hdiv := Nat.mod_add_div w.canonicalNumerator w.residueModulus
  rw [w.canonicalNumerator_mod_residueModulus] at hdiv
  calc
    2 ^ w.twoSteps * w.canonicalEnd
        = 2 ^ w.twoSteps +
            w.residueModulus * (w.canonicalNumerator / w.residueModulus) := by
              unfold canonicalEnd residueModulus
              rw [pow_succ]
              ring
    _ = w.canonicalNumerator := by
      simpa [Nat.mul_comm] using hdiv

/-- canonical終点は奇数。 -/
theorem canonicalEnd_odd (w : Collatz.Word) : Odd w.canonicalEnd := by
  refine ⟨w.canonicalNumerator / w.residueModulus, ?_⟩
  unfold canonicalEnd
  omega

/-- canonical終点は正。 -/
theorem canonicalEnd_pos (w : Collatz.Word) : 0 < w.canonicalEnd := by
  unfold canonicalEnd
  omega

/-- 任意の自然数実現をcanonical代表からのreplay回数で表す座標。 -/
structure ReplayCoordinate (w : Collatz.Word) (X Y : ℕ) where
  quotient : ℕ
  start_eq : X = w.canonicalStart + w.residueModulus * quotient
  finish_eq : Y = w.canonicalEnd + 2 * 3 ^ w.oddSteps * quotient

namespace ReplayCoordinate

/-- 奇数終点を持つ自然数実現からcanonical replay座標を構成する。 -/
def ofRealization
    {w : Collatz.Word} {X Y : ℕ}
    (h : w.Realizes X Y) (hY : Odd Y) :
    ReplayCoordinate w X Y := by
  let q := X / w.residueModulus
  have hmod : X % w.residueModulus = w.canonicalStart :=
    h.start_mod_eq_canonicalStart hY
  have hdecomp := Nat.mod_add_div X w.residueModulus
  rw [hmod] at hdecomp
  have hstart : X = w.canonicalStart + w.residueModulus * q := by
    dsimp [q]
    simpa [Nat.mul_comm] using hdecomp.symm
  have hreplay :
      w.Realizes
        (w.canonicalStart + w.residueModulus * q)
        (w.canonicalEnd + 2 * 3 ^ w.oddSteps * q) := by
    simpa [residueModulus] using (canonicalEnd_realizes w).replay (k := q)
  have hfinish : Y = w.canonicalEnd + 2 * 3 ^ w.oddSteps * q := by
    have hsame :
        2 ^ w.twoSteps * Y =
          2 ^ w.twoSteps * (w.canonicalEnd + 2 * 3 ^ w.oddSteps * q) := by
      calc
        2 ^ w.twoSteps * Y = 3 ^ w.oddSteps * X + w.affineConst := h
        _ = 3 ^ w.oddSteps *
              (w.canonicalStart + w.residueModulus * q) + w.affineConst := by rw [hstart]
        _ = 2 ^ w.twoSteps *
              (w.canonicalEnd + 2 * 3 ^ w.oddSteps * q) := hreplay.symm
    exact Nat.mul_left_cancel (Nat.pow_pos (by omega : 0 < (2 : ℕ))) hsame
  exact ⟨q, hstart, hfinish⟩

/-- 非空actual runからcanonical replay座標を構成する。 -/
def ofRuns
    {w : Collatz.Word} {X Y : ℕ}
    (h : Runs w X Y) (hne : w ≠ []) : ReplayCoordinate w X Y :=
  ofRealization h.realizes (h.end_odd_of_ne_nil hne)

/-- quotientが0なら開始値はcanonical代表。 -/
theorem start_eq_canonical_of_quotient_eq_zero
    {w : Collatz.Word} {X Y : ℕ}
    (C : ReplayCoordinate w X Y) (hzero : C.quotient = 0) :
    X = w.canonicalStart := by
  rw [C.start_eq, hzero]
  simp

/-- 開始値がcanonical代表ならquotientは0。 -/
theorem quotient_eq_zero_of_start_eq_canonical
    {w : Collatz.Word} {X Y : ℕ}
    (C : ReplayCoordinate w X Y) (hstart : X = w.canonicalStart) :
    C.quotient = 0 := by
  have hsum :
      w.canonicalStart = w.canonicalStart + w.residueModulus * C.quotient := by
    calc
      w.canonicalStart = X := hstart.symm
      _ = w.canonicalStart + w.residueModulus * C.quotient := C.start_eq
  have hmul : w.residueModulus * C.quotient = 0 := by omega
  by_contra hq
  have hqpos : 0 < C.quotient := Nat.pos_of_ne_zero hq
  have hmodPos : 0 < w.residueModulus := Nat.pow_pos (by omega)
  have hpositive : 0 < w.residueModulus * C.quotient :=
    Nat.mul_pos hmodPos hqpos
  omega

/-- replay quotientが0であることとcanonical開始値であることは同値。 -/
theorem quotient_eq_zero_iff_start_eq_canonical
    {w : Collatz.Word} {X Y : ℕ}
    (C : ReplayCoordinate w X Y) :
    C.quotient = 0 ↔ X = w.canonicalStart := by
  constructor
  · exact C.start_eq_canonical_of_quotient_eq_zero
  · exact C.quotient_eq_zero_of_start_eq_canonical

end ReplayCoordinate

/-- 一つ下の自然数合同代表へ降ろしたaffine replayデータ。 -/
structure LowerNaturalReplayData
    (w : Collatz.Word) (X Y : ℕ) where
  lowerStart : ℕ
  lowerFinish : ℕ
  lowerRealizes : w.Realizes lowerStart lowerFinish
  start_step : X = lowerStart + w.residueModulus
  finish_step : Y = lowerFinish + 2 * 3 ^ w.oddSteps
  start_lt : lowerStart < X
  finish_lt : lowerFinish < Y

namespace ReplayCoordinate

/-- replay quotientが正なら一つ下の自然数affine replayを明示できる。 -/
def lowerNaturalReplay
    {w : Collatz.Word} {X Y : ℕ}
    (C : ReplayCoordinate w X Y) (hpos : 0 < C.quotient) :
    LowerNaturalReplayData w X Y := by
  let q := C.quotient - 1
  have hq : C.quotient = q + 1 := by dsimp [q]; omega
  let X' := w.canonicalStart + w.residueModulus * q
  let Y' := w.canonicalEnd + 2 * 3 ^ w.oddSteps * q
  have hreal : w.Realizes X' Y' := by
    dsimp [X', Y']
    simpa [residueModulus] using (canonicalEnd_realizes w).replay (k := q)
  have hstartStep : X = X' + w.residueModulus := by
    rw [C.start_eq, hq]
    dsimp [X']
    ring
  have hfinishStep : Y = Y' + 2 * 3 ^ w.oddSteps := by
    rw [C.finish_eq, hq]
    dsimp [Y']
    ring
  refine ⟨X', Y', hreal, hstartStep, hfinishStep, ?_, ?_⟩
  · have hmodulus : 0 < w.residueModulus := Nat.pow_pos (by omega)
    omega
  · have hthree : 0 < 3 ^ w.oddSteps := Nat.pow_pos (by omega)
    omega

end ReplayCoordinate

/-- 同じwordの奇数終点二実現では開始差がcanonical法全体で割り切れる。 -/
theorem Realizes.residueModulus_dvd_startDifference
    {w : Collatz.Word} {x₁ x₂ y₁ y₂ : ℕ}
    (h₁ : w.Realizes x₁ y₁)
    (h₂ : w.Realizes x₂ y₂)
    (hx : x₁ ≤ x₂)
    (hy₁ : Odd y₁) (hy₂ : Odd y₂) :
    w.residueModulus ∣ x₂ - x₁ := by
  have hy : y₁ ≤ y₂ := h₁.finish_mono h₂ hx
  rcases hy₁ with ⟨a, ha⟩
  rcases hy₂ with ⟨b, hb⟩
  have hab : a ≤ b := by omega
  have hFinishDiff : y₂ - y₁ = 2 * (b - a) := by omega
  have hDiff := h₁.difference h₂ hx
  have hProduct :
      2 ^ (w.twoSteps + 1) ∣ 3 ^ w.oddSteps * (x₂ - x₁) := by
    refine ⟨b - a, ?_⟩
    calc
      3 ^ w.oddSteps * (x₂ - x₁)
          = 2 ^ w.twoSteps * (y₂ - y₁) := hDiff.symm
      _ = 2 ^ w.twoSteps * (2 * (b - a)) := by rw [hFinishDiff]
      _ = 2 ^ (w.twoSteps + 1) * (b - a) := by rw [pow_succ]; ring
  have hCoprime : Nat.Coprime (2 ^ (w.twoSteps + 1)) (3 ^ w.oddSteps) :=
    (by decide : Nat.Coprime 2 3).pow (w.twoSteps + 1) w.oddSteps
  have hDiv : 2 ^ (w.twoSteps + 1) ∣ x₂ - x₁ :=
    hCoprime.dvd_of_dvd_mul_left hProduct
  simpa [residueModulus] using hDiv

/-- canonical法の整数cast。 -/
@[simp] theorem residueModulus_int_cast (w : Collatz.Word) :
    (w.residueModulus : ℤ) = (2 : ℤ) ^ (w.twoSteps + 1) := by
  simp [residueModulus]

/-- canonical法の整数倍だけ下げるsigned replay。 -/
theorem RealizesInt.sub_replay
    {w : Collatz.Word} {x y : ℤ}
    (h : w.RealizesInt x y) (k : ℤ) :
    w.RealizesInt
      (x - (w.residueModulus : ℤ) * k)
      (y - 2 * (3 : ℤ) ^ w.oddSteps * k) := by
  unfold RealizesInt at h ⊢
  rw [w.residueModulus_int_cast]
  calc
    (2 : ℤ) ^ w.twoSteps *
          (y - 2 * (3 : ℤ) ^ w.oddSteps * k)
        = (2 : ℤ) ^ w.twoSteps * y -
            (2 : ℤ) ^ (w.twoSteps + 1) * (3 : ℤ) ^ w.oddSteps * k := by
              rw [pow_succ]
              ring
    _ = ((3 : ℤ) ^ w.oddSteps * x + w.affineConstInt) -
          (2 : ℤ) ^ (w.twoSteps + 1) * (3 : ℤ) ^ w.oddSteps * k := by rw [h]
    _ = (3 : ℤ) ^ w.oddSteps *
          (x - (2 : ℤ) ^ (w.twoSteps + 1) * k) + w.affineConstInt := by ring

end Word
end Collatz
