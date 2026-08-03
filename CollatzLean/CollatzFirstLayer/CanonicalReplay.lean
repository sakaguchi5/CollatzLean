import CollatzLean.CollatzFirstLayer.Orbit
import CollatzLean.CollatzFirstLayer.Replay

/-!
# canonical replay座標と直前shadow

canonical剰余類の最小非負代表から、対応する奇数終点を語だけから構成する。
さらに、任意の自然数実現をcanonical代表からのreplay回数で一意に座標化し、
一つ下の合同代表に対応する整数shadowとconnection方程式を導く。
-/

namespace CollatzFirstLayer
namespace ExpWord

/-- 自然数に限定しない有限語のアフィン実現式。 -/
def RealizesInt (w : ExpWord) (x y : ℤ) : Prop :=
  (2 : ℤ) ^ twoSteps w * y =
    (3 : ℤ) ^ oddSteps w * x + affineConstInt w

/-- 自然数上の実現式を整数上へ持ち上げる。 -/
theorem Realizes.toInt
    {w : ExpWord} {x y : ℕ}
    (h : Realizes w x y) :
    RealizesInt w (x : ℤ) (y : ℤ) := by
  unfold Realizes at h
  unfold RealizesInt
  simp only [affineConstInt]
  exact_mod_cast h

/-- canonical開始値を代入したアフィン式の分子。 -/
def canonicalNumerator (w : ExpWord) : ℕ :=
  3 ^ oddSteps w * canonicalStart w + affineConst w

/-- canonical分子は`2^H`を法`2^(H+1)`で持つ。 -/
theorem canonicalNumerator_mod_residueModulus
    (w : ExpWord) :
    canonicalNumerator w % residueModulus w =
      2 ^ twoSteps w := by
  haveI : NeZero (residueModulus w) :=
    ⟨by simp [residueModulus]⟩
  have hcast :
      ((canonicalNumerator w : ℕ) : ZMod (residueModulus w)) =
        ((2 ^ twoSteps w : ℕ) : ZMod (residueModulus w)) := by
    calc
      ((canonicalNumerator w : ℕ) : ZMod (residueModulus w))
          =
          (((3 ^ oddSteps w : ℕ) : ZMod (residueModulus w)) *
              ((canonicalStart w : ℕ) : ZMod (residueModulus w))) +
            ((affineConst w : ℕ) : ZMod (residueModulus w)) := by
              simp [canonicalNumerator]
      _ =
          (((3 ^ oddSteps w : ℕ) : ZMod (residueModulus w)) *
              canonicalClass w) +
            ((affineConst w : ℕ) : ZMod (residueModulus w)) := by
              rw [canonicalStart_cast]
      _ = ((2 ^ twoSteps w : ℕ) : ZMod (residueModulus w)) :=
        canonicalClass_spec w
  have hval := congrArg ZMod.val hcast
  have hpowlt :
      2 ^ twoSteps w < residueModulus w := by
    unfold residueModulus
    exact Nat.pow_lt_pow_right (by omega) (Nat.lt_succ_self _)
  calc
    canonicalNumerator w % residueModulus w
        =
        (((canonicalNumerator w : ℕ) :
            ZMod (residueModulus w))).val := by
          simp only [ZMod.val_natCast]
    _ =
        (((2 ^ twoSteps w : ℕ) :
            ZMod (residueModulus w))).val := hval
    _ = (2 ^ twoSteps w) % residueModulus w := by
          simp only [ZMod.val_natCast]
    _ = 2 ^ twoSteps w :=
          Nat.mod_eq_of_lt hpowlt

/-- canonical開始値に対応する正の奇数終点。 -/
def canonicalEnd (w : ExpWord) : ℕ :=
  2 * (canonicalNumerator w / residueModulus w) + 1

/-- canonical開始値とcanonical終点はアフィン実現式を満たす。 -/
theorem canonicalEnd_realizes (w : ExpWord) :
    Realizes w (canonicalStart w) (canonicalEnd w) := by
  unfold Realizes
  change
    2 ^ twoSteps w * canonicalEnd w = canonicalNumerator w
  have hdiv :=
    Nat.mod_add_div (canonicalNumerator w) (residueModulus w)
  rw [canonicalNumerator_mod_residueModulus] at hdiv
  calc
    2 ^ twoSteps w * canonicalEnd w
        =
      2 ^ twoSteps w +
        residueModulus w *
          (canonicalNumerator w / residueModulus w) := by
            unfold canonicalEnd residueModulus
            rw [pow_succ]
            ring
    _ = canonicalNumerator w := by
      simpa [Nat.mul_comm] using hdiv

/-- canonical終点は奇数。 -/
theorem canonicalEnd_odd (w : ExpWord) :
    Odd (canonicalEnd w) := by
  refine ⟨canonicalNumerator w / residueModulus w, ?_⟩
  unfold canonicalEnd
  omega

/-- canonical終点は正。 -/
theorem canonicalEnd_pos (w : ExpWord) :
    0 < canonicalEnd w := by
  unfold canonicalEnd
  omega

/--
任意の自然数実現をcanonical代表からのreplay回数で表す座標。
-/
structure CanonicalReplayCoordinate
    (w : ExpWord) (X Y : ℕ) where
  quotient : ℕ
  start_eq :
    X = canonicalStart w + residueModulus w * quotient
  finish_eq :
    Y = canonicalEnd w + 2 * 3 ^ oddSteps w * quotient

/-- 奇数終点を持つ自然数実現からcanonical replay座標を構成する。 -/
def canonicalReplayCoordinate_of_realization
    {w : ExpWord} {X Y : ℕ}
    (h : Realizes w X Y)
    (hY : Odd Y) :
    CanonicalReplayCoordinate w X Y := by
  let q := X / residueModulus w
  have hmod :
      X % residueModulus w = canonicalStart w :=
    natural_start_mod_eq_canonicalStart h hY
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
    simpa [residueModulus] using
      replay_theorem (canonicalEnd_realizes w) (k := q)
  have hfinish :
      Y = canonicalEnd w + 2 * 3 ^ oddSteps w * q := by
    have hsame :
        2 ^ twoSteps w * Y =
          2 ^ twoSteps w *
            (canonicalEnd w + 2 * 3 ^ oddSteps w * q) := by
      calc
        2 ^ twoSteps w * Y
            = 3 ^ oddSteps w * X + affineConst w := h
        _ =
          3 ^ oddSteps w *
              (canonicalStart w + residueModulus w * q) +
            affineConst w := by rw [hstart]
        _ =
          2 ^ twoSteps w *
            (canonicalEnd w + 2 * 3 ^ oddSteps w * q) :=
          hreplay.symm
    exact Nat.mul_left_cancel
      (Nat.pow_pos (by omega : 0 < (2 : ℕ))) hsame
  exact ⟨q, hstart, hfinish⟩

/-- 非空の実軌道区間からcanonical replay座標を構成する。 -/
def canonicalReplayCoordinate_of_runs
    {w : ExpWord} {X Y : ℕ}
    (h : Runs w X Y)
    (hne : w ≠ []) :
    CanonicalReplayCoordinate w X Y :=
  canonicalReplayCoordinate_of_realization
    h.realizes (h.end_odd_of_ne_nil hne)

/-- canonical合同類の一つ下にある整数開始値。 -/
def predecessorStart (w : ExpWord) : ℤ :=
  (canonicalStart w : ℤ) - (residueModulus w : ℤ)

/-- predecessor開始値は必ず負。 -/
theorem predecessorStart_neg (w : ExpWord) :
    predecessorStart w < 0 := by
  unfold predecessorStart
  have hlt :
      (canonicalStart w : ℤ) < (residueModulus w : ℤ) := by
    exact_mod_cast (canonicalStart_lt_modulus w)
  exact sub_neg.mpr hlt

/-- 一つ下の合同代表に対応する整数終点。 -/
def predecessorShadow (w : ExpWord) : ℤ :=
  (canonicalEnd w : ℤ) - 2 * (3 : ℤ) ^ oddSteps w

/-- predecessor開始値とpredecessor shadowは同じ語の整数実現式を満たす。 -/
theorem predecessorShadow_realizes (w : ExpWord) :
    RealizesInt w (predecessorStart w) (predecessorShadow w) := by
  have hcanon := Realizes.toInt (canonicalEnd_realizes w)
  unfold RealizesInt at hcanon ⊢
  unfold predecessorStart predecessorShadow residueModulus
  calc
    (2 : ℤ) ^ twoSteps w *
        ((canonicalEnd w : ℤ) - 2 * (3 : ℤ) ^ oddSteps w)
        =
      (2 : ℤ) ^ twoSteps w * (canonicalEnd w : ℤ) -
        (2 : ℤ) ^ (twoSteps w + 1) *
          (3 : ℤ) ^ oddSteps w := by
            rw [pow_succ]
            ring
    _ =
      ((3 : ℤ) ^ oddSteps w * (canonicalStart w : ℤ) +
        affineConstInt w) -
        (2 : ℤ) ^ (twoSteps w + 1) *
          (3 : ℤ) ^ oddSteps w := by rw [hcanon]
    _ =
      (3 : ℤ) ^ oddSteps w *
          ((canonicalStart w : ℤ) -
            (2 : ℤ) ^ (twoSteps w + 1)) +
        affineConstInt w := by ring

/-- predecessor shadowは奇数。 -/
theorem predecessorShadow_odd (w : ExpWord) :
    Odd (predecessorShadow w) := by
  have hcanon : Odd (canonicalEnd w : ℤ) :=
    (canonicalEnd_odd w).natCast
  have heven :
      Even (2 * (3 : ℤ) ^ oddSteps w) := by
    exact ⟨(3 : ℤ) ^ oddSteps w, by ring⟩
  exact hcanon.sub_even heven

/-- predecessor shadowは0にならない。 -/
theorem predecessorShadow_ne_zero (w : ExpWord) :
    predecessorShadow w ≠ 0 := by
  intro hzero
  have hodd := predecessorShadow_odd w
  rw [hzero] at hodd
  rcases hodd with ⟨k, hk⟩
  omega

/-- predecessor shadowが負であることの数値的特徴づけ。 -/
theorem predecessorShadow_neg_iff (w : ExpWord) :
    predecessorShadow w < 0 ↔
      (canonicalEnd w : ℤ) < 2 * (3 : ℤ) ^ oddSteps w := by
  unfold predecessorShadow
  omega

/-- predecessor shadowが正であることの数値的特徴づけ。 -/
theorem predecessorShadow_pos_iff (w : ExpWord) :
    0 < predecessorShadow w ↔
      2 * (3 : ℤ) ^ oddSteps w < (canonicalEnd w : ℤ) := by
  unfold predecessorShadow
  omega

/-- 一つ下の自然数合同代表へ降ろしたaffine replayデータ。 -/
structure LowerNaturalReplayData
    (w : ExpWord) (X Y : ℕ) where
  lowerStart : ℕ
  lowerFinish : ℕ
  lowerRealizes : Realizes w lowerStart lowerFinish
  start_step : X = lowerStart + residueModulus w
  finish_step : Y = lowerFinish + 2 * 3 ^ oddSteps w
  start_lt : lowerStart < X
  finish_lt : lowerFinish < Y

namespace CanonicalReplayCoordinate

/-- replay座標から得られるconnection方程式。 -/
theorem connectionEquation
    {w : ExpWord} {X Y : ℕ}
    (C : CanonicalReplayCoordinate w X Y) :
    (Y : ℤ) - predecessorShadow w =
      2 * (3 : ℤ) ^ oddSteps w * ((C.quotient : ℤ) + 1) := by
  have hfinish :
      (Y : ℤ) =
        (canonicalEnd w : ℤ) +
          2 * (3 : ℤ) ^ oddSteps w * (C.quotient : ℤ) := by
    exact_mod_cast C.finish_eq
  rw [hfinish]
  unfold predecessorShadow
  ring

/-- replay quotientが0なら、実開始値はcanonical代表そのもの。 -/
theorem start_eq_canonical_of_quotient_eq_zero
    {w : ExpWord} {X Y : ℕ}
    (C : CanonicalReplayCoordinate w X Y)
    (hzero : C.quotient = 0) :
    X = canonicalStart w := by
  rw [C.start_eq, hzero]
  simp

/-- 実開始値がcanonical代表そのものならreplay quotientは0。 -/
theorem quotient_eq_zero_of_start_eq_canonical
    {w : ExpWord} {X Y : ℕ}
    (C : CanonicalReplayCoordinate w X Y)
    (hstart : X = canonicalStart w) :
    C.quotient = 0 := by
  have hsum :
      canonicalStart w =
        canonicalStart w + residueModulus w * C.quotient := by
    calc
      canonicalStart w = X := hstart.symm
      _ = canonicalStart w + residueModulus w * C.quotient := C.start_eq
  have hmul : residueModulus w * C.quotient = 0 := by
    omega
  by_contra hq
  have hqpos : 0 < C.quotient := Nat.pos_of_ne_zero hq
  have hmodulusPos : 0 < residueModulus w := by
    exact Nat.pow_pos (by omega)
  have hpositive : 0 < residueModulus w * C.quotient :=
    Nat.mul_pos hmodulusPos hqpos
  omega

/-- replay quotient 0とcanonical境界は同値。 -/
theorem quotient_eq_zero_iff_start_eq_canonical
    {w : ExpWord} {X Y : ℕ}
    (C : CanonicalReplayCoordinate w X Y) :
    C.quotient = 0 ↔ X = canonicalStart w := by
  constructor
  · exact C.start_eq_canonical_of_quotient_eq_zero
  · exact C.quotient_eq_zero_of_start_eq_canonical

/-- replay quotientが正なら、一つ下の自然数affine replayを明示できる。 -/
def lowerNaturalReplay
    {w : ExpWord} {X Y : ℕ}
    (C : CanonicalReplayCoordinate w X Y)
    (hpos : 0 < C.quotient) :
    LowerNaturalReplayData w X Y := by
  let q := C.quotient - 1
  have hq : C.quotient = q + 1 := by
    dsimp [q]
    omega
  let X' := canonicalStart w + residueModulus w * q
  let Y' := canonicalEnd w + 2 * 3 ^ oddSteps w * q
  have hreal : Realizes w X' Y' := by
    dsimp [X', Y']
    simpa [residueModulus] using
      replay_theorem (canonicalEnd_realizes w) (k := q)
  have hstartStep : X = X' + residueModulus w := by
    rw [C.start_eq, hq]
    dsimp [X']
    ring
  have hfinishStep : Y = Y' + 2 * 3 ^ oddSteps w := by
    rw [C.finish_eq, hq]
    dsimp [Y']
    ring
  refine ⟨X', Y', hreal, hstartStep, hfinishStep, ?_, ?_⟩
  · have hmodulus : 0 < residueModulus w := by
      exact Nat.pow_pos (by omega)
    omega
  · have hthree : 0 < 3 ^ oddSteps w :=
      Nat.pow_pos (by omega)
    omega

end CanonicalReplayCoordinate

end ExpWord
end CollatzFirstLayer
