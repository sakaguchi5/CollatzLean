import CollatzLean.Collatz3.Mersenne.SmallHoleModular
import Mathlib.Tactic.NormNum

/-!
# Collatz3 Mersenne: tail / loop modular infrastructure

`Pow23Periods` は 2,3 がともに unit である modulus には便利だが、
small-hole の有限 lifting では `2^s` や `3^t` を modulus に含め、

* 小さい exponent は exact な tail として保持する
* tail 以後だけ period で畳む

方が強い。

このファイルでは一つの base に対する `PowTailLoop` と、2/3 を同時に持つ
`Pow23TailLoops` を置く。
-/

namespace Collatz3
namespace Mersenne

/-- tail / loop で exponent を有限代表へ落とす。 -/
def tailLoopExponent (tail period e : ℕ) : ℕ :=
  if e < tail then e else tail + ((e - tail) % period)

/--
`base^tail * base^period = base^tail (mod m)` を tail/loop certificate とする。

base が unit なら `tail=0` で通常の period に戻る。
base が modulus の素因子を含む場合は、tail で nilpotent 部分を吸収できる。
-/
structure PowTailLoop
    (m base tail period : ℕ) : Prop where
  period_pos : 0 < period
  loop_at_tail :
    (base : ZMod m) ^ tail * (base : ZMod m) ^ period =
      (base : ZMod m) ^ tail

namespace PowTailLoop

/-- tail 前では reduction は恒等。 -/
theorem tailLoopExponent_eq_self_of_lt
    {m base tail period e : ℕ}
    (_h : PowTailLoop m base tail period)
    (he : e < tail) :
    tailLoopExponent tail period e = e := by
  simp [tailLoopExponent, he]

/-- tail 以後では `tail + residue` に落ちる。 -/
theorem tailLoopExponent_eq_of_le
    {m base tail period e : ℕ}
    (_h : PowTailLoop m base tail period)
    (he : tail ≤ e) :
    tailLoopExponent tail period e =
      tail + ((e - tail) % period) := by
  simp [tailLoopExponent, Nat.not_lt.mpr he]

/-- reduction 後 exponent は `tail+period` 未満。 -/
theorem tailLoopExponent_lt
    {m base tail period e : ℕ}
    (h : PowTailLoop m base tail period) :
    tailLoopExponent tail period e < tail + period := by
  by_cases he : e < tail
  · rw [h.tailLoopExponent_eq_self_of_lt he]
    omega
  · have hle : tail ≤ e := Nat.le_of_not_gt he
    rw [h.tailLoopExponent_eq_of_le hle]
    have hmod : (e - tail) % period < period :=
      Nat.mod_lt _ h.period_pos
    omega

/-- loop factor は何周期掛けても tail を変えない。 -/
private theorem loop_pow
    {m base tail period q : ℕ}
    (h : PowTailLoop m base tail period) :
    (base : ZMod m) ^ tail *
        ((base : ZMod m) ^ period) ^ q =
      (base : ZMod m) ^ tail := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [pow_succ]
      calc
        (base : ZMod m) ^ tail *
              (((base : ZMod m) ^ period) ^ q *
                (base : ZMod m) ^ period)
            = ((base : ZMod m) ^ tail *
                ((base : ZMod m) ^ period) ^ q) *
                (base : ZMod m) ^ period := by ac_rfl
        _ = (base : ZMod m) ^ tail *
              (base : ZMod m) ^ period := by rw [ih]
        _ = (base : ZMod m) ^ tail := h.loop_at_tail

/--
任意 exponent の power は tail/loop representative の power と一致する。
-/
theorem pow_reduce
    {m base tail period e : ℕ}
    (h : PowTailLoop m base tail period) :
    (base : ZMod m) ^ e =
      (base : ZMod m) ^ (tailLoopExponent tail period e) := by
  by_cases he : e < tail
  · rw [h.tailLoopExponent_eq_self_of_lt he]
  · have hle : tail ≤ e := Nat.le_of_not_gt he
    let d : ℕ := e - tail
    let q : ℕ := d / period
    let s : ℕ := d % period
    have heq : e = tail + d := by
      dsimp [d]
      omega
    have hd : d = s + period * q := by
      dsimp [d, q, s]
      exact (Nat.mod_add_div (e - tail) period).symm
    have hloop := loop_pow h (q := q)
    rw [h.tailLoopExponent_eq_of_le hle]
    calc
      (base : ZMod m) ^ e
          = (base : ZMod m) ^ tail *
              (base : ZMod m) ^ d := by
              rw [heq, pow_add]
      _ = (base : ZMod m) ^ tail *
            (base : ZMod m) ^ (s + period * q) := by rw [hd]
      _ = (base : ZMod m) ^ tail *
            ((base : ZMod m) ^ s *
              (base : ZMod m) ^ (period * q)) := by rw [pow_add]
      _ = (base : ZMod m) ^ tail *
            ((base : ZMod m) ^ s *
              ((base : ZMod m) ^ period) ^ q) := by rw [pow_mul]
      _ = ((base : ZMod m) ^ tail *
              ((base : ZMod m) ^ period) ^ q) *
            (base : ZMod m) ^ s := by ac_rfl
      _ = (base : ZMod m) ^ tail *
            (base : ZMod m) ^ s := by rw [hloop]
      _ = (base : ZMod m) ^ (tail + s) := by rw [pow_add]

end PowTailLoop

/-- 2 と 3 の tail/loop certificate を同じ modulus 上に束ねる。 -/
structure Pow23TailLoops
    (m twoTail twoPeriod threeTail threePeriod : ℕ) : Prop where
  two : PowTailLoop m 2 twoTail twoPeriod
  three : PowTailLoop m 3 threeTail threePeriod

namespace Pow23TailLoops

/-- 2冪の finite tail/loop reduction。 -/
theorem two_pow_reduce
    {m twoTail twoPeriod threeTail threePeriod e : ℕ}
    (h : Pow23TailLoops
      m twoTail twoPeriod threeTail threePeriod) :
    (2 : ZMod m) ^ e =
      (2 : ZMod m) ^
        (tailLoopExponent twoTail twoPeriod e) :=
  h.two.pow_reduce

/-- 3冪の finite tail/loop reduction。 -/
theorem three_pow_reduce
    {m twoTail twoPeriod threeTail threePeriod e : ℕ}
    (h : Pow23TailLoops
      m twoTail twoPeriod threeTail threePeriod) :
    (3 : ZMod m) ^ e =
      (3 : ZMod m) ^
        (tailLoopExponent threeTail threePeriod e) :=
  h.three.pow_reduce

end Pow23TailLoops

/-! ## small-hole modular equations の tail/loop reduction -/

theorem SourceOneHoleModEquation.reduce_tailLoop
    {m t2 p2 t3 p3 k n r L a : ℕ}
    (hTL : Pow23TailLoops m t2 p2 t3 p3)
    (h : SourceOneHoleModEquation m k n r L a) :
    SourceOneHoleModEquation m
      (tailLoopExponent t3 p3 k)
      (tailLoopExponent t2 p2 n)
      (tailLoopExponent t2 p2 r)
      (tailLoopExponent t2 p2 L)
      (tailLoopExponent t2 p2 a) := by
  unfold SourceOneHoleModEquation at h ⊢
  rw [← hTL.three_pow_reduce (e := k),
      ← hTL.two_pow_reduce (e := n),
      ← hTL.two_pow_reduce (e := r),
      ← hTL.two_pow_reduce (e := L),
      ← hTL.two_pow_reduce (e := a)]
  exact h

theorem TargetOneHoleModEquation.reduce_tailLoop
    {m t2 p2 t3 p3 k n r L b : ℕ}
    (hTL : Pow23TailLoops m t2 p2 t3 p3)
    (h : TargetOneHoleModEquation m k n r L b) :
    TargetOneHoleModEquation m
      (tailLoopExponent t3 p3 k)
      (tailLoopExponent t2 p2 n)
      (tailLoopExponent t2 p2 r)
      (tailLoopExponent t2 p2 L)
      (tailLoopExponent t2 p2 b) := by
  unfold TargetOneHoleModEquation at h ⊢
  rw [← hTL.three_pow_reduce (e := k),
      ← hTL.two_pow_reduce (e := n),
      ← hTL.two_pow_reduce (e := r),
      ← hTL.two_pow_reduce (e := L),
      ← hTL.two_pow_reduce (e := b)]
  exact h

theorem SourceTwoHoleModEquation.reduce_tailLoop
    {m t2 p2 t3 p3 k n r L a b : ℕ}
    (hTL : Pow23TailLoops m t2 p2 t3 p3)
    (h : SourceTwoHoleModEquation m k n r L a b) :
    SourceTwoHoleModEquation m
      (tailLoopExponent t3 p3 k)
      (tailLoopExponent t2 p2 n)
      (tailLoopExponent t2 p2 r)
      (tailLoopExponent t2 p2 L)
      (tailLoopExponent t2 p2 a)
      (tailLoopExponent t2 p2 b) := by
  unfold SourceTwoHoleModEquation at h ⊢
  rw [← hTL.three_pow_reduce (e := k),
      ← hTL.two_pow_reduce (e := n),
      ← hTL.two_pow_reduce (e := r),
      ← hTL.two_pow_reduce (e := L),
      ← hTL.two_pow_reduce (e := a),
      ← hTL.two_pow_reduce (e := b)]
  exact h

theorem SplitTwoHoleModEquation.reduce_tailLoop
    {m t2 p2 t3 p3 k n r L a b : ℕ}
    (hTL : Pow23TailLoops m t2 p2 t3 p3)
    (h : SplitTwoHoleModEquation m k n r L a b) :
    SplitTwoHoleModEquation m
      (tailLoopExponent t3 p3 k)
      (tailLoopExponent t2 p2 n)
      (tailLoopExponent t2 p2 r)
      (tailLoopExponent t2 p2 L)
      (tailLoopExponent t2 p2 a)
      (tailLoopExponent t2 p2 b) := by
  unfold SplitTwoHoleModEquation at h ⊢
  rw [← hTL.three_pow_reduce (e := k),
      ← hTL.two_pow_reduce (e := n),
      ← hTL.two_pow_reduce (e := r),
      ← hTL.two_pow_reduce (e := L),
      ← hTL.two_pow_reduce (e := a),
      ← hTL.two_pow_reduce (e := b)]
  exact h

theorem TargetTwoHoleModEquation.reduce_tailLoop
    {m t2 p2 t3 p3 k n r L a b : ℕ}
    (hTL : Pow23TailLoops m t2 p2 t3 p3)
    (h : TargetTwoHoleModEquation m k n r L a b) :
    TargetTwoHoleModEquation m
      (tailLoopExponent t3 p3 k)
      (tailLoopExponent t2 p2 n)
      (tailLoopExponent t2 p2 r)
      (tailLoopExponent t2 p2 L)
      (tailLoopExponent t2 p2 a)
      (tailLoopExponent t2 p2 b) := by
  unfold TargetTwoHoleModEquation at h ⊢
  rw [← hTL.three_pow_reduce (e := k),
      ← hTL.two_pow_reduce (e := n),
      ← hTL.two_pow_reduce (e := r),
      ← hTL.two_pow_reduce (e := L),
      ← hTL.two_pow_reduce (e := a),
      ← hTL.two_pow_reduce (e := b)]
  exact h

/-! ## 最初の concrete tail/loop certificate -/

/--
`mod 5440 = 2^6 * 5 * 17` では 2冪は tail 6、その後 period 8。
Dimitrov--Howe 型 sieve の最初の concrete window として使える。
-/
theorem powTailLoop_two_mod5440 :
    PowTailLoop 5440 2 6 8 := by
  refine ⟨by norm_num, ?_⟩
  norm_num
  decide

/-- `mod 5440` では 3 は unit で period 16。 -/
theorem powTailLoop_three_mod5440 :
    PowTailLoop 5440 3 0 16 := by
  refine ⟨by norm_num, ?_⟩
  norm_num
  decide

/-- `mod 5440` の 2/3 combined certificate。 -/
theorem pow23TailLoops_mod5440 :
    Pow23TailLoops 5440 6 8 0 16 :=
  ⟨powTailLoop_two_mod5440, powTailLoop_three_mod5440⟩

end Mersenne
end Collatz3
