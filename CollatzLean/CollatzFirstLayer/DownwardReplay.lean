import CollatzLean.CollatzFirstLayer.CanonicalReplay

/-!
# canonical replayの下向き取消し

上向きreplayだけでなく、実際の`Runs`が既知で開始値・終点が同じreplay幅だけ
上にある場合、その幅を取り除いた下側も同じ指数語を実行することを示す。
これによりpositive replay枝を単なるアフィン候補ではなくactual odd-only runへ昇格する。
-/

namespace CollatzFirstLayer
namespace ExpWord
namespace Runs

/-- 同じ語を同じ開始値から実行した終点は一意。 -/
theorem end_unique
    {w : ExpWord} {X Y Z : ℕ}
    (hY : Runs w X Y)
    (hZ : Runs w X Z) :
    Y = Z := by
  have hYr := hY.realizes
  have hZr := hZ.realizes
  unfold Realizes at hYr hZr
  have hmul : 2 ^ twoSteps w * Y = 2 ^ twoSteps w * Z := by
    calc
      2 ^ twoSteps w * Y
          = 3 ^ oddSteps w * X + affineConst w := hYr
      _ = 2 ^ twoSteps w * Z := hZr.symm
  exact Nat.mul_left_cancel
    (Nat.pow_pos (by omega : 0 < (2 : ℕ))) hmul

/--
consで語を1要素延長すると、residue modulusは先頭指数に対応する
`2 ^ e`倍になる。
-/
lemma residueModulus_cons_eq
    (e : ℕ) (w : ExpWord) :
    residueModulus (e :: w) =
      2 ^ e * residueModulus w := by
  unfold residueModulus
  rw [twoSteps_cons]
  rw [show e + twoSteps w + 1 = e + (twoSteps w + 1) by omega]
  rw [pow_add]

/--
residue modulusの任意の自然数倍は偶数である。
-/
lemma residueModulus_mul_even
    (w : ExpWord) (k : ℕ) :
    Even (residueModulus w * k) := by
  unfold residueModulus
  rw [pow_succ]
  refine ⟨2 ^ twoSteps w * k, ?_⟩
  ring

/--
奇数を「非負部分と偶数部分の和」に分解したとき、
非負部分も奇数になる。
-/
private lemma odd_of_eq_add_even
    {y y' shift : ℕ}
    (hy : Odd y)
    (hshift : Even shift)
    (hdecomp : y = y' + shift) :
    Odd y' := by
  rcases hy with ⟨a, ha⟩
  rcases hshift with ⟨b, hb⟩
  have hrel :
      y' + 2 * b = 2 * a + 1 := by
    omega
  have hbLe : b ≤ a := by
    omega
  refine ⟨a - b, ?_⟩
  omega

/--
cons runの先頭ステップからreplay幅を取り除く。

開始値から`residueModulus (e :: w) * k`を取り除くと、
中間値からはtail用の幅`residueModulus w * (3 * k)`が取り除かれる。
-/
lemma replay_head_down
    {e : ℕ}
    {w : ExpWord}
    {x y X' k : ℕ}
    (hstep : 2 ^ e * y = 3 * x + 1)
    (hy : Odd y)
    (hstart :
      x = X' + residueModulus (e :: w) * k) :
    ∃ y' : ℕ,
      y = y' + residueModulus w * (3 * k) ∧
      2 ^ e * y' = 3 * X' + 1 ∧
      Odd y' := by
  let shift : ℕ :=
    residueModulus w * (3 * k)
  have hscaled :
      2 ^ e * y =
        3 * X' + 1 + 2 ^ e * shift := by
    calc
      2 ^ e * y
          = 3 * x + 1 := hstep
      _ = 3 * (X' + residueModulus (e :: w) * k) + 1 := by
            rw [hstart]
      _ = 3 * X' + 1 + 2 ^ e * shift := by
            rw [residueModulus_cons_eq]
            dsimp [shift]
            ring
  have hshift_le :
      shift ≤ y := by
    have hpowPos :
        0 < 2 ^ e := Nat.pow_pos (by omega)
    have hmulLe :
        2 ^ e * shift ≤ 2 ^ e * y := by
      rw [hscaled]
      omega
    exact Nat.le_of_mul_le_mul_left hmulLe hpowPos
  let y' : ℕ :=
    y - shift
  have hydecomp :
      y = y' + shift := by
    dsimp [y']
    omega
  have hstep' :
      2 ^ e * y' = 3 * X' + 1 := by
    have hcancel :
        2 ^ e * y' + 2 ^ e * shift =
          (3 * X' + 1) + 2 ^ e * shift := by
      calc
        2 ^ e * y' + 2 ^ e * shift
            = 2 ^ e * (y' + shift) := by
                rw [Nat.mul_add]
        _ = 2 ^ e * y := by
              rw [← hydecomp]
        _ = (3 * X' + 1) + 2 ^ e * shift := hscaled
    exact Nat.add_right_cancel hcancel
  have hshiftEven :
      Even shift := by
    dsimp [shift]
    exact residueModulus_mul_even w (3 * k)
  have hyOdd :
      Odd y' := by
    exact odd_of_eq_add_even hy hshiftEven hydecomp
  exact ⟨y', hydecomp, hstep', hyOdd⟩

/--
consで増えた1回のodd stepを、tail側のreplay幅へ移す。
-/
lemma replay_finish_width_cons
    {e : ℕ}
    {w : ExpWord}
    {z Y' k : ℕ}
    (hfinish :
      z = Y' + 2 * 3 ^ oddSteps (e :: w) * k) :
    z = Y' + 2 * 3 ^ oddSteps w * (3 * k) := by
  rw [hfinish]
  simp only [oddSteps_cons, pow_succ]
  ring

/--
実際のrunからreplay幅を取り除く一般定理。

開始値を`residueModulus w * k`、終点を`2 * 3 ^ oddSteps w * k`
だけ下げた非負の候補値が与えられていれば、同じ語の`Runs`が成立する。
-/
theorem replay_down
    {w : ExpWord}
    {X Y X' Y' k : ℕ}
    (h : Runs w X Y)
    (hstart :
      X = X' + residueModulus w * k)
    (hfinish :
      Y = Y' + 2 * 3 ^ oddSteps w * k) :
    Runs w X' Y' := by
  induction h generalizing X' Y' k with
  | nil x =>
      have hxy : X' = Y' := by
        simp [residueModulus, twoSteps, oddSteps] at hstart hfinish
        omega
      subst Y'
      exact Runs.nil X'
  | @cons e w x y z he hstep hy _htail ih =>
      obtain ⟨y', htailStart, hstep', hy'⟩ :=
        replay_head_down
          (w := w)
          hstep
          hy
          hstart
      have htailFinish :
          z = Y' + 2 * 3 ^ oddSteps w * (3 * k) :=
        replay_finish_width_cons
          (e := e)
          (w := w)
          hfinish
      exact Runs.cons
        he
        hstep'
        hy'
        (ih htailStart htailFinish)

end Runs

/-- actual runまで保存する一段下の自然数replay。 -/
structure LowerNaturalRunReplayData
    (w : ExpWord) (X Y : ℕ) where
  lowerStart : ℕ
  lowerFinish : ℕ
  lowerRuns : Runs w lowerStart lowerFinish
  start_step : X = lowerStart + residueModulus w
  finish_step : Y = lowerFinish + 2 * 3 ^ oddSteps w
  start_lt : lowerStart < X
  finish_lt : lowerFinish < Y

namespace CanonicalReplayCoordinate

/--
正のreplay quotientを持つactual runから、一段下のactual runを構成する。
-/
def lowerNaturalRunReplay
    {w : ExpWord} {X Y : ℕ}
    (C : CanonicalReplayCoordinate w X Y)
    (hRun : Runs w X Y)
    (hpos : 0 < C.quotient) :
    LowerNaturalRunReplayData w X Y := by
  let L := C.lowerNaturalReplay hpos
  have hstart :
      X = L.lowerStart + residueModulus w * 1 := by
    simpa using L.start_step
  have hfinish :
      Y = L.lowerFinish + 2 * 3 ^ oddSteps w * 1 := by
    simpa using L.finish_step
  have hLower : Runs w L.lowerStart L.lowerFinish :=
    hRun.replay_down hstart hfinish
  exact
    ⟨L.lowerStart, L.lowerFinish, hLower,
      L.start_step, L.finish_step, L.start_lt, L.finish_lt⟩

end CanonicalReplayCoordinate
end ExpWord
end CollatzFirstLayer
