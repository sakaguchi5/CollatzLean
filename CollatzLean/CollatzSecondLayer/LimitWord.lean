import CollatzLean.CollatzSecondLayer.MovingCompactness
import CollatzLean.CollatzFirstLayer.FirstCarry
import Mathlib.Tactic.Ring

/-!
# 極限指数語の一方向膨張

future-minimumが実数的に無限大へ進み、固定長prefixが安定するなら、
極限指数語の各非空prefixは純乗法的に膨張する。
-/

namespace CollatzSecondLayer

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

/-- 有効な非空語では、`2^H`と`3^p`は等しくならない。 -/
lemma twoPow_ne_threePow_of_valid_nonempty
    {w : ExpWord} (hw : Valid w) (hne : w ≠ []) :
    2 ^ twoSteps w ≠ 3 ^ oddSteps w := by
  intro heq
  have hH : 0 < twoSteps w :=
    twoSteps_pos_of_valid_nonempty hw hne
  have hodd3 : Odd (3 : ℕ) := ⟨1, by omega⟩
  have hodd : Odd (3 ^ oddSteps w) :=
    hodd3.pow
  have heven2 : Even (2 : ℕ) := ⟨1, by omega⟩
  have heven : Even (2 ^ twoSteps w) :=
    heven2.pow_of_ne_zero (Nat.ne_of_gt hH)
  have hboth : Even (3 ^ oddSteps w) := by
    rw [← heq]
    exact heven
  exact odd_even_false_nat hodd hboth


/-- 正の長さに対応する極限語は空語ではない。 -/
lemma limitWord_nonempty
    {O : OddOrbit} (D : MovingLimitData O)
    {m : ℕ} (hm : 0 < m) :
    D.limitWord m ≠ [] := by
  intro hnil
  have hlen : m = 0 := by
    simpa [MovingLimitData.limitWord] using
      congrArg List.length hnil
  omega


/--
有限区間の指数語が`w`に一致すれば、
その区間は`w`に従う実行を与える。
-/
lemma runs_of_segmentWord_eq
    {O : OddOrbit} {i m : ℕ} {w : ExpWord}
    (hword : O.segmentWord i m = w) :
    Runs w
      (O.value i)
      (O.value (i + m)) := by
  have hseg := O.runs_segment i m
  rw [hword] at hseg
  exact hseg


/--
語`w`による実行で終点が始点以上なら、
純乗法項とaffine項の間に上界不等式が成り立つ。
-/
lemma scaled_le_of_run_and_start_le_end
    {w : ExpWord} {X Z : ℕ}
    (hrun : Runs w X Z)
    (hXZ : X ≤ Z) :
    2 ^ twoSteps w * X ≤
      3 ^ oddSteps w * X + affineConst w := by
  have hreal := hrun.realizes
  calc
    2 ^ twoSteps w * X
        ≤ 2 ^ twoSteps w * Z := by
            exact Nat.mul_le_mul_left _ hXZ
    _ = 3 ^ oddSteps w * X + affineConst w :=
        hreal


/--
`B + 1 ≤ A`かつ`A*x ≤ B*x + C`なら、`x ≤ C`である。

左辺と右辺の共通部分`B*x`を除去するための、
純粋な自然数算術補題。
-/
lemma value_le_affine_of_coefficient_gap
    {A B C x : ℕ}
    (hgap : B + 1 ≤ A)
    (hupper : A * x ≤ B * x + C) :
    x ≤ C := by
  have hscaled :
      (B + 1) * x ≤ A * x := by
    exact Nat.mul_le_mul_right x hgap
  have hchain :
      B * x + x ≤ B * x + C := by
    calc
      B * x + x = (B + 1) * x := by
        ring
      _ ≤ A * x := hscaled
      _ ≤ B * x + C := hupper
  exact Nat.le_of_add_le_add_left hchain


/--
有効な非空語が膨張しないなら、
`2^H`は`3^p`より少なくとも1だけ大きい。
-/
lemma coefficient_gap_of_valid_nonexpanding
    {w : ExpWord}
    (hw : Valid w)
    (hne : w ≠ [])
    (hnot : ¬Expanding w) :
    3 ^ oddSteps w + 1 ≤ 2 ^ twoSteps w := by
  have hle :
      3 ^ oddSteps w ≤ 2 ^ twoSteps w := by
    unfold Expanding at hnot
    omega
  have hnepow :
      2 ^ twoSteps w ≠ 3 ^ oddSteps w :=
    twoPow_ne_threePow_of_valid_nonempty hw hne
  omega


/--
future-minimumのmoving limitから得られる極限語は、
すべての非空prefixで純乗法的に膨張する。
-/
theorem limitWord_expanding
    {O : OddOrbit} (D : MovingLimitData O)
    {m : ℕ} (hm : 0 < m) :
    Expanding (D.limitWord m) := by
  let w := D.limitWord m
  have hw : Valid w := by
    simpa [w] using D.limitWord_valid m
  have hne : w ≠ [] := by
    simpa [w] using limitWord_nonempty D hm
  obtain ⟨J, hstable⟩ :=
    D.prefix_stabilizes m
  obtain ⟨j, hjJ, hjlarge⟩ :=
    D.minima.eventually_large (affineConst w) J
  have hword :
      O.segmentWord (D.minima.index j) m = w := by
    simpa [w, MovingLimitData.limitWord] using
      hstable j hjJ
  have hrun :
      Runs w
        (O.value (D.minima.index j))
        (O.value (D.minima.index j + m)) :=
    runs_of_segmentWord_eq hword
  have hend :
      O.value (D.minima.index j) ≤
        O.value (D.minima.index j + m) :=
    D.minima.futureMinimum j _ (by omega)
  have hupper :
      2 ^ twoSteps w * O.value (D.minima.index j) ≤
        3 ^ oddSteps w * O.value (D.minima.index j) +
          affineConst w :=
    scaled_le_of_run_and_start_le_end hrun hend
  by_contra hnot
  have hgap :
      3 ^ oddSteps w + 1 ≤ 2 ^ twoSteps w :=
    coefficient_gap_of_valid_nonexpanding hw hne hnot
  have hsmall :
      O.value (D.minima.index j) ≤ affineConst w :=
    value_le_affine_of_coefficient_gap hgap hupper
  omega

end CollatzSecondLayer
