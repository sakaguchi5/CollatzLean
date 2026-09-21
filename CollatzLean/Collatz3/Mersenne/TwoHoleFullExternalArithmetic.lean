import CollatzLean.Collatz3.Mersenne.TwoHoleFullPattern

/-!
# Collatz3 Mersenne: full six-term two-hole 外部算術 interface

内部では `k≥3` の two-hole equation を three placements すべて full six-term
nondegenerate certificate まで縮約した。

このファイルでは、その genuinely full case にだけ必要な外部 arithmetic を
一つの proposition-valued structure に隔離する。one-hole の外部仮定や
proper residual はここへ含めない。
-/

namespace Collatz3
namespace Mersenne

/--
full six-term two-hole arithmetic の外部 package。

想定する中身は effective S-unit / Baker 型 bound と、その bounded residual に対する
modular / Hensel / finite certificate の合成。repository 側では最終的に必要な
`k≥7` 排除だけを interface として受け取る。
-/
structure TwoHoleFullExternalArithmetic : Prop where
  largeDepth_impossible :
    ∀ {k n r L : ℕ},
      7 ≤ k →
      TwoHoleFullCase k n r L →
      False

/-- external full-six-term package の下では、well-formed two-hole は `k≤6`。 -/
theorem TwoHoleWellFormedEquation.depth_le_six_of_external
    (A : TwoHoleFullExternalArithmetic)
    {k n r L : ℕ}
    (h : TwoHoleWellFormedEquation k n r L) :
    k ≤ 6 := by
  by_contra hNot
  have hk7 : 7 ≤ k := by omega
  have hFull := h.exists_fullCase (by omega : 3 ≤ k)
  exact A.largeDepth_impossible hk7 hFull

/-- source-two の branch-specific convenience theorem。 -/
theorem SourceTwoHoleEquation.depth_le_six_of_full_external
    (A : TwoHoleFullExternalArithmetic)
    {k n r L a b : ℕ}
    (ha0 : 0 < a)
    (hab : a < b)
    (hbn : b < n)
    (hr : 0 < r)
    (hL : 0 < L)
    (hEq : SourceTwoHoleEquation k n r L a b) :
    k ≤ 6 := by
  exact TwoHoleWellFormedEquation.depth_le_six_of_external A
    (TwoHoleWellFormedEquation.source a b ha0 hab hbn hr hL hEq)

/-- split-two の branch-specific convenience theorem。 -/
theorem SplitTwoHoleEquation.depth_le_six_of_full_external
    (A : TwoHoleFullExternalArithmetic)
    {k n r L a b : ℕ}
    (ha0 : 0 < a)
    (han : a < n)
    (hr : 0 < r)
    (hb0 : 0 < b)
    (hbL : b < L)
    (hEq : SplitTwoHoleEquation k n r L a b) :
    k ≤ 6 := by
  exact TwoHoleWellFormedEquation.depth_le_six_of_external A
    (TwoHoleWellFormedEquation.split a b ha0 han hr hb0 hbL hEq)

/-- target-two の branch-specific convenience theorem。 -/
theorem TargetTwoHoleEquation.depth_le_six_of_full_external
    (A : TwoHoleFullExternalArithmetic)
    {k n r L a b : ℕ}
    (hn : 0 < n)
    (hr : 0 < r)
    (ha0 : 0 < a)
    (hab : a < b)
    (hbL : b < L)
    (hEq : TargetTwoHoleEquation k n r L a b) :
    k ≤ 6 := by
  exact TwoHoleWellFormedEquation.depth_le_six_of_external A
    (TwoHoleWellFormedEquation.target a b hn hr ha0 hab hbL hEq)

end Mersenne
end Collatz3
