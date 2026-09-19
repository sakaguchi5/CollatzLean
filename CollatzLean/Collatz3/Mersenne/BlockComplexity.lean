import CollatzLean.Collatz3.Binary.Complexity
import CollatzLean.Collatz3.Mersenne.TargetTwoHoleValuation
import Mathlib.NumberTheory.Multiplicity

/-!
# Collatz3 Mersenne: target-two block complexity / Stephan bridge

この層は二つの仕事だけをする。

1. target-two の三 geometric phase をまとめて、残る内部 target を
   `Binary.HasPeriodBreakAtMost (3^k) n 5` として固定する。
2. Stephan/Baker--Wustholz 側から実際に必要な corollary を外部 `Prop` interface に隔離し、
   既存 `TargetTwoHoleValuation` の width bound と接続する。

重要なのは、Stephan の深い定理そのものを axiom として追加しないこと。
このファイルの `StephanValuationWidthPeriodBreakEscape` は、後で外部形式化または
明示的 finite bound に置き換えるための薄い interface にすぎない。
-/

namespace Collatz3
namespace Mersenne

/-- target-two の三 geometric phase を一つの Prop にまとめる。 -/
def TargetTwoHoleGeometricBranch
    (k n r L a b : ℕ) : Prop :=
  Nonempty (TargetTwoHoleWrappedGeometricData k n r L a b) ∨
    Nonempty (TargetTwoHoleSplitForwardGeometricData k n r L a b) ∨
      Nonempty (TargetTwoHoleSplitReverseGeometricData k n r L a b)

/--
3-block normal form から最終的に内部で証明したい period-break target。

`5` は二つの block boundary の bit mismatch を合わせた安全な上界。
この定義自体は仮定ではなく、後段で埋める内部 theorem target を名前にしたもの。
-/
def TargetTwoHolePeriodBreakAtMostFive : Prop :=
  ∀ {k n r L a b : ℕ},
    4 ≤ n →
    (r = 1 ∨ r = 2) →
    TargetTwoHoleGeometricBranch k n r L a b →
    Binary.HasPeriodBreakAtMost (3 ^ k) n 5

/--
Stephan の binary aperiodicity theorem から、この project が必要とする形だけを切り出す。

period `p` が `v₂(k)` または `v₂(k-1)` による logarithmic width 以下で、
period-break 数が固定値 `B` 以下なら、depth `k` は一様有界、という corollary。

この定義は axiom ではない。外部数学を明示的に受け取る interface である。
-/
def StephanValuationWidthPeriodBreakEscape : Prop :=
  ∀ B : ℕ,
    ∃ K : ℕ,
      ∀ {k p : ℕ},
        2 ≤ k →
        (p ≤ 3 + padicValNat 2 k ∨
          p ≤ 3 + padicValNat 2 (k - 1)) →
        Binary.HasPeriodBreakAtMost (3 ^ k) p B →
        k < K

/--
内部の `break≤5` と外部 Stephan corollary が揃えば、
target-two `n≥4` の三 geometric phase は一様 bounded-depth になる。

ここでは parity/exit-depth 対応も仮定に明示する。
* `r=1` は even `k`
* `r=2` は odd `k`
-/
theorem targetTwo_depth_bounded_of_stephan
    (hStephan : StephanValuationWidthPeriodBreakEscape)
    (hBreak : TargetTwoHolePeriodBreakAtMostFive) :
    ∃ K : ℕ,
      ∀ {k n r L a b : ℕ},
        2 ≤ k →
        4 ≤ n →
        ((r = 1 ∧ Even k) ∨ (r = 2 ∧ k % 2 = 1)) →
        TargetTwoHoleGeometricBranch k n r L a b →
        k < K := by
  unfold StephanValuationWidthPeriodBreakEscape at hStephan
  rcases hStephan 5 with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k n r L a b hk2 hn4 hParity hGeom
  unfold TargetTwoHolePeriodBreakAtMostFive at hBreak
  rcases hParity with hEvenBranch | hOddBranch
  · rcases hEvenBranch with ⟨rfl, hkEven⟩
    have hPB : Binary.HasPeriodBreakAtMost (3 ^ k) n 5 :=
      hBreak (k := k) (n := n) (r := 1) (L := L) (a := a) (b := b)
        hn4 (Or.inl rfl) hGeom
    have hWidth : n ≤ 3 + padicValNat 2 k := by
      rcases hGeom with hWrapped | hRest
      · rcases hWrapped with ⟨h⟩
        exact h.even_width_le (by omega) hkEven hn4
      · rcases hRest with hForward | hReverse
        · rcases hForward with ⟨h⟩
          exact h.even_width_le (by omega) hkEven hn4
        · rcases hReverse with ⟨h⟩
          exact h.even_width_le (by omega) hkEven hn4
    exact hK hk2 (Or.inl hWidth) hPB
  · rcases hOddBranch with ⟨rfl, hkOdd⟩
    have hPB : Binary.HasPeriodBreakAtMost (3 ^ k) n 5 :=
      hBreak (k := k) (n := n) (r := 2) (L := L) (a := a) (b := b)
        hn4 (Or.inr rfl) hGeom
    have hWidth : n ≤ 3 + padicValNat 2 (k - 1) := by
      rcases hGeom with hWrapped | hRest
      · rcases hWrapped with ⟨h⟩
        exact h.odd_width_le hk2 hkOdd hn4
      · rcases hRest with hForward | hReverse
        · rcases hForward with ⟨h⟩
          exact h.odd_width_le hk2 hkOdd hn4
        · rcases hReverse with ⟨h⟩
          exact h.odd_width_le hk2 hkOdd hn4
    exact hK hk2 (Or.inr hWidth) hPB

end Mersenne
end Collatz3
