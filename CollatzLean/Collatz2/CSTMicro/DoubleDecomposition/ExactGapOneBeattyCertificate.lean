import CollatzLean.Collatz2.CSTMicro.DoubleDecomposition.CriticalGapOneFerrersCertificate
import CollatzLean.Collatz2.CSTMicro.DoubleDecomposition.CriticalHeightBeattyBridge

/-!
# 真の gap=1 を固定する Beatty 終端条件

前段の `CriticalGapOneFerrersDeficitCertificate` は、
minimal FirstCrossing と critical affine budget を固定した。
ここではさらに terminal 2-depth が critical roof のちょうど一段上

  H = beattyIndex p + 1

であることを保持する。
また full packet の coefficient gap が正であることも保持する。
これにより、7・91 型の「first coefficient crossing の直後の1手でも contracting」
という局所 Beatty 幾何を certificate 自身に固定する。
-/

namespace Collatz2
namespace CSTMicro
namespace DoubleDecomposition

/--
7・91 型の真の gap-one certificate。

`terminalDepth_eq` が first crossing の terminal depth を critical roof + 1 に固定し、
`gap_pos` が最後の exponent-1 step を加えた全体も coefficient-contracting とする。
-/
structure ExactCriticalGapOneFerrersCertificate
    (w : Word)
    (p H deficit gap m : ℕ) : Prop
    extends CriticalGapOneFerrersDeficitCertificate w p H deficit gap m where
  terminalDepth_eq : H = beattyIndex p + 1
  gap_pos : 0 < gap

/-- 強化版から前段の critical certificate を取り出す。 -/
theorem ExactCriticalGapOneFerrersCertificate.toCritical
    {w : Word}
    {p H deficit gap m : ℕ}
    (C : ExactCriticalGapOneFerrersCertificate w p H deficit gap m) :
    CriticalGapOneFerrersDeficitCertificate w p H deficit gap m :=
  C.toCriticalGapOneFerrersDeficitCertificate

/-- terminal depth は Ferrers roof `criticalHeight p` のちょうど一段上。 -/
theorem ExactCriticalGapOneFerrersCertificate.terminalDepth_eq_criticalHeight_succ
    {w : Word}
    {p H deficit gap m : ℕ}
    (C : ExactCriticalGapOneFerrersCertificate w p H deficit gap m) :
    H = Word.criticalHeight p + 1 := by
  rw [C.terminalDepth_eq, criticalHeight_eq_beattyIndex]

/-- minimal block が非空なので odd-step 数 `p` は正。 -/
theorem ExactCriticalGapOneFerrersCertificate.oddSteps_pos
    {w : Word}
    {p H deficit gap m : ℕ}
    (C : ExactCriticalGapOneFerrersCertificate w p H deficit gap m) :
    0 < p := by
  have hne : w ≠ [] := C.minimal.2.nonempty
  have hlen : 0 < w.length := List.length_pos_iff.mpr hne
  simpa [← C.oddSteps_eq, Word.oddSteps] using hlen

/--
terminal の次の Beatty increment は exact に 1。

すなわち

  beattyIndex (p+1) = beattyIndex p + 1.

これは 7 と 91 に共通する「critical roof と平行に1セル進む」局所幾何である。
-/
theorem ExactCriticalGapOneFerrersCertificate.beattyIndex_succ_eq
    {w : Word}
    {p H deficit gap m : ℕ}
    (C : ExactCriticalGapOneFerrersCertificate w p H deficit gap m) :
    beattyIndex (p + 1) = beattyIndex p + 1 := by
  have hpPos : 0 < p := C.oddSteps_pos
  have hPrev : 2 ^ beattyIndex p < 3 ^ p :=
    beattyIndex_lower_strict_of_pos hpPos
  have hLow : 2 ^ H < 3 ^ (p + 1) := by
    rw [C.terminalDepth_eq, pow_succ, pow_succ]
    omega
  have hHighStrict : 3 ^ (p + 1) < 2 ^ (H + 1) := by
    have hEq := C.next_gap_equation
    have hGapPos : 0 < gap := C.gap_pos
    omega
  have hAtH : beattyIndex (p + 1) = H :=
    beattyIndex_eq_of_adjacent_dyadic_bracket hLow (Nat.le_of_lt hHighStrict)
  rw [hAtH, C.terminalDepth_eq]

/-- 真の gap-one certificate から既存の genuine run 結論を得る。 -/
theorem gapOneParadoxical_of_exactCriticalFerrersCertificate
    {w : Word}
    {p H deficit gap m : ℕ}
    (C : ExactCriticalGapOneFerrersCertificate w p H deficit gap m) :
    Runs w (3 * m + 1) (2 * m + 1) ∧
      2 * m + 1 < 3 * m + 1 ∧
      Word.Realizes ([1] : Word) (2 * m + 1) (3 * m + 2) := by
  exact gapOneParadoxical_of_criticalFerrersDeficitEquation C.toCritical

end DoubleDecomposition
end CSTMicro
end Collatz2
