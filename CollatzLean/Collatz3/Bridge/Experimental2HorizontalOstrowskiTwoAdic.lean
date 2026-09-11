import CollatzLean.Collatz3.Bridge.Experimental2DualOstrowskiCoordinates
import CollatzLean.Collatz3.Experimental2.OstrowskiResidueScan
import CollatzLean.Collatz3.Arithmetic.ModTwoPow

/-!
# Collatz3 Bridge: initial-value Ostrowski の 2-adic scan-local law

horizontal canonical Ostrowski digits は、有限個の低位 suffix だけで
`v₂(3x+1)` を決める座標ではない。
しかし固定した `r` に対して全 digit を一度走査すれば、

`x mod 2^r`

を有限状態で exact に復元できる。
従って `v₂(3x+1) ≥ r` に相当する threshold

`2^r ∣ 3x+1`

も最終走査状態だけから exact に判定できる。

ここでは valuation の新定義は導入せず、2冪 divisibility を正本とする。
-/

namespace Collatz3
open Experimental2
namespace Bridge

namespace BeattyRegularOstrowskiSystem

/--
初期値 `x` の horizontal canonical digits を法 `2^r` で走査した最終状態。

`x + 1` 桁まで読めば canonical reconstruction theorem がそのまま使える。
-/
def horizontalTwoAdicScanState
    (D : BeattyRegularOstrowskiSystem)
    (r x : ℕ) : OstrowskiResidueState :=
  ostrowskiResidueStateAfter
    D.horizontalWeights
    (Arithmetic.twoPowModulus r)
    (D.horizontalOstrowskiDigits x)
    (x + 1)

/--
horizontal digit 全走査後の `sum` は initial value `x` の `2^r` 剰余そのもの。
-/
theorem horizontalTwoAdicScanState_sum_eq
    (D : BeattyRegularOstrowskiSystem)
    (r x : ℕ) :
    (D.horizontalTwoAdicScanState r x).sum =
      x % Arithmetic.twoPowModulus r := by
  rw [horizontalTwoAdicScanState,
    ostrowskiResidueStateAfter_sum,
    D.horizontalOstrowskiDigits_reconstruct x]

/--
horizontal scan の最終 `sum` は initial value `x` と法 `2^r` で合同。
-/
theorem horizontalTwoAdicScanState_modEq
    (D : BeattyRegularOstrowskiSystem)
    (r x : ℕ) :
    (D.horizontalTwoAdicScanState r x).sum ≡
      x [MOD Arithmetic.twoPowModulus r] := by
  rw [D.horizontalTwoAdicScanState_sum_eq r x]
  exact Nat.mod_modEq x (Arithmetic.twoPowModulus r)

/--
`v₂(3x+1) ≥ r` を valuation を導入せず 2冪 divisibility で表す薄い述語。
-/
def HasTwoAdicCollatzThreshold
    (r x : ℕ) : Prop :=
  Arithmetic.twoPowModulus r ∣ 3 * x + 1

/--
初期値 `x` の `r`-threshold は horizontal Ostrowski 全走査の最終 residue だけで判定できる。

これは

`v₂` は finite-suffix-local ではないが scan-local である

という主張の exact な整数論版である。
-/
theorem hasTwoAdicCollatzThreshold_iff_horizontalScan
    (D : BeattyRegularOstrowskiSystem)
    (r x : ℕ) :
    HasTwoAdicCollatzThreshold r x ↔
      Arithmetic.twoPowModulus r ∣
        3 * (D.horizontalTwoAdicScanState r x).sum + 1 := by
  have hCong :
      3 * (D.horizontalTwoAdicScanState r x).sum + 1 ≡
        3 * x + 1 [MOD Arithmetic.twoPowModulus r] :=
    three_mul_add_one_modEq_of_modEq
      (D.horizontalTwoAdicScanState_modEq r x)
  constructor
  · intro hx
    have hRight :
        3 * x + 1 ≡ 0 [MOD Arithmetic.twoPowModulus r] :=
      Nat.modEq_zero_iff_dvd.2 hx
    exact Nat.modEq_zero_iff_dvd.1 (hCong.trans hRight)
  · intro hs
    have hLeft :
        3 * (D.horizontalTwoAdicScanState r x).sum + 1 ≡
          0 [MOD Arithmetic.twoPowModulus r] :=
      Nat.modEq_zero_iff_dvd.2 hs
    exact Nat.modEq_zero_iff_dvd.1 (hCong.symm.trans hLeft)

/--
threshold 判定を remainder `= 0` の形で書いた版。

最終 state 以外の full integer `x` を判定側に再投入しない。
-/
theorem hasTwoAdicCollatzThreshold_iff_horizontalScan_mod_eq_zero
    (D : BeattyRegularOstrowskiSystem)
    (r x : ℕ) :
    HasTwoAdicCollatzThreshold r x ↔
      (3 * (D.horizontalTwoAdicScanState r x).sum + 1) %
          Arithmetic.twoPowModulus r = 0 := by
  rw [D.hasTwoAdicCollatzThreshold_iff_horizontalScan r x]
  exact Nat.dvd_iff_mod_eq_zero

/--
実際の初期値を一度 canonical horizontal digits にした後は、任意の固定 depth `r` について
`3x+1` の `2^r` divisibility を residue state だけで読める。

この定理は suffix locality を主張しない。高位 digit も scan の途中で `sum` を更新し得る。
-/
theorem horizontalOstrowski_scan_local_twoAdicCriterion
    (D : BeattyRegularOstrowskiSystem)
    (r x : ℕ) :
    (Arithmetic.twoPowModulus r ∣ 3 * x + 1) ↔
      (3 * (D.horizontalTwoAdicScanState r x).sum + 1) %
          Arithmetic.twoPowModulus r = 0 := by
  exact D.hasTwoAdicCollatzThreshold_iff_horizontalScan_mod_eq_zero r x

end BeattyRegularOstrowskiSystem

end Bridge
end Collatz3
