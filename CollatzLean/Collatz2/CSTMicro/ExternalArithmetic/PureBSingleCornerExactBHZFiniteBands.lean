import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBSingleCornerExactBHZWidth
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalPowerPGapGrowth14

set_option linter.style.emptyLine false

/-!
# Pure B single-corner: exact BHZ 初期 denominator band の数値閉鎖

`N = 19 + 15*ell` が初期 critical denominator table に入る範囲を、
degree 196 の majorant を使わず exact に評価する。

使用する exact P-coordinate は

  P7  = 53,
  P8  = 306,
  P9  = 665,
  P10 = 15601,
  P11 = 31867,
  P12 = 79335,
  P13 = 111202.

これにより

* ell = 13       : m-b <= 2155,
* 14 <= ell <= 19: m-b <= 2245,
* 20 <= ell <= 43: m-b <= 33195,
* 44 <= ell <= 5287: m-b <= 460397

を得る。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-! ## 1. 初期 P-coordinate の exact table -/

/-- `P_7 = 53`。 -/
theorem criticalPowerP_seven_eq :
    criticalPowerP 7 = 53 := by
  norm_num [criticalPowerP, criticalPowerConvergent, criticalInitialConvergent]

/-- `P_8 = 306`。 -/
theorem criticalPowerP_eight_eq :
    criticalPowerP 8 = 306 := by
  exact criticalPowerP_eight

/-- `P_9 = 665`。 -/
theorem criticalPowerP_nine_eq :
    criticalPowerP 9 = 665 := by
  exact criticalPowerP_nine

/-- `P_10 = 15601`。 -/
theorem criticalPowerP_ten_eq :
    criticalPowerP 10 = 15601 := by
  norm_num [criticalPowerP, criticalPowerConvergent, criticalInitialConvergent]

/-- `P_11 = 31867`。 -/
theorem criticalPowerP_eleven_eq :
    criticalPowerP 11 = 31867 := by
  norm_num [criticalPowerP, criticalPowerConvergent, criticalInitialConvergent]

/-- `P_12 = 79335`。 -/
theorem criticalPowerP_twelve_eq :
    criticalPowerP 12 = 79335 := by
  norm_num [
    criticalPowerP,
    criticalPowerConvergent,
    criticalTailState,
    criticalTailStart,
    criticalConv12,
    criticalConv13
  ]

/-- `P_13 = 111202`。 -/
theorem criticalPowerP_thirteen_eq :
    criticalPowerP 13 = 111202 := by
  norm_num [
    criticalPowerP,
    criticalPowerConvergent,
    criticalTailState,
    criticalTailStart,
    criticalConv12,
    criticalConv13
  ]

namespace MinimalActualABObstructionPacket

/-! ## 2. exact BHZ band ごとの terminal width -/

/--
`ell = 13` では `N=214` なので `P_7 <= N < P_8`。
exact selector の root は `P_8+P_9=971` 以下であり、
criticalization 左側の `18+15*ell` を足して `m-b <= 2155`。
-/
theorem singleCorner_m_sub_b_le_2155_of_ell_thirteen
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (S :
      (M.toPureBProfileObstruction hL).SingleExposedCornerRigidityPacket)
    (hmSize :
      (M.toPureBProfileObstruction hL).m + 1 <= 2 ^ 13) :
    (M.toPureBProfileObstruction hL).m - S.b <= 2155 := by
  have hWidth :=
    M.singleCorner_m_sub_b_le_exactBHZBand
      R hL S
      (ell := 13) (j := 7)
      hmSize
      (by omega)
      (by rw [criticalPowerP_seven_eq]; norm_num)
      (by rw [criticalPowerP_eight_eq]; norm_num)
  rw [criticalPowerP_eight_eq, criticalPowerP_nine_eq] at hWidth
  norm_num at hWidth ⊢
  exact hWidth

/--
`14 <= ell <= 19` では引き続き `P_7 <= N < P_8`。
この帯全体を `ell=19` の左側距離でまとめて `m-b <= 2245` とする。
-/
theorem singleCorner_m_sub_b_le_2245_of_ell_fourteen_nineteen
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (S :
      (M.toPureBProfileObstruction hL).SingleExposedCornerRigidityPacket)
    {ell : ℕ}
    (hmSize :
      (M.toPureBProfileObstruction hL).m + 1 <= 2 ^ ell)
    (hellLower : 14 <= ell)
    (hellUpper : ell <= 19) :
    (M.toPureBProfileObstruction hL).m - S.b <= 2245 := by
  have hWidth :=
    M.singleCorner_m_sub_b_le_exactBHZBand
      R hL S
      (ell := ell) (j := 7)
      hmSize
      (by omega)
      (by rw [criticalPowerP_seven_eq]; omega)
      (by rw [criticalPowerP_eight_eq]; omega)
  rw [criticalPowerP_eight_eq, criticalPowerP_nine_eq] at hWidth
  omega

/--
`20 <= ell <= 43` では `P_8 <= N < P_9`。
root は `P_9+P_10=16266` 以下なので、帯全体で `m-b <= 33195`。
-/
theorem singleCorner_m_sub_b_le_33195_of_ell_twenty_fortythree
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (S :
      (M.toPureBProfileObstruction hL).SingleExposedCornerRigidityPacket)
    {ell : ℕ}
    (hmSize :
      (M.toPureBProfileObstruction hL).m + 1 <= 2 ^ ell)
    (hellLower : 20 <= ell)
    (hellUpper : ell <= 43) :
    (M.toPureBProfileObstruction hL).m - S.b <= 33195 := by
  have hWidth :=
    M.singleCorner_m_sub_b_le_exactBHZBand
      R hL S
      (ell := ell) (j := 8)
      hmSize
      (by omega)
      (by rw [criticalPowerP_eight_eq]; omega)
      (by rw [criticalPowerP_nine_eq]; omega)
  rw [criticalPowerP_nine_eq, criticalPowerP_ten_eq] at hWidth
  omega

/--
`44 <= ell <= 5287` では `N` は `P_9` より右、`P_12` より左にある。
したがって band index は `9 <= j <= 11`。

各 `j` を列挙せず monotonicity だけで

  P_(j+1) <= P_12,
  P_(j+2) <= P_13

と押さえ、帯全体を一発で `m-b <= 460397` に局在する。
-/
theorem singleCorner_m_sub_b_le_460397_of_ell_fortyfour_5287
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (S :
      (M.toPureBProfileObstruction hL).SingleExposedCornerRigidityPacket)
    {ell : ℕ}
    (hmSize :
      (M.toPureBProfileObstruction hL).m + 1 <= 2 ^ ell)
    (hellLower : 44 <= ell)
    (hellUpper : ell <= 5287) :
    (M.toPureBProfileObstruction hL).m - S.b <= 460397 := by
  have hN : 2 <= 19 + 15 * ell := by
    omega
  obtain ⟨j, hjTwo, hBandLower, hBandUpper⟩ :=
    exists_criticalPowerP_band hN

  have hjNine : 9 <= j := by
    by_contra hnot
    have hjLe : j <= 8 := by omega
    have hMono :=
      criticalPowerP_mono_from_two
        (i := j + 1) (j := 9)
        (by omega) (by omega)
    rw [criticalPowerP_nine_eq] at hMono
    omega

  have hjEleven : j <= 11 := by
    by_contra hnot
    have hjTwelve : 12 <= j := by omega
    have hMono :=
      criticalPowerP_mono_from_two
        (i := 12) (j := j)
        (by omega) hjTwelve
    rw [criticalPowerP_twelve_eq] at hMono
    omega

  have hWidth :=
    M.singleCorner_m_sub_b_le_exactBHZBand
      R hL S hmSize hjTwo hBandLower hBandUpper

  have hPNext :=
    criticalPowerP_mono_from_two
      (i := j + 1) (j := 12)
      (by omega) (by omega)
  have hPNext2 :=
    criticalPowerP_mono_from_two
      (i := j + 2) (j := 13)
      (by omega) (by omega)
  rw [criticalPowerP_twelve_eq] at hPNext
  rw [criticalPowerP_thirteen_eq] at hPNext2
  omega

end MinimalActualABObstructionPacket

end ExternalArithmetic
end CSTMicro
end Collatz2
