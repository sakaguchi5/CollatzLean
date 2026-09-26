import CollatzLean.Collatz4.Core.Forward
set_option exponentiation.threshold 10996
/-!
# Collatz4.M7.Constants

m=7 前向き排除で使う固定定数を集約する。
Collatz3 の定義・名前空間には依存しない。

`gEnvelope` 自体は m=7 の数値を含まないが、現在の互換 API を保つため
このファイルに置いたまま、その一般的な単調性を数学的に証明する。
-/

namespace Collatz4.M7

/-- 元の全2指数。 -/
def totalTwoExponent : ℕ := 13396

/-- 前向き系の共通終端時刻。 -/
def targetTime : ℕ := 8456

/-- 目標値 `H` の2進指数。 -/
def targetTwoExponent : ℕ := 10996

/-- `H` の奇数部分。 -/
def targetOdd : ℕ := 87 * 2 ^ 2400 - 1

/-- 前向き反復の目標値。 -/
def targetH : ℕ := 2 ^ targetTwoExponent * targetOdd

/-- `G_* = H - 3^8456`。 -/
def gStar : ℕ := targetH - 3 ^ targetTime

/-- 終端 `B_{q,2401}` を剥がした後に残る総2指数。 -/
def residualTwoExponent (q : ℕ) : ℕ := targetTwoExponent - 2 * q

/-- 総2指数 `E` で作れる `G` の理論包絡線。 -/
def gEnvelope (E : ℕ) : ℕ := 3 ^ (E + 1) - 2 ^ (E + 2)

/--
`gEnvelope` は指数を1増やしても減らない。

証明では冪そのものを比較する必要はなく、
`A - B ≤ 3A - 2B` という自然数減算の一般的な算術だけを使う。
-/
theorem gEnvelope_le_succ (E : ℕ) :
    gEnvelope E ≤ gEnvelope (E + 1) := by
  have h3 : 3 ^ ((E + 1) + 1) = 3 * 3 ^ (E + 1) := by
    rw [pow_succ]
    ac_rfl
  have h2 : 2 ^ ((E + 1) + 2) = 2 * 2 ^ (E + 2) := by
    have hexp : (E + 1) + 2 = (E + 2) + 1 := by
      omega
    rw [hexp, pow_succ]
    ac_rfl
  unfold gEnvelope
  rw [h3, h2]
  omega

/-- `gEnvelope` は総2指数 `E` に関して単調増加。 -/
theorem gEnvelope_monotone : Monotone gEnvelope := by
  exact monotone_nat_of_le_succ gEnvelope_le_succ

/-- 1275 境界の左端。 -/
theorem residualTwoExponent_1275 : residualTwoExponent 1275 = 8446 := by
  decide

/-- 1276 では既に 8446 を2だけ下回る。 -/
theorem residualTwoExponent_1276 : residualTwoExponent 1276 = 8444 := by
  decide

/-- `G_*` は `E=8445` の包絡線を超える。 -/
theorem envelope_8445_lt_gStar : gEnvelope 8445 < gStar := by
  decide

/-- `E=8446` の包絡線は `G_*` を超える。 -/
theorem gStar_lt_envelope_8446 : gStar < gEnvelope 8446 := by
  decide

/-- 目標奇数部分は1ではない。 -/
theorem one_lt_targetOdd : 1 < targetOdd := by
  decide

end Collatz4.M7
