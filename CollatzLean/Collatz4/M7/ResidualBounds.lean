import CollatzLean.Collatz4.General.ResidualBounds
import CollatzLean.Collatz4.M7.LengthBound

set_option exponentiation.threshold 10996

/-!
# Collatz4.M7.ResidualBounds

m=7 の残余語に対する `G`-bound を、一般 `ResidualGBounds` に特殊化する。

この層で使う数値境界は二点だけである。

* 上端側: `G_* < L(8446)`
* 下端側: `U(10994,4087) < G_*`

ここで `L/U` は `General.ResidualBounds` の粗い包絡線。
正確な `G_min/G_max` から粗い包絡線への移行は一般層で証明済みなので、
m=7 側では巨大な有限探索を行わない。
-/

namespace Collatz4.M7

/--
残余語側から finite candidate へ進むために必要な最小データ。

`g_bounds` は正確な `G_min/G_max` の間に `G_*` があることを保持する。
`q_pos` と偶数性は元の残余語の構造から供給されるべき意味論的条件である。
-/
structure ResidualData where
  q : ℕ
  r : ℕ
  q_pos : 0 < q
  q_admissible : qEnvelopeAdmissible q
  r_even : r % 2 = 0
  g_bounds :
    Collatz4.General.ResidualGBounds gStar (residualTwoExponent q) r

/-- `q≥1` なら残り2指数は `10994` 以下。 -/
theorem residualTwoExponent_le_10994_of_pos
    {q : ℕ} (hq : 0 < q) :
    residualTwoExponent q ≤ 10994 := by
  simp [residualTwoExponent, targetTwoExponent]
  omega

/--
上側長さ境界の数値一点。

`r=8446` では粗い下界だけで既に `G_*` を超える。
-/
theorem gStar_lt_coarseResidualLower_8446 :
    gStar < Collatz4.General.coarseResidualLower 8446 := by
  decide

/--
下側長さ境界の数値一点。

`E≤10994` かつ `r≤4087` なら単調性によりこの値以下なので、
`G_*` に到達できない。
-/
theorem coarseResidualUpper_10994_4087_lt_gStar :
    Collatz4.General.coarseResidualUpper 10994 4087 < gStar := by
  decide

namespace ResidualData

/-- admissible な residual data では従来どおり `q≤1275`。 -/
theorem q_le_1275 (d : ResidualData) : d.q ≤ 1275 :=
  q_le_1275_of_envelope d.q_admissible

/-- 正確な G-bound から残余語長の下端 `4088` を得る。 -/
theorem r_lower (d : ResidualData) : 4088 ≤ d.r := by
  have hE : residualTwoExponent d.q ≤ 10994 :=
    residualTwoExponent_le_10994_of_pos d.q_pos
  have hlt : 4087 < d.r :=
    Collatz4.General.ResidualGBounds.boundary_lt_length_of_upper_boundary
      d.g_bounds hE coarseResidualUpper_10994_4087_lt_gStar
  omega

/-- 正確な G-bound と偶数性から残余語長の上端 `8444` を得る。 -/
theorem r_upper (d : ResidualData) : d.r ≤ 8444 := by
  have hlt : d.r < 8446 :=
    Collatz4.General.ResidualGBounds.length_lt_of_lower_boundary
      d.g_bounds gStar_lt_coarseResidualLower_8446
  have heven := d.r_even
  omega

/-- m=7 residual data が満たす有限化直前の三条件をまとめる。 -/
theorem finite_interval (d : ResidualData) :
    d.q ≤ 1275 ∧ 4088 ≤ d.r ∧ d.r ≤ 8444 ∧ d.r % 2 = 0 := by
  exact ⟨d.q_le_1275, d.r_lower, d.r_upper, d.r_even⟩

end ResidualData

end Collatz4.M7
