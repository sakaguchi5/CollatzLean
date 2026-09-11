import CollatzLean.Collatz3.Bridge.Experimental2CanonicalOstrowski

/-!
# Collatz3 Bridge: dual canonical Ostrowski coordinates

このファイルでは、初期値側と RecordFerrers 側に別々の大きな Ostrowski structure を置かない。
`BeattyRegularOstrowskiSystem` が持つ一つの continued-fraction lattice `(P,Q)` から、

* `Q` 側を用いる vertical canonical coordinate、
* 一段ずらした `P` 側を用いる horizontal canonical coordinate

だけを薄く導く。

vertical coordinate は profile height / two-depth の canonical 表現を担う。
horizontal coordinate は初期値、odd-step の位置、first-passage 幅、record length など、
通常の自然数を `log₂(3/2)` 側の Ostrowski weight で表す intrinsic coordinate を担う。

Record cut の位置そのものは horizontal coordinate を定義に保存しない。
まず vertical code を取り、同じ digit を `P` 側へ射影して Beatty inverse を復元し、
必要なら得られた自然数を改めて horizontal canonical form に正規化する。
この分離により `canonicalRecordLengths` も第三の primitive coordinate にはしない。

また二座標の関係も定義には埋め込まない。
同一 Collatz 軌道片の endpoint equation を仮定したときにだけ、
vertical code と horizontal code を一つの等式へ結ぶ derived theorem として与える。
-/

namespace Collatz3
open Experimental2
open ExactOstrowskiCorridorSystem
namespace Bridge

namespace BeattyRegularOstrowskiSystem

/--
`BeattyRegularOstrowskiSystem` の最初の partial quotient は必ず `1`。

`n = 0` の lower Farey certificate は

`1 < log₂ 3 < (a₀ + 1) / a₀`

を与える。一方 `2^3 < 3^2` から `3/2 < log₂ 3` が従うため、
`a₀ ≥ 2` なら `(a₀ + 1) / a₀ ≤ 3/2` となって矛盾する。

従って horizontal shifted `P`-weight system の初期条件は
外部仮定として保存する必要がない。
-/
@[simp] theorem firstPartialQuotient_eq_one
    (D : BeattyRegularOstrowskiSystem) :
    D.conv.a 0 = 1 := by
  have hUpper :=
    (D.lowerBracket 0 (by norm_num)).2.2.2.1
  rw [D.conv.q_one, D.conv.p_one] at hUpper
  have hThreeLe :
      3 ≤ Critical.beattyIndex 2 := by
    exact
      Critical.le_beattyIndex_of_twoPow_lt_threePow
        (by norm_num)
  have hBeattyStrict :
      (Critical.beattyIndex 2 : ℝ) <
        (2 : ℝ) * Real.logb 2 3 := by
    simpa using
      (beattyIndex_lt_mul_logb_two_three
        (m := 2) (by norm_num))
  have hSlope :
      (3 : ℝ) / 2 < Real.logb 2 3 := by
    have hThreeLeR :
        (3 : ℝ) ≤ (Critical.beattyIndex 2 : ℝ) := by
      exact_mod_cast hThreeLe
    nlinarith
  have haPos : 0 < D.conv.a 0 :=
    D.conv.a_pos 0
  by_contra hNe
  have haTwo : 2 ≤ D.conv.a 0 := by
    omega
  have haR :
      (0 : ℝ) < (D.conv.a 0 : ℝ) := by
    exact_mod_cast haPos
  have haTwoR :
      (2 : ℝ) ≤ (D.conv.a 0 : ℝ) := by
    exact_mod_cast haTwo
  have hRatio :
      (((D.conv.a 0 + 1 : ℕ) : ℝ) /
          (D.conv.a 0 : ℝ)) ≤
        (3 : ℝ) / 2 := by
    apply (div_le_iff₀ haR).2
    calc
      ((D.conv.a 0 + 1 : ℕ) : ℝ)
          = (D.conv.a 0 : ℝ) + 1 := by
              norm_num
      _ ≤ (3 / 2 : ℝ) * (D.conv.a 0 : ℝ) := by
              nlinarith
  linarith

/--
`P₁,P₂,...` を weight として使う horizontal Ostrowski system。

現行の shifted convergent では `P 0 = P 1 = 1` となる退化を一つ落とすため、
horizontal weight `n` は `P (n+1)` とする。

最初の部分商 `conv.a 0 = 1` は `firstPartialQuotient_eq_one` により
`n = 0` の Farey certificate から導出されるため、外部仮定として受け取らない。
-/
def horizontalWeights
    (D : BeattyRegularOstrowskiSystem) :
    UnitOstrowskiWeightSystem where
  a n := D.conv.a (n + 1)
  Q n := D.conv.P (n + 1)
  a_pos n := D.conv.a_pos (n + 1)
  q_zero := by
    rw [D.conv.p_one, D.firstPartialQuotient_eq_one]
  q_one := by
    rw [D.conv.p_rec 0, D.conv.p_one, D.conv.p_zero,
      D.firstPartialQuotient_eq_one]
    simp
  q_rec n := by
    simpa [Nat.add_assoc] using D.conv.p_rec (n + 1)

/--
vertical canonical coordinate。

`N` を既存の `Q`-weight 系で canonical に表す。
profile height / prefix two-depth / terminal height などの構造側の自然数にはこの座標を使う。
-/
def verticalOstrowskiDigits
    (D : BeattyRegularOstrowskiSystem)
    (N : ℕ) : ℕ → ℕ :=
  canonicalOstrowskiDigits D.weights N

/--
horizontal canonical coordinate。

初期値 `x`、odd-step の位置 `k`、first-passage 幅 `m`、record length `r` など、
通常の自然数を `P₁,P₂,...` の weight 系で canonical に表す。
用途ごとの別 structure は作らず、すべてこの一つの座標関数を使う。
-/
def horizontalOstrowskiDigits
    (D : BeattyRegularOstrowskiSystem)
    (n : ℕ) : ℕ → ℕ :=
  canonicalOstrowskiDigits (D.horizontalWeights) n

/--
vertical code を同じ lattice の `P` 側で評価した値。
RecordFerrers 側では、これに endpoint correction を加えると Beatty inverse の横座標になる。
-/
def verticalPShadow
    (D : BeattyRegularOstrowskiSystem)
    (N : ℕ) : ℕ :=
  ostrowskiPrefixSum D.conv.P (D.verticalOstrowskiDigits N) (N + 1)

/-- vertical canonical digits は元の `N` を `Q` 側で正確に復元する。 -/
theorem verticalOstrowskiDigits_reconstruct
    (D : BeattyRegularOstrowskiSystem)
    (N : ℕ) :
    ostrowskiPrefixSum D.weights.Q
        (D.verticalOstrowskiDigits N) (N + 1) = N := by
  simpa [verticalOstrowskiDigits] using
    canonicalOstrowskiDigits_reconstruct D.weights N

/-- horizontal canonical digits は元の自然数を shifted `P` weight 側で正確に復元する。 -/
theorem horizontalOstrowskiDigits_reconstruct
    (D : BeattyRegularOstrowskiSystem)
    (n : ℕ) :
    ostrowskiPrefixSum (D.horizontalWeights).Q
        (D.horizontalOstrowskiDigits n) (n + 1) = n := by
  simpa [horizontalOstrowskiDigits] using
    canonicalOstrowskiDigits_reconstruct (D.horizontalWeights) n

/-- horizontal weight は定義どおり shifted `P` 座標そのもの。 -/
@[simp] theorem horizontalWeights_Q
    (D : BeattyRegularOstrowskiSystem)
    (n : ℕ) :
    (D.horizontalWeights).Q n = D.conv.P (n + 1) := rfl

/-- vertical weight は元の convergent の `Q` 座標そのもの。 -/
@[simp] theorem verticalWeights_Q
    (D : BeattyRegularOstrowskiSystem)
    (n : ℕ) :
    D.weights.Q n = D.conv.Q n := rfl

/--
positive vertical coordinate の Beatty inverse は、vertical code の `P`-shadow と
最小非零 digit の parity correction だけから復元できる。

これは「RecordFerrers の structural code」と「横位置」を結ぶ基本射影公式であり、
horizontal intrinsic code そのものと同一視はしない。
-/
theorem beattyInverseHeight_eq_verticalPShadow_add_correction
    (D : BeattyRegularOstrowskiSystem)
    (N : ℕ)
    (hN : 0 < N) :
    beattyInverseHeight N =
      D.verticalPShadow N +
        (canonicalOstrowskiMinIndex D.weights N hN) % 2 := by
  simpa [verticalPShadow, verticalOstrowskiDigits] using
    D.beattyCanonicalOstrowski_height_formula N hN

/--
`k` が vertical height `N` の Beatty inverse であるなら、`k` は vertical code の
`P`-shadow と endpoint correction から導出される。
Record cut などはこの一般定理へ既存の inverse-boundary theorem を渡して使う。
-/
theorem horizontalPosition_eq_verticalPShadow_add_correction
    (D : BeattyRegularOstrowskiSystem)
    {N k : ℕ}
    (hN : 0 < N)
    (hk : k = beattyInverseHeight N) :
    k = D.verticalPShadow N +
      (canonicalOstrowskiMinIndex D.weights N hN) % 2 := by
  rw [hk]
  exact D.beattyInverseHeight_eq_verticalPShadow_add_correction N hN

/--
二つの vertical endpoint `N₀,N₁` から導かれる横位置の差は、第三の primitive coordinate を
導入せず、二つの Beatty inverse の差として定義できる。
`canonicalRecordLengths` はこの形の successive endpoint displacement として扱う。
-/
theorem horizontalDisplacement_eq_beattyInverse_sub
    {N₀ N₁ k₀ k₁ r : ℕ}
    (hk₀ : k₀ = beattyInverseHeight N₀)
    (hk₁ : k₁ = beattyInverseHeight N₁)
    (hr : r = k₁ - k₀) :
    r = beattyInverseHeight N₁ - beattyInverseHeight N₀ := by
  simpa [hk₀, hk₁] using hr

/--
前定理の displacement `r` も、独立した third coordinate を保存せず、必要な時点で
horizontal canonical coordinate に正規化できる。
-/
theorem horizontalDisplacement_reconstruct
    (D : BeattyRegularOstrowskiSystem)
    (r : ℕ) :
    ostrowskiPrefixSum (D.horizontalWeights).Q
        (D.horizontalOstrowskiDigits r) (r + 1) = r := by
  exact D.horizontalOstrowskiDigits_reconstruct r

/--
同一 Collatz 軌道片に由来する endpoint equation を、二つの canonical Ostrowski 座標へ
そのまま持ち上げる基本 coupling theorem。

ここでは endpoint equation 自体を定義へ埋め込まず、
`2^N * y = 3^k * x + A` を外から仮定する。
vertical code は `(N,k)` の structural coordinate を、horizontal code は初期値 `x` の
intrinsic coordinate を表す。
-/
theorem sameOrbit_dualOstrowski_endpointEquation
    (D : BeattyRegularOstrowskiSystem)
    {N k x y A : ℕ}
    (hN : 0 < N)
    (hk : k = beattyInverseHeight N)
    (hEndpoint : 2 ^ N * y = 3 ^ k * x + A) :
    2 ^ (ostrowskiPrefixSum D.weights.Q
          (D.verticalOstrowskiDigits N) (N + 1)) * y =
      3 ^ (D.verticalPShadow N +
            (canonicalOstrowskiMinIndex D.weights N hN) % 2) *
          (ostrowskiPrefixSum (D.horizontalWeights).Q
            (D.horizontalOstrowskiDigits x) (x + 1)) + A := by
  rw [D.verticalOstrowskiDigits_reconstruct N]
  rw [D.horizontalOstrowskiDigits_reconstruct x]
  have hk' :
      k = D.verticalPShadow N +
        (canonicalOstrowskiMinIndex D.weights N hN) % 2 :=
    D.horizontalPosition_eq_verticalPShadow_add_correction hN hk
  rw [← hk']
  exact hEndpoint

/--
同一軌道 coupling の divisibility 版。
structural vertical code が指定する `2`-depth は、horizontal initial coordinate と
`P`-shadow で書いた affine numerator を割り切る。
これは後で actual `Word.endpointEquation_iff` を接続するための薄い算術 API である。
-/
theorem sameOrbit_dualOstrowski_dvd
    (D : BeattyRegularOstrowskiSystem)
    {N k x y A : ℕ}
    (hN : 0 < N)
    (hk : k = beattyInverseHeight N)
    (hEndpoint : 2 ^ N * y = 3 ^ k * x + A) :
    2 ^ (ostrowskiPrefixSum D.weights.Q
          (D.verticalOstrowskiDigits N) (N + 1)) ∣
      3 ^ (D.verticalPShadow N +
            (canonicalOstrowskiMinIndex D.weights N hN) % 2) *
          (ostrowskiPrefixSum (D.horizontalWeights).Q
            (D.horizontalOstrowskiDigits x) (x + 1)) + A := by
  refine ⟨y, ?_⟩
  symm
  exact D.sameOrbit_dualOstrowski_endpointEquation hN hk hEndpoint

end BeattyRegularOstrowskiSystem

end Bridge
end Collatz3
