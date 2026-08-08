import CollatzLean.CollatzSecondLayer3.PolynomialCrossing
import CollatzLean.CollatzSecondLayer3.PositivePreparation

/-!
# first-crossing actual returnの算術核

negative shadowを主矛盾源にせず、future-minimumからfirst-crossing終点までの
actual positive returnだけを保存する。

中心となる量は

* `d = endpoint - start`
* `g = 2^H - 3^p`
* `B = affineConst`

であり、exact identity

`B = 3^p * d + g * endpoint`

を使う。

さらにfirst-crossingの全proper prefixがexpandingであることから
`B ≤ p * 3^(p-1)`までsharpに下げ、`3*d < p`を得る。
-/

namespace CollatzSecondLayer3

open CollatzSupport
open CollatzExternal
open CollatzCore
open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

namespace ExpWord

/--
WeightedPrefixBound の長さ0 prefixから先頭係数の bound を得る。
-/
private theorem weightedPrefixBound_head_le
    (e : ℕ)
    (w : ExpWord)
    (a c : ℕ)
    (h : WeightedPrefixBound a c (e :: w)) :
    a ≤ c := by
  have hh := h 0 (by simp)
  simpa [WeightedPrefixBound, twoSteps] using hh


/--
cons 語の WeightedPrefixBound を tail へ移す。

先頭指数 e を通過するため a は 2^e 倍、
3側の scale は 3 倍される。
-/
private theorem weightedPrefixBound_tail
    (e : ℕ)
    (w : ExpWord)
    (a c : ℕ)
    (h : WeightedPrefixBound a c (e :: w)) :
    WeightedPrefixBound (a * 2 ^ e) (c * 3) w := by
  intro j hj
  have hh := h (j + 1) (by
    simp
    omega)
  simpa [
    WeightedPrefixBound,
    List.take_succ_cons,
    twoSteps_cons,
    pow_add,
    pow_succ,
    Nat.mul_assoc,
    Nat.mul_left_comm,
    Nat.mul_comm
  ] using hh


/--
非空語では 3^length を length-1 scale へ落とせる。
-/
private theorem three_pow_length_eq_mul_pred
    (w : ExpWord)
    (hw : w ≠ []) :
    3 ^ w.length = 3 * 3 ^ (w.length - 1) := by
  have hwpos : 0 < w.length :=
    List.length_pos_of_ne_nil hw
  rw [show w.length = (w.length - 1) + 1 by omega, pow_succ]
  have h : w.length - 1 + 1 - 1 = w.length - 1 := by
    omega
  rw [h]
  ring


/--
sharp induction stepで必要な純算術合成。

head項とtail項をともに `3^(w.length-1)` scaleへ揃える。
-/
private theorem weighted_affineConst_cons_step
    (e : ℕ)
    (w : ExpWord)
    (a c : ℕ)
    (hw : w ≠ [])
    (h0 : a ≤ c)
    (hi :
      (a * 2 ^ e) * affineConst w ≤
        w.length * (c * 3) * 3 ^ (w.length - 1)) :
    a * affineConst (e :: w) ≤
      (e :: w).length * c * 3 ^ ((e :: w).length - 1) := by
  have hhead :
      a * 3 ^ w.length ≤
        c * 3 ^ w.length :=
    Nat.mul_le_mul_right (3 ^ w.length) h0
  have hpow :
      3 ^ w.length =
        3 * 3 ^ (w.length - 1) :=
    three_pow_length_eq_mul_pred w hw
  calc
    a * affineConst (e :: w)
        =
          a * 3 ^ w.length +
            (a * 2 ^ e) * affineConst w := by
          simp [affineConst]
          ring
    _ ≤
        c * 3 ^ w.length +
          w.length * (c * 3) * 3 ^ (w.length - 1) :=
      Nat.add_le_add hhead hi
    _ =
        (w.length + 1) * c * 3 ^ w.length := by
      rw [hpow]
      ring
    _ =
        (e :: w).length * c *
          3 ^ ((e :: w).length - 1) := by
      simp

/--
既存`weighted_affineConst_le`のsharp版。

非空語では、prefix boundの各項を`3^(length-1)`scaleへ揃えることで
余分な3倍を除去できる。
-/
theorem weighted_affineConst_le_sharp
    (w : ExpWord)
    (a c : ℕ)
    (h : WeightedPrefixBound a c w) :
    a * affineConst w ≤
      w.length * c * 3 ^ (w.length - 1) := by
  induction w generalizing a c with
  | nil =>
      simp [affineConst]
  | cons e w ih =>
      have h0 : a ≤ c :=
        weightedPrefixBound_head_le e w a c h
      by_cases hw : w = []
      · subst w
        simpa [affineConst] using h0
      · have htail :
            WeightedPrefixBound
              (a * 2 ^ e) (c * 3) w :=
          weightedPrefixBound_tail e w a c h
        have hi :
            (a * 2 ^ e) * affineConst w ≤
              w.length * (c * 3) *
                3 ^ (w.length - 1) :=
          ih
            (a := a * 2 ^ e)
            (c := c * 3)
            htail
        exact
          weighted_affineConst_cons_step
            e w a c hw h0 hi

/-- first-crossing語のaffine定数は`p * 3^(p-1)`以下。 -/
theorem firstCrossing_affineConst_le_length_mul_threePow_pred
    {w : ExpWord}
    (hC : FirstCrossing w) :
    affineConst w ≤ w.length * 3 ^ (w.length - 1) := by
  have h :=
    weighted_affineConst_le_sharp
      w 1 1 (firstCrossing_weightedPrefixBound hC)
  simpa using h

end ExpWord

/-- first-crossingのactual positive return gap。 -/
def firstCrossingReturnGap
    {O : OddOrbit} (n p : ℕ) : ℕ :=
  O.value (n + p) - O.value n

/-- first-crossingのpure multiplicative gap。 -/
def firstCrossingMultiplicativeGap
    {O : OddOrbit} (n p : ℕ) : ℕ :=
  2 ^ twoSteps (O.segmentWord n p) - 3 ^ p

/-- 非有界future-minimum first-crossingの終点は開始値より真に大きい。 -/
theorem firstCrossing_endpoint_gt_start
    {O : OddOrbit} {n p : ℕ}
    (hU : O.Unbounded)
    (hmin : O.FutureMinimumAt n)
    (hC : FirstCrossingAt O n p) :
    O.value n < O.value (n + p) := by
  have hp : 0 < p := hC.length_pos
  have hle := hmin (n + p) (by omega)
  have hne : O.value n ≠ O.value (n + p) := by
    exact O.value_ne_of_lt_of_unbounded hU (by omega)
  omega

/-- first-crossing return gapは正。 -/
theorem firstCrossingReturnGap_pos
    {O : OddOrbit} {n p : ℕ}
    (hU : O.Unbounded)
    (hmin : O.FutureMinimumAt n)
    (hC : FirstCrossingAt O n p) :
    0 < firstCrossingReturnGap (O := O) n p := by
  unfold firstCrossingReturnGap
  exact Nat.sub_pos_of_lt (firstCrossing_endpoint_gt_start hU hmin hC)

/-- first-crossing actual return gapは偶数。 -/
theorem firstCrossingReturnGap_even
    {O : OddOrbit} {n p : ℕ}
    (hU : O.Unbounded)
    (hmin : O.FutureMinimumAt n)
    (hC : FirstCrossingAt O n p) :
    Even (firstCrossingReturnGap (O := O) n p) := by
  have hlt := firstCrossing_endpoint_gt_start hU hmin hC
  rcases O.value_odd n with ⟨a, ha⟩
  rcases O.value_odd (n + p) with ⟨b, hb⟩
  have hab : a < b := by
    rw [ha, hb] at hlt
    omega
  refine ⟨b - a, ?_⟩
  unfold firstCrossingReturnGap
  rw [ha, hb]
  omega

/-- positive even return gapは少なくとも2。 -/
theorem two_le_firstCrossingReturnGap
    {O : OddOrbit} {n p : ℕ}
    (hU : O.Unbounded)
    (hmin : O.FutureMinimumAt n)
    (hC : FirstCrossingAt O n p) :
    2 ≤ firstCrossingReturnGap (O := O) n p := by
  obtain ⟨q, hq⟩ := firstCrossingReturnGap_even hU hmin hC
  have hpos := firstCrossingReturnGap_pos hU hmin hC
  rw [hq] at hpos ⊢
  omega

/-- first-crossing multiplicative gapは正。 -/
theorem firstCrossingMultiplicativeGap_pos
    {O : OddOrbit} {n p : ℕ}
    (hC : FirstCrossingAt O n p) :
    0 < firstCrossingMultiplicativeGap (O := O) n p := by
  unfold firstCrossingMultiplicativeGap
  have h := hC.terminalContracting
  simpa [oddSteps] using Nat.sub_pos_of_lt h

/--
actual realizationをreturn gapで書き直したexact identity。

`B = 3^p*d + g*endpoint`。
-/
theorem firstCrossing_return_identity
    {O : OddOrbit} {n p : ℕ}
    (hmin : O.FutureMinimumAt n)
    (hC : FirstCrossingAt O n p) :
    affineConst (O.segmentWord n p) =
      3 ^ p * firstCrossingReturnGap (O := O) n p +
        firstCrossingMultiplicativeGap (O := O) n p *
          O.value (n + p) := by
  let w := O.segmentWord n p
  let x := O.value n
  let z := O.value (n + p)
  let d := firstCrossingReturnGap (O := O) n p
  let H := twoSteps w
  let g := firstCrossingMultiplicativeGap (O := O) n p
  have hrun :
      2 ^ H * z = 3 ^ p * x + affineConst w := by
    simpa [w, x, z, H, Realizes, oddSteps] using O.realizes_segment n p
  have hxz : x ≤ z := hmin (n + p) (by omega)
  have hzd : z = x + d := by
    dsimp [d, firstCrossingReturnGap, x, z]
    omega
  have hcontractWord :
      (O.segmentWord n p).Contracting :=
    hC.terminalContracting
  have hcontract : 3 ^ p < 2 ^ H := by
    simpa [Contracting, w, H, oddSteps] using hcontractWord
  have htwo : 2 ^ H = 3 ^ p + g := by
    dsimp [g, firstCrossingMultiplicativeGap]
    exact (Nat.add_sub_of_le hcontract.le).symm
  have hcancel :
      3 ^ p * x +
          (3 ^ p * d + g * z) =
        3 ^ p * x + affineConst w := by
    calc
      3 ^ p * x + (3 ^ p * d + g * z)
          = (3 ^ p + g) * z := by
              rw [hzd]
              ring
      _ = 2 ^ H * z := by rw [htwo]
      _ = 3 ^ p * x + affineConst w := hrun
  have hEq :
      3 ^ p * d + g * z = affineConst w :=
    Nat.add_left_cancel hcancel
  simpa [w, z, d, g] using hEq.symm

/-- first-crossing affine定数のsharp orbit版。 -/
theorem firstCrossing_affineConst_le_sharp
    {O : OddOrbit} {n p : ℕ}
    (hC : FirstCrossingAt O n p) :
    affineConst (O.segmentWord n p) ≤
      p * 3 ^ (p - 1) := by
  have h :=
    ExpWord.firstCrossing_affineConst_le_length_mul_threePow_pred
      (w := O.segmentWord n p) hC
  simpa using h

/--
非有界future-minimum first-crossingのactual returnは`p/3`より真に小さい。
除算を使わず`3*d < p`で保存する。
-/
theorem three_mul_firstCrossingReturnGap_lt_length
    {O : OddOrbit} {n p : ℕ}
    (hmin : O.FutureMinimumAt n)
    (hC : FirstCrossingAt O n p) :
    3 * firstCrossingReturnGap (O := O) n p < p := by
  have hp : 0 < p := hC.length_pos
  obtain ⟨r, hr⟩ : ∃ r : ℕ, p = r + 1 := by
    exact ⟨p - 1, by omega⟩
  let d := firstCrossingReturnGap (O := O) n p
  let g := firstCrossingMultiplicativeGap (O := O) n p
  let z := O.value (n + p)
  let B := affineConst (O.segmentWord n p)
  have hid : B = 3 ^ p * d + g * z := by
    simpa [B, d, g, z] using firstCrossing_return_identity hmin hC
  have hg : 0 < g := by
    simpa [g] using firstCrossingMultiplicativeGap_pos hC
  have hz : 0 < z := O.value_pos (n + p)
  have hgz : 0 < g * z := Nat.mul_pos hg hz
  have hlow : 3 ^ p * d < B := by
    rw [hid]
    omega
  have hB : B ≤ p * 3 ^ (p - 1) := by
    simpa [B] using firstCrossing_affineConst_le_sharp hC
  have hchain : 3 ^ p * d < p * 3 ^ (p - 1) :=
    lt_of_lt_of_le hlow hB
  subst p
  have hpowPos : 0 < 3 ^ r := Nat.pow_pos (by omega)
  have hscaled :
      3 ^ r * (3 * d) < 3 ^ r * (r + 1) := by
    simpa [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hchain
  exact (Nat.mul_lt_mul_left hpowPos).mp hscaled

/-- first-crossing return gap自身は語長未満。 -/
theorem firstCrossingReturnGap_lt_length
    {O : OddOrbit} {n p : ℕ}
    (hmin : O.FutureMinimumAt n)
    (hC : FirstCrossingAt O n p) :
    firstCrossingReturnGap (O := O) n p < p := by
  have h := three_mul_firstCrossingReturnGap_lt_length hmin hC
  omega

/-- first-crossing return slack `p - 3*d`。 -/
def firstCrossingReturnSlack
    {O : OddOrbit} (n p : ℕ) : ℕ :=
  p - 3 * firstCrossingReturnGap (O := O) n p

/-- sharp return boundによりreturn slackは正。 -/
theorem firstCrossingReturnSlack_pos
    {O : OddOrbit} {n p : ℕ}
    (hmin : O.FutureMinimumAt n)
    (hC : FirstCrossingAt O n p) :
    0 < firstCrossingReturnSlack (O := O) n p := by
  unfold firstCrossingReturnSlack
  have h := three_mul_firstCrossingReturnGap_lt_length hmin hC
  omega

/--
return identityとsharp affine boundから得るslack評価。
`3*g*endpoint ≤ (p-3d)*3^p`。
-/
theorem three_mul_gap_mul_endpoint_le_returnSlack_threePow
    {O : OddOrbit} {n p : ℕ}
    (hmin : O.FutureMinimumAt n)
    (hC : FirstCrossingAt O n p) :
    3 * firstCrossingMultiplicativeGap (O := O) n p * O.value (n + p) ≤
      firstCrossingReturnSlack (O := O) n p * 3 ^ p := by
  let d := firstCrossingReturnGap (O := O) n p
  let g := firstCrossingMultiplicativeGap (O := O) n p
  let z := O.value (n + p)
  let B := affineConst (O.segmentWord n p)
  let s := firstCrossingReturnSlack (O := O) n p
  have hp : 0 < p := hC.length_pos
  have hsharp : 3 * d < p := by
    simpa [d] using three_mul_firstCrossingReturnGap_lt_length hmin hC
  have hps : p = 3 * d + s := by
    dsimp [s, firstCrossingReturnSlack, d]
    omega
  have hid : B = 3 ^ p * d + g * z := by
    simpa [B, d, g, z] using firstCrossing_return_identity hmin hC
  have hB : B ≤ p * 3 ^ (p - 1) := by
    simpa [B] using firstCrossing_affineConst_le_sharp hC
  have hp1 : 1 ≤ p := by
    omega
  have hpow : 3 * 3 ^ (p - 1) = 3 ^ p := by
    calc
      3 * 3 ^ (p - 1)
          = 3 ^ (p - 1) * 3 := by
              ring
      _ = 3 ^ ((p - 1) + 1) := by
            rw [pow_succ]
      _ = 3 ^ p := by
          rw [Nat.sub_add_cancel hp1]
  have hscaled : 3 * B ≤ p * 3 ^ p := by
    have h := Nat.mul_le_mul_left 3 hB
    calc
      3 * B ≤ 3 * (p * 3 ^ (p - 1)) := h
      _ = p * 3 ^ p := by
        rw [← hpow]
        ring
  have hscaled : 3 * B ≤ p * 3 ^ p := by
    have h := Nat.mul_le_mul_left 3 hB
    calc
      3 * B ≤ 3 * (p * 3 ^ (p - 1)) := h
      _ = p * 3 ^ p := by rw [← hpow]; ring
  have hsum :
      3 ^ p * (3 * d) + 3 * g * z ≤
        3 ^ p * (3 * d) + s * 3 ^ p := by
    calc
      3 ^ p * (3 * d) + 3 * g * z
          = 3 * B := by rw [hid]; ring
      _ ≤ p * 3 ^ p := hscaled
      _ = 3 ^ p * (3 * d) + s * 3 ^ p := by
          rw [hps]
          ring
  have hcancel : 3 * g * z ≤ s * 3 ^ p :=
    Nat.le_of_add_le_add_left hsum
  simpa [g, z, s] using hcancel

/--
Baker型gap入力とreturn slack評価を合成し、endpointをslack付き多項式で抑える。
-/
theorem firstCrossing_endpoint_le_returnSlack_polynomial
    (hGap : TwoThreeGapPolynomialBound) :
    ∃ K A : ℕ,
      ∀ O : OddOrbit,
      ∀ n p : ℕ,
        O.Unbounded →
        O.FutureMinimumAt n →
        FirstCrossingAt O n p →
        3 * O.value (n + p) ≤
          firstCrossingReturnSlack (O := O) n p *
            (K * (p + 1) ^ A) := by
  rcases hGap with ⟨K, A, _hK, hBaker⟩
  refine ⟨K, A, ?_⟩
  intro O n p hU hmin hC
  let H := twoSteps (O.segmentWord n p)
  let g := firstCrossingMultiplicativeGap (O := O) n p
  let s := firstCrossingReturnSlack (O := O) n p
  let z := O.value (n + p)
  have hp : 0 < p := hC.length_pos
  have hcontractWord :
      (O.segmentWord n p).Contracting :=
    hC.terminalContracting
  change
    3 ^ oddSteps (O.segmentWord n p) <
      2 ^ twoSteps (O.segmentWord n p)
    at hcontractWord
  have hcontract : 3 ^ p < 2 ^ H := by
    simpa [H, oddSteps] using hcontractWord
  have hg : 0 < g := by
    simpa [g] using firstCrossingMultiplicativeGap_pos hC
  have hBaker' : 3 ^ p ≤ K * (p + 1) ^ A * g := by
    simpa [H, g, firstCrossingMultiplicativeGap] using
      hBaker p H hp hcontract
  have hslack : 3 * g * z ≤ s * 3 ^ p := by
    simpa [g, s, z] using
      three_mul_gap_mul_endpoint_le_returnSlack_threePow hmin hC
  have hwithG :
      g * (3 * z) ≤ g * (s * (K * (p + 1) ^ A)) := by
    calc
      g * (3 * z) = 3 * g * z := by ring
      _ ≤ s * 3 ^ p := hslack
      _ ≤ s * (K * (p + 1) ^ A * g) :=
        Nat.mul_le_mul_left s hBaker'
      _ = g * (s * (K * (p + 1) ^ A)) := by ring
  have hcancel : 3 * z ≤ s * (K * (p + 1) ^ A) :=
    Nat.le_of_mul_le_mul_left hwithG hg
  simpa [z, s] using hcancel

/-- first-crossing full-windowの差depthもsharpに`3*2^depth < p`。 -/
theorem three_mul_twoPow_returnDepth_lt_length
    {O : OddOrbit}
    (F : MovingFirstCrossingData O)
    (j : ℕ) :
    3 * 2 ^ (movingFullWindowDifference F j).depth <
      F.crossingLength j := by
  let D := movingFullWindowDifference F j
  let p := F.crossingLength j
  have hgap :=
    three_mul_firstCrossingReturnGap_lt_length
      (F.minima.futureMinimum j)
      (F.crossing j)
  have huPos : 0 < D.oddPart := by
    rcases D.oddPart_odd with ⟨u, hu⟩
    omega
  have hpowLe :
      2 ^ D.depth ≤ 2 ^ D.depth * D.oddPart := by
    have hu : 1 ≤ D.oddPart := by omega
    simpa using Nat.mul_le_mul_left (2 ^ D.depth) hu
  have hdelta :
      firstCrossingReturnGap
          (O := O)
          (F.minima.index j)
          (F.crossingLength j) =
        2 ^ D.depth * D.oddPart := by
    unfold firstCrossingReturnGap
    have hd := D.difference
    dsimp [D, p] at hd ⊢
    omega
  rw [hdelta] at hgap
  have hthree := Nat.mul_le_mul_left 3 hpowLe
  exact lt_of_le_of_lt hthree hgap

/-- `2 ≤ p`なら`2^(p+1) ≤ 3^p`。 -/
private theorem twoPow_succ_le_threePow_of_two_le
    (p : ℕ) (hp : 2 ≤ p) :
    2 ^ (p + 1) ≤ 3 ^ p := by
  obtain ⟨q, hq⟩ : ∃ q : ℕ, p = q + 2 :=
    ⟨p - 2, by omega⟩
  subst p
  have hpow : 2 ^ q ≤ 3 ^ q := twoPow_le_threePow q
  calc
    2 ^ ((q + 2) + 1) = 8 * 2 ^ q := by
      rw [show q + 2 + 1 = 3 + q by omega, pow_add]
      norm_num
    _ ≤ 9 * 3 ^ q := Nat.mul_le_mul (by norm_num) hpow
    _ = 3 ^ (q + 2) := by
      rw [show q + 2 = 2 + q by omega, pow_add]
      norm_num

/--
Baker型gap入力のもとでは、十分長いfirst-crossingで
multiplicative gap `g = 2^H - 3^p` は語長`p`より大きい。
-/
theorem firstCrossing_multiplicativeGap_gt_length_eventually
    (hGap : TwoThreeGapPolynomialBound) :
    ∃ N : ℕ,
      ∀ O : OddOrbit,
      ∀ n p : ℕ,
        N ≤ p →
        FirstCrossingAt O n p →
        p < firstCrossingMultiplicativeGap (O := O) n p := by
  rcases hGap with ⟨K, A, _hK, hBaker⟩
  obtain ⟨Npoly, hNpoly⟩ := polynomialBelowTwoPower K (A + 1)
  let N := max Npoly 2
  refine ⟨N, ?_⟩
  intro O n p hpN hC
  have hp : 0 < p := hC.length_pos
  let H := twoSteps (O.segmentWord n p)
  let g := firstCrossingMultiplicativeGap (O := O) n p
  have hcontractWord :
      (O.segmentWord n p).Contracting :=
    hC.terminalContracting
  change
    3 ^ oddSteps (O.segmentWord n p) <
      2 ^ twoSteps (O.segmentWord n p)
    at hcontractWord
  have hcontract : 3 ^ p < 2 ^ H := by
    simpa [H, oddSteps] using hcontractWord
  have hgapPos : 0 < g := by
    simpa [g] using firstCrossingMultiplicativeGap_pos hC
  have hBaker' : 3 ^ p ≤ K * (p + 1) ^ A * g := by
    simpa [g, H, firstCrossingMultiplicativeGap] using
      hBaker p H hp hcontract
  have hpTwo : 2 ≤ p := by
    dsimp [N] at hpN
    omega
  have htwoThree : 2 ^ (p + 1) ≤ 3 ^ p :=
    twoPow_succ_le_threePow_of_two_le p hpTwo
  by_contra hnot
  have hgle : g ≤ p := Nat.le_of_not_gt hnot
  have hpolyGrow :
      K * (p + 1) ^ A * p ≤
        K * (p + 1) ^ (A + 1) := by
    have hpLe : p ≤ p + 1 := by omega
    have hmul := Nat.mul_le_mul_left (K * (p + 1) ^ A) hpLe
    simpa [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul
  have hthreePoly :
      3 ^ p ≤ K * (p + 1) ^ (A + 1) := by
    calc
      3 ^ p ≤ K * (p + 1) ^ A * g := hBaker'
      _ ≤ K * (p + 1) ^ A * p :=
        Nat.mul_le_mul_left (K * (p + 1) ^ A) hgle
      _ ≤ K * (p + 1) ^ (A + 1) := hpolyGrow
  have hpolyTwo :
      K * (p + 1) ^ (A + 1) < 2 ^ (p + 1) := by
    apply hNpoly p
    dsimp [N] at hpN
    omega
  have : 3 ^ p < 3 ^ p :=
    lt_of_le_of_lt hthreePoly (lt_of_lt_of_le hpolyTwo htwoThree)
  exact (Nat.lt_irrefl _) this

/--
十分長いfirst-crossingではactual return gapはmultiplicative gapより小さい。
small residue rigidityの整数版として後続で使う。
-/
theorem firstCrossing_returnGap_lt_multiplicativeGap_eventually
    (hGap : TwoThreeGapPolynomialBound) :
    ∃ N : ℕ,
      ∀ O : OddOrbit,
      ∀ n p : ℕ,
        O.Unbounded →
        O.FutureMinimumAt n →
        N ≤ p →
        FirstCrossingAt O n p →
        firstCrossingReturnGap (O := O) n p <
          firstCrossingMultiplicativeGap (O := O) n p := by
  obtain ⟨N, hN⟩ :=
    firstCrossing_multiplicativeGap_gt_length_eventually hGap
  refine ⟨N, ?_⟩
  intro O n p hU hmin hp hC
  have hd := firstCrossingReturnGap_lt_length hmin hC
  have hg := hN O n p hp hC
  exact lt_trans hd hg


/--
future-minimumから始まる一つのfirst-crossing actual returnを正本化したデータ。
negative shadowやterminal geometryをフィールドに持たない。
-/
structure FutureMinimumFirstCrossingReturnData (O : OddOrbit) where
  unbounded : O.Unbounded
  start : ℕ
  length : ℕ
  futureMinimum : O.FutureMinimumAt start
  crossing : FirstCrossingAt O start length

namespace FutureMinimumFirstCrossingReturnData

/-- moving first-crossingの一項をactual return正本へ忘却する。 -/
def ofMoving
    {O : OddOrbit}
    (F : MovingFirstCrossingData O)
    (j : ℕ) :
    FutureMinimumFirstCrossingReturnData O :=
  { unbounded := F.unbounded
    start := F.minima.index j
    length := F.crossingLength j
    futureMinimum := F.minima.futureMinimum j
    crossing := F.crossing j }

/-- first-crossing exponent word。 -/
def word
    {O : OddOrbit}
    (D : FutureMinimumFirstCrossingReturnData O) : ExpWord :=
  O.segmentWord D.start D.length

/-- first-crossing開始値。 -/
def startValue
    {O : OddOrbit}
    (D : FutureMinimumFirstCrossingReturnData O) : ℕ :=
  O.value D.start

/-- first-crossing終点値。 -/
def endpointValue
    {O : OddOrbit}
    (D : FutureMinimumFirstCrossingReturnData O) : ℕ :=
  O.value (D.start + D.length)

/-- actual return gap。 -/
def returnGap
    {O : OddOrbit}
    (D : FutureMinimumFirstCrossingReturnData O) : ℕ :=
  firstCrossingReturnGap (O := O) D.start D.length

/-- first-crossing総2進指数。 -/
def totalExponent
    {O : OddOrbit}
    (D : FutureMinimumFirstCrossingReturnData O) : ℕ :=
  twoSteps D.word

/-- multiplicative gap `2^H-3^p`。 -/
def multiplicativeGap
    {O : OddOrbit}
    (D : FutureMinimumFirstCrossingReturnData O) : ℕ :=
  firstCrossingMultiplicativeGap (O := O) D.start D.length

/-- affine定数。 -/
def affine
    {O : OddOrbit}
    (D : FutureMinimumFirstCrossingReturnData O) : ℕ :=
  affineConst D.word

/-- return gapは正。 -/
theorem returnGap_pos
    {O : OddOrbit}
    (D : FutureMinimumFirstCrossingReturnData O) :
    0 < D.returnGap := by
  exact firstCrossingReturnGap_pos D.unbounded D.futureMinimum D.crossing

/-- multiplicative gapは正。 -/
theorem multiplicativeGap_pos
    {O : OddOrbit}
    (D : FutureMinimumFirstCrossingReturnData O) :
    0 < D.multiplicativeGap := by
  exact firstCrossingMultiplicativeGap_pos D.crossing

/-- 正本return identity。 -/
theorem return_identity
    {O : OddOrbit}
    (D : FutureMinimumFirstCrossingReturnData O) :
    D.affine =
      3 ^ D.length * D.returnGap +
        D.multiplicativeGap * D.endpointValue := by
  simpa [affine, word, returnGap, multiplicativeGap, endpointValue] using
    firstCrossing_return_identity D.futureMinimum D.crossing

/-- sharp return gap bound。 -/
theorem three_mul_returnGap_lt_length
    {O : OddOrbit}
    (D : FutureMinimumFirstCrossingReturnData O) :
    3 * D.returnGap < D.length := by
  exact three_mul_firstCrossingReturnGap_lt_length
    D.futureMinimum D.crossing

end FutureMinimumFirstCrossingReturnData

/--
局所prefix pairの`7/4` boundを除算なしで表した純整数補題。
`e=1`でも`e≥2`でも、連続二prefixがともにexpandingなら成立する。
-/
theorem prefixPair_seven_fourths_bound
    {j H e : ℕ}
    (he : 0 < e)
    (h0 : 2 ^ H < 3 ^ j)
    (h1 : 2 ^ (H + e) < 3 ^ (j + 1)) :
    4 * (3 * 2 ^ H + 2 ^ (H + e)) <
      7 * 3 ^ (j + 1) := by
  by_cases heOne : e = 1
  · subst e
    have h20 : 20 * 2 ^ H < 20 * 3 ^ j :=
      (Nat.mul_lt_mul_left (by omega : 0 < 20)).2 h0
    have hpos : 0 < 3 ^ j :=
      Nat.pow_pos (by omega)
    simp only [pow_succ]
    nlinarith
  · have heTwo : 2 ≤ e := by
      omega
    have hpowFour : 4 ≤ 2 ^ e := by
      simpa using
        Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) heTwo
    have hA : 4 * 2 ^ H ≤ 2 ^ (H + e) := by
      rw [pow_add]
      simpa [Nat.mul_comm] using
        Nat.mul_le_mul_left (2 ^ H) hpowFour
    have hA3 : 4 * 2 ^ H < 3 * 3 ^ j := by
      exact lt_of_le_of_lt hA
        (by simpa [pow_succ, Nat.mul_comm] using h1)
    have hB : 4 * 2 ^ (H + e) < 12 * 3 ^ j := by
      calc
        4 * 2 ^ (H + e) < 4 * 3 ^ (j + 1) := by
          exact (Nat.mul_lt_mul_left (by omega : 0 < 4)).2 h1
        _ = 12 * 3 ^ j := by
          rw [pow_succ]
          ring
    nlinarith


/--
actual first-crossingの連続二proper prefixに対する`7/4` bound。
除算を避けた整数形で保存する。
-/
theorem firstCrossing_prefixPair_seven_fourths_bound
    {O : OddOrbit} {n p j : ℕ}
    (hC : FirstCrossingAt O n p)
    (hj : 0 < j)
    (hnext : j + 1 < p) :
    4 *
        (3 * 2 ^ O.windowTwoSteps n j +
          2 ^ (O.windowTwoSteps n j + O.exponent (n + j))) <
      7 * 3 ^ (j + 1) := by
  have hjp : j < p := by omega
  have hE0 := hC.properExpanding j hj (by simpa using hjp)
  have hE1 := hC.properExpanding (j + 1) (by omega) (by simpa using hnext)
  have hjle : j ≤ p := Nat.le_of_lt hjp
  have hj1le : j + 1 ≤ p := Nat.le_of_lt hnext
  rw [O.segmentWord_take_of_le hjle] at hE0
  rw [O.segmentWord_take_of_le hj1le] at hE1
  have h0 : 2 ^ O.windowTwoSteps n j < 3 ^ j := by
    simpa [OddOrbit.windowTwoSteps, Expanding, oddSteps] using hE0
  have h1raw :
      2 ^ O.windowTwoSteps n (j + 1) < 3 ^ (j + 1) := by
    simpa [OddOrbit.windowTwoSteps, Expanding, oddSteps] using hE1
  have hlast := O.windowTwoSteps_succ_last n j
  have h1 :
      2 ^ (O.windowTwoSteps n j + O.exponent (n + j)) <
        3 ^ (j + 1) := by
    rw [hlast] at h1raw
    exact h1raw
  exact prefixPair_seven_fourths_bound
    (O.exponent_pos (n + j)) h0 h1

end CollatzSecondLayer3
