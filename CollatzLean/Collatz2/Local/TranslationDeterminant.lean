import CollatzLean.Collatz2.Core.TranslationPath
import CollatzLean.Collatz2.Local.SuffixDeterminantProfile

/-!
# Collatz2 Local: translation path と determinant integral

`B = affineConst w` は determinant sign profile と独立の量ではない。
translation path を prefix / suffix の signed determinant に沿って積分すると、exact に

  `3*B - p*A`

および

  `p*C - 3*B`

が得られる。

有限和を新しい primitive object にせず、suffix 側は先頭から、prefix 側は末尾から
再帰的に weighted integral を作る。
-/

namespace Collatz2
namespace Word

/-! ## Suffix determinant integral（suffix 側 determinant 積分） -/

/--
Prefix two-depth を重みとして全 nonempty suffix determinant を積分する。

`e :: w` では whole determinant を weight `1` で取り、tail 側の全 weight を
`2^e` 倍する。
-/
def suffixDeterminantIntegral : Word → ℤ
  | [] => 0
  | e :: w =>
      (AffineTransfer.ofWord (e :: w)).determinant +
        ((2 : ℤ) ^ e) * suffixDeterminantIntegral w

/--
Suffix 側の exact identity：

  `suffixIntegral(w) = 3*B(w) - p(w)*2^H(w)`。
-/
theorem suffixDeterminantIntegral_eq
    (w : Word) :
    suffixDeterminantIntegral w =
      3 * (affineConst w : ℤ) -
        (oddSteps w : ℤ) * ((2 : ℤ) ^ twoSteps w) := by
  induction w with
  | nil =>
      simp [suffixDeterminantIntegral, affineConst, oddSteps, twoSteps]
  | cons e w ih =>
      rw [suffixDeterminantIntegral, ih]
      rw [AffineTransfer.determinant_ofWord]
      simp only [affineConst_cons, oddSteps_cons, twoSteps_cons]
      push_cast
      rw [pow_add, pow_succ]
      ring

/-- 全 suffix が negative である profile は tail にも継承される。 -/
theorem AllSuffixesNegativeDeterminant.tail
    {e : ℕ} {w : Word}
    (h : AllSuffixesNegativeDeterminant (e :: w)) :
    AllSuffixesNegativeDeterminant w := by
  intro k hk
  have h' := h (k + 1) (by simp; omega)
  simpa [suffixDeterminant] using h'

/-- nonempty かつ全 suffix が negative なら、weighted integral は負になる。 -/
theorem suffixDeterminantIntegral_neg_of_allSuffixesNegative
    {w : Word}
    (hne : w ≠ [])
    (hAll : AllSuffixesNegativeDeterminant w) :
    suffixDeterminantIntegral w < 0 := by
  induction w with
  | nil =>
      contradiction
  | cons e w ih =>
      have hwhole : (AffineTransfer.ofWord (e :: w)).determinant < 0 := by
        have h0 := hAll 0 (by simp)
        simpa [suffixDeterminant] using h0
      by_cases hw : w = []
      · subst w
        simp only [suffixDeterminantIntegral, mul_zero, add_zero, gt_iff_lt] at hwhole ⊢
        exact hwhole
      · have htail : AllSuffixesNegativeDeterminant w := hAll.tail
        have hi : suffixDeterminantIntegral w < 0 := ih hw htail
        have hpow : (0 : ℤ) < (2 : ℤ) ^ e := by positivity
        have hscaled :
            ((2 : ℤ) ^ e) * suffixDeterminantIntegral w < 0 :=
          mul_neg_of_pos_of_neg hpow hi
        simp only [suffixDeterminantIntegral]
        linarith

/--
全 suffix が contracting なら sharp な translation budget

  `3*B < p*2^H`

が成り立つ。これは exact suffix determinant integral から一行で従う符号系である。
-/
theorem AllSuffixesContracting.three_mul_affineConst_lt_oddSteps_mul_twoPow
    {w : Word}
    (hAll : AllSuffixesContracting w)
    (hne : w ≠ []) :
    3 * affineConst w < oddSteps w * 2 ^ twoSteps w := by
  have hi : suffixDeterminantIntegral w < 0 :=
    suffixDeterminantIntegral_neg_of_allSuffixesNegative hne hAll
  have hEq := suffixDeterminantIntegral_eq w
  have hz :
      (3 : ℤ) * (affineConst w : ℤ) <
        (oddSteps w : ℤ) * ((2 : ℤ) ^ twoSteps w) := by
    linarith
  exact_mod_cast hz

/-! ## Proper-prefix determinant integral（proper-prefix 側 determinant 積分） -/

/--
proper-prefix integral の reverse recursion。

`w = u ++ [e]` なら、新しい proper prefix は `u` であり、それ以前の全 prefix weight には
`3` が一因子追加される。従って

  `J(u ++ [e]) = 3 * (J(u) + determinant(u))`。
-/
def prefixDeterminantIntegralRev : Word → ℤ
  | [] => 0
  | _e :: r =>
      3 *
        (prefixDeterminantIntegralRev r +
          (AffineTransfer.ofWord r.reverse).determinant)

/-- word の proper-prefix integral。 -/
def prefixDeterminantIntegral (w : Word) : ℤ :=
  prefixDeterminantIntegralRev w.reverse

/-- reverse recursion で定義した proper-prefix integral の閉形式。 -/
theorem prefixDeterminantIntegralRev_eq
    (r : Word) :
    prefixDeterminantIntegralRev r =
      (oddSteps r : ℤ) * ((3 : ℤ) ^ oddSteps r) -
        3 * (affineConst r.reverse : ℤ) := by
  induction r with
  | nil =>
      simp [prefixDeterminantIntegralRev, oddSteps]
  | cons e r ih =>
      rw [prefixDeterminantIntegralRev, ih]
      rw [AffineTransfer.determinant_ofWord]
      have hB := affineConst_append r.reverse ([e] : Word)
      have hBZ0 :
          (affineConst (r.reverse ++ [e]) : ℤ) =
            ((3 : ℤ) ^ oddSteps ([e] : Word)) *
                (affineConst r.reverse : ℤ) +
              ((2 : ℤ) ^ twoSteps r.reverse) *
                (affineConst ([e] : Word) : ℤ) := by
        exact_mod_cast hB
      have hBZ :
          (affineConst (r.reverse ++ [e]) : ℤ) =
            3 * (affineConst r.reverse : ℤ) +
              ((2 : ℤ) ^ twoSteps r) := by
        simpa [oddSteps, twoSteps, affineConst] using hBZ0
      simp only [List.reverse_cons, oddSteps_cons]
      rw [hBZ]
      simp only [oddSteps, List.length_reverse, twoSteps,
       List.sum_reverse, Nat.cast_add, Nat.cast_one]
      rw [pow_succ]
      ring

/--
Prefix 側の exact identity：

  `prefixIntegral(w) = p(w)*3^p(w) - 3*B(w)`。
-/
theorem prefixDeterminantIntegral_eq
    (w : Word) :
    prefixDeterminantIntegral w =
      (oddSteps w : ℤ) * ((3 : ℤ) ^ oddSteps w) -
        3 * (affineConst w : ℤ) := by
  unfold prefixDeterminantIntegral
  rw [prefixDeterminantIntegralRev_eq]
  simp [oddSteps]

/--
reverse recursion 上で proper prefix がすべて positive なら integral は非負になる。
さらに記号数が2以上なら strict に正になる。
-/
private theorem prefixDeterminantIntegralRev_nonneg_and_pos
    (r : Word)
    (hP : ProperPrefixesPositiveDeterminant r.reverse) :
    0 ≤ prefixDeterminantIntegralRev r ∧
      (1 < r.length → 0 < prefixDeterminantIntegralRev r) := by
  induction r with
  | nil =>
      simp [prefixDeterminantIntegralRev]
  | cons e r ih =>
      by_cases hr : r = []
      · subst r
        simp [prefixDeterminantIntegralRev,
          AffineTransfer.determinant,
          AffineTransfer.ofWord]
      · have hPr : ProperPrefixesPositiveDeterminant r.reverse := by
          intro k hkPos hkLt
          have hkLe : k ≤ r.reverse.length :=
            Nat.le_of_lt hkLt
          have hlen :
              r.reverse.length < (e :: r).reverse.length := by
            simp
          have hOrig :=
            hP k hkPos (lt_trans hkLt hlen)
          have htake :
              List.take k (e :: r).reverse =
                List.take k r.reverse := by
            rw [List.reverse_cons]
            simp [List.take_append_of_le_length hkLe]
          rw [htake] at hOrig
          exact hOrig
        have ihData := ih hPr
        have hdet :
            0 < (AffineTransfer.ofWord r.reverse).determinant := by
          have hkPos : 0 < r.reverse.length := by
            simpa using List.length_pos_iff.mpr hr
          have hlen :
              r.reverse.length < (e :: r).reverse.length := by
            simp
          have hOrig :=
            hP r.reverse.length hkPos hlen
          have htake :
              List.take r.reverse.length (e :: r).reverse =
                r.reverse := by
            rw [List.reverse_cons]
            simp
          rw [htake] at hOrig
          change
            0 < (AffineTransfer.ofWord r.reverse).determinant
            at hOrig
          exact hOrig
        constructor
        · simp only [prefixDeterminantIntegralRev]
          have hsum :
              0 <
                prefixDeterminantIntegralRev r +
                  (AffineTransfer.ofWord r.reverse).determinant := by
            linarith [ihData.1, hdet]
          linarith
        · intro hlen
          simp only [prefixDeterminantIntegralRev]
          have hsum :
              0 <
                prefixDeterminantIntegralRev r +
                  (AffineTransfer.ofWord r.reverse).determinant := by
            linarith [ihData.1, hdet]
          linarith

/-- proper-prefix が positive な profile なら weighted prefix integral は非負。 -/
theorem prefixDeterminantIntegral_nonneg_of_properPrefixesPositive
    {w : Word}
    (hP : ProperPrefixesPositiveDeterminant w) :
    0 ≤ prefixDeterminantIntegral w := by
  unfold prefixDeterminantIntegral
  have h := prefixDeterminantIntegralRev_nonneg_and_pos w.reverse (by
    simpa using hP)
  exact h.1

/-- 記号数が2以上なら weighted proper-prefix integral は正。 -/
theorem prefixDeterminantIntegral_pos_of_properPrefixesPositive
    {w : Word}
    (hP : ProperPrefixesPositiveDeterminant w)
    (hlen : 1 < w.length) :
    0 < prefixDeterminantIntegral w := by
  unfold prefixDeterminantIntegral
  have h := prefixDeterminantIntegralRev_nonneg_and_pos w.reverse (by
    simpa using hP)
  apply h.2
  simpa using hlen

/--
proper prefix がすべて positive なら dual translation budget

  `3*B ≤ p*3^p`

が従う。
-/
theorem ProperPrefixesPositiveDeterminant.three_mul_affineConst_le_oddSteps_mul_threePow
    {w : Word}
    (hP : ProperPrefixesPositiveDeterminant w) :
    3 * affineConst w ≤ oddSteps w * 3 ^ oddSteps w := by
  have hi : 0 ≤ prefixDeterminantIntegral w :=
    prefixDeterminantIntegral_nonneg_of_properPrefixesPositive hP
  have hEq := prefixDeterminantIntegral_eq w
  have hz :
      (3 : ℤ) * (affineConst w : ℤ) ≤
        (oddSteps w : ℤ) * ((3 : ℤ) ^ oddSteps w) := by
    linarith
  exact_mod_cast hz

/-- genuine な proper prefix が存在すれば dual translation budget は strict。 -/
theorem ProperPrefixesPositiveDeterminant.three_mul_affineConst_lt_oddSteps_mul_threePow
    {w : Word}
    (hP : ProperPrefixesPositiveDeterminant w)
    (hlen : 1 < w.length) :
    3 * affineConst w < oddSteps w * 3 ^ oddSteps w := by
  have hi : 0 < prefixDeterminantIntegral w :=
    prefixDeterminantIntegral_pos_of_properPrefixesPositive hP hlen
  have hEq := prefixDeterminantIntegral_eq w
  have hz :
      (3 : ℤ) * (affineConst w : ℤ) <
        (oddSteps w : ℤ) * ((3 : ℤ) ^ oddSteps w) := by
    linarith
  exact_mod_cast hz

/-- First crossing は常に weak prefix budget を満たす。 -/
theorem FirstCrossing.three_mul_affineConst_le_oddSteps_mul_threePow
    {w : Word}
    (hF : FirstCrossing w) :
    3 * affineConst w ≤ oddSteps w * 3 ^ oddSteps w :=
  hF.properPositive.three_mul_affineConst_le_oddSteps_mul_threePow

/-- 長さ2以上の First crossing は strict prefix budget を満たす。 -/
theorem FirstCrossing.three_mul_affineConst_lt_oddSteps_mul_threePow
    {w : Word}
    (hF : FirstCrossing w)
    (hlen : 1 < w.length) :
    3 * affineConst w < oddSteps w * 3 ^ oddSteps w :=
  hF.properPositive.three_mul_affineConst_lt_oddSteps_mul_threePow hlen

end Word
end Collatz2
