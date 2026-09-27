import CollatzLean.Collatz3.CSTCarry.WrapExceptions
import CollatzLean.Collatz3.Critical.RoofAnchor
import Mathlib.Data.Nat.GCD.Basic

/-!
# Collatz3 CSTCarry: critical row envelope と 2-adic 基礎

actual first-passage Ferrers rows を CSTCarry 側で使うために必要な、
最小限の row 条件だけを pure predicate として切り出す。

row list は terminal 側から initial 側へ読むため、幅 `P+1` では先頭 row が
critical index `P` に対応する。

ここで保存するのは次だけ。

* index `r` の boundary は `beattyIndex r` 以下、
* actual depth は `r` 以上、
* actual depth は row list に沿って strict に下降する。

actual `Critical.Profile` からこの predicate への exact bridge は別ファイルの責務とする。
このファイルでは未証明 bridge を仮定しない。
-/

namespace Collatz3
namespace CSTCarry

open Critical

/--
terminal-to-initial row list に対する critical envelope。

幅 `P+1` の先頭 row は critical index `P` に対応する。
-/
def CriticalRowEnvelope : ℕ → List FerrersRow → Prop
  | 0, rows => rows = []
  | _P + 1, [] => False
  | P + 1, R :: Rs =>
      R.boundary ≤ beattyIndex P ∧
      P ≤ R.actual ∧
      CriticalRowEnvelope P Rs

/-- row list を terminal 側から読むと actual depth は strict に下降する。 -/
def ActualStrictDescending : List FerrersRow → Prop
  | [] => True
  | [_] => True
  | R :: Q :: Rs =>
      Q.actual < R.actual ∧ ActualStrictDescending (Q :: Rs)

/-- actual first-passage row list に必要な二条件を束ねた薄い predicate。 -/
def CriticalCarryRows
    (P : ℕ)
    (rows : List FerrersRow) : Prop :=
  CriticalRowEnvelope P rows ∧ ActualStrictDescending rows

/-- critical envelope が持つ weighted defect の幅だけによる最大値。 -/
def criticalWeightedDefectUpper : ℕ → ℕ
  | 0 => 0
  | P + 1 =>
      3 * criticalWeightedDefectUpper P +
        (2 ^ beattyIndex P - 2 ^ P)

/-- `2^a` が割るが `2^(a+1)` は割らない、という exact 2-adic condition。 -/
def ExactTwoPower (a n : ℕ) : Prop :=
  2 ^ a ∣ n ∧ ¬ 2 ^ (a + 1) ∣ n

/-- 小さい指数の 2 冪は大きい指数の 2 冪を割る。 -/
theorem twoPow_dvd_twoPow_of_le
    {a b : ℕ}
    (hab : a ≤ b) :
    2 ^ a ∣ 2 ^ b := by
  refine ⟨2 ^ (b - a), ?_⟩
  have hb : b = a + (b - a) := by
    omega
  rw [hb, pow_add]
  simp

/-- exponent が 2 以上なら `2^n` は 4 の倍数。 -/
theorem four_dvd_twoPow
    {n : ℕ}
    (hn : 2 ≤ n) :
    4 ∣ 2 ^ n := by
  have h := twoPow_dvd_twoPow_of_le (a := 2) (b := n) hn
  simpa using h

namespace FerrersRow

/-- Ferrers row defect は常に `2^actual` の倍数。 -/
theorem twoPow_actual_dvd_defect
    (R : FerrersRow) :
    2 ^ R.actual ∣ R.defect := by
  unfold defect
  have hPow : 2 ^ R.actual ∣ 2 ^ R.boundary :=
    twoPow_dvd_twoPow_of_le R.actual_le_boundary
  exact Nat.dvd_sub hPow dvd_rfl

/-- actual depth が 2 以上なら row defect は 4 の倍数。 -/
theorem four_dvd_defect_of_two_le_actual
    (R : FerrersRow)
    (hActual : 2 ≤ R.actual) :
    4 ∣ R.defect := by
  exact (four_dvd_twoPow hActual).trans R.twoPow_actual_dvd_defect

/--
非零 Ferrers defect の exact 2-adic exponent は `actual`。

`boundary > actual` のとき
`2^boundary - 2^actual` は `2^actual * odd` になることを
factorization library を使わず divisibility だけで表す。
-/
theorem exactTwoPower_defect_of_ne_zero
    (R : FerrersRow)
    (hNonzero : R.defect ≠ 0) :
    ExactTwoPower R.actual R.defect := by
  have hStrict : R.actual < R.boundary := by
    by_contra hNot
    have hEq : R.actual = R.boundary := by
      apply Nat.le_antisymm
      · exact R.actual_le_boundary
      · exact Nat.le_of_not_gt hNot
    have hZero : R.defect = 0 := by
      simp [defect, hEq]
    exact hNonzero hZero
  refine ⟨R.twoPow_actual_dvd_defect, ?_⟩
  intro hHighDefect
  have hHighBoundary :
      2 ^ (R.actual + 1) ∣ 2 ^ R.boundary :=
    twoPow_dvd_twoPow_of_le (by omega)
  have hHighActualRaw :
      2 ^ (R.actual + 1) ∣ 2 ^ R.boundary - R.defect :=
    Nat.dvd_sub hHighBoundary hHighDefect
  have hPowLe : 2 ^ R.actual ≤ 2 ^ R.boundary :=
    Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) R.actual_le_boundary
  have hSub :
      2 ^ R.boundary - R.defect = 2 ^ R.actual := by
    unfold defect
    omega
  rw [hSub] at hHighActualRaw
  have hLe :
      2 ^ (R.actual + 1) ≤ 2 ^ R.actual :=
    Nat.le_of_dvd (pow_pos (by decide : 0 < (2 : ℕ)) R.actual)
      hHighActualRaw
  have hLt :
      2 ^ R.actual < 2 ^ (R.actual + 1) := by
    exact (Nat.pow_lt_pow_iff_right (by decide : 1 < (2 : ℕ))).2 (by omega)
  omega

/-- critical row index `r` の envelope から defect の pointwise 上界を得る。 -/
theorem defect_le_criticalBound
    (R : FerrersRow)
    {r : ℕ}
    (hBoundary : R.boundary ≤ beattyIndex r)
    (hActual : r ≤ R.actual) :
    R.defect ≤ 2 ^ beattyIndex r - 2 ^ r := by
  have hBoundaryPow :
      2 ^ R.boundary ≤ 2 ^ beattyIndex r :=
    Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hBoundary
  have hActualPow :
      2 ^ r ≤ 2 ^ R.actual :=
    Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hActual
  unfold defect
  omega

end FerrersRow

/-- envelope の row 数は width に exact に一致する。 -/
theorem CriticalRowEnvelope.length_eq
    {P : ℕ}
    {rows : List FerrersRow}
    (h : CriticalRowEnvelope P rows) :
    rows.length = P := by
  induction P generalizing rows with
  | zero =>
      simp only [CriticalRowEnvelope] at h
      subst rows
      rfl
  | succ P ih =>
      cases rows with
      | nil =>
          simp [CriticalRowEnvelope] at h
      | cons R Rs =>
          simp only [CriticalRowEnvelope] at h
          have hTail := ih h.2.2
          simp [hTail]

/-- envelope から weighted defect の global 上界を得る。 -/
theorem CriticalRowEnvelope.weightedDefect_le_upper
    {P : ℕ}
    {rows : List FerrersRow}
    (h : CriticalRowEnvelope P rows) :
    ferrersWeightedDefect rows ≤ criticalWeightedDefectUpper P := by
  induction P generalizing rows with
  | zero =>
      simp only [CriticalRowEnvelope] at h
      subst rows
      simp [criticalWeightedDefectUpper]
  | succ P ih =>
      cases rows with
      | nil =>
          simp [CriticalRowEnvelope] at h
      | cons R Rs =>
          simp only [CriticalRowEnvelope] at h
          have hRow :
              R.defect ≤ 2 ^ beattyIndex P - 2 ^ P :=
            R.defect_le_criticalBound h.1 h.2.1
          have hTail := ih h.2.2
          simp only [ferrersWeightedDefect_cons, criticalWeightedDefectUpper]
          omega

/--
critical envelope の全 row defect は 4 の倍数なので、weighted defect 全体も 4 の倍数。

index `0,1` の row は envelope だけで defect `0` に強制される。
index `r≥2` では `actual≥r≥2` から 4 divisibility が出る。
-/
theorem CriticalRowEnvelope.four_dvd_weightedDefect
    {P : ℕ}
    {rows : List FerrersRow}
    (h : CriticalRowEnvelope P rows) :
    4 ∣ ferrersWeightedDefect rows := by
  induction P generalizing rows with
  | zero =>
      simp only [CriticalRowEnvelope] at h
      subst rows
      simp
  | succ P ih =>
      cases rows with
      | nil =>
          simp [CriticalRowEnvelope] at h
      | cons R Rs =>
          simp only [CriticalRowEnvelope] at h
          have hTail : 4 ∣ ferrersWeightedDefect Rs :=
            ih h.2.2
          have hRow : 4 ∣ R.defect := by
            by_cases hP0 : P = 0
            · subst P
              have hbLe : R.boundary ≤ 0 := by
                simpa using h.1
              have hb : R.boundary = 0 := by
                omega
              have ha : R.actual = 0 := by
                have hActualLe : R.actual ≤ R.boundary :=
                  R.actual_le_boundary
                omega
              simp [FerrersRow.defect, hb, ha]
            · by_cases hP1 : P = 1
              · subst P
                have hBeattyOne : beattyIndex 1 = 1 := by
                  apply Nat.le_antisymm
                  · apply beattyIndex_le_of_upper
                    norm_num
                  · have hStep :
                        beattyIndex 0 < beattyIndex 1 := by
                      simp only [beattyIndex_zero, beattyIndex_one, zero_lt_one]
                    rw [beattyIndex_zero] at hStep
                    omega
                have hbLe : R.boundary ≤ 1 := by
                  rw [← hBeattyOne]
                  exact h.1
                have haGe : 1 ≤ R.actual :=
                  h.2.1
                have haLe : R.actual ≤ R.boundary :=
                  R.actual_le_boundary
                have ha : R.actual = 1 := by
                  omega
                have hb : R.boundary = 1 := by
                  omega
                simp [FerrersRow.defect, hb, ha]
              · have hTwo : 2 ≤ P := by
                  omega
                exact R.four_dvd_defect_of_two_le_actual
                  (le_trans hTwo h.2.1)
          simp only [ferrersWeightedDefect_cons]
          exact Nat.dvd_add hRow (dvd_mul_of_dvd_right hTail 3)

/-- critical envelope なら全 row boundary は critical terminal bit width より手前。 -/
theorem CriticalRowEnvelope.insideBitWidth
    {P : ℕ}
    {rows : List FerrersRow}
    (h : CriticalRowEnvelope P rows) :
    RowsInsideBitWidth (criticalTwoDepth P) rows := by
  induction P generalizing rows with
  | zero =>
      simp only [CriticalRowEnvelope] at h
      subst rows
      intro R hR
      simp at hR
  | succ P ih =>
      cases rows with
      | nil =>
          simp [CriticalRowEnvelope] at h
      | cons R Rs =>
          simp only [CriticalRowEnvelope] at h
          have hTail := ih h.2.2
          intro Q hQ
          simp only [List.mem_cons] at hQ
          rcases hQ with rfl | hQ
          · have hBeatty := beattyIndex_lt_succ P
            unfold criticalTwoDepth
            omega
          · have hOld := hTail Q hQ
            have hBeatty := beattyIndex_lt_succ P
            unfold criticalTwoDepth at hOld ⊢
            omega

/-- exact 2-adic condition は odd factor `3` を掛けても保存される。 -/
theorem ExactTwoPower.mul_three
    {a n : ℕ}
    (h : ExactTwoPower a n) :
    ExactTwoPower a (3 * n) := by
  refine ⟨dvd_mul_of_dvd_right h.1 3, ?_⟩
  intro hHigh
  have hCoprime : Nat.Coprime (2 ^ (a + 1)) 3 := by
    exact (by decide : Nat.Coprime 2 3).pow_left (a + 1)
  have hBack : 2 ^ (a + 1) ∣ n :=
    (hCoprime.dvd_mul_left).1 hHigh
  exact h.2 hBack

/--
`y` の exact exponent が `a` で、`x` が一段高い `2^(a+1)` で割れるなら、
`x+y` の exact exponent も `a`。
-/
theorem exactTwoPower_add_of_high_dvd
    {a x y : ℕ}
    (hx : 2 ^ (a + 1) ∣ x)
    (hy : ExactTwoPower a y) :
    ExactTwoPower a (x + y) := by
  have hLowHigh : 2 ^ a ∣ 2 ^ (a + 1) :=
    twoPow_dvd_twoPow_of_le (by omega)
  have hLowX : 2 ^ a ∣ x := hLowHigh.trans hx
  refine ⟨Nat.dvd_add hLowX hy.1, ?_⟩
  intro hHighSum
  have hHighY : 2 ^ (a + 1) ∣ (x + y) - x :=
    Nat.dvd_sub hHighSum hx
  have : 2 ^ (a + 1) ∣ y := by
    simpa using hHighY
  exact hy.2 this

/--
strict descending actual depth の weighted defect は 0 か、
先頭 actual 以下のどこかに exact 2-adic exponent を持つ。
-/
theorem weightedDefect_zero_or_exactTwoPower
    {rows : List FerrersRow}
    (hDesc : ActualStrictDescending rows) :
    ferrersWeightedDefect rows = 0 ∨
      ∃ a : ℕ,
        a ≤ (match rows with
          | [] => 0
          | R :: _ => R.actual) ∧
        ExactTwoPower a (ferrersWeightedDefect rows) := by
  revert hDesc
  induction rows with
  | nil =>
      intro hDesc
      simp [ferrersWeightedDefect]
  | cons R Rs ih =>
      intro hDesc
      cases Rs with
      | nil =>
          by_cases hZero : R.defect = 0
          · left
            simp [ferrersWeightedDefect, hZero]
          · right
            refine ⟨R.actual, by simp, ?_⟩
            simpa only [ferrersWeightedDefect_cons, ferrersWeightedDefect_nil,
                         mul_zero, add_zero] using
              R.exactTwoPower_defect_of_ne_zero hZero
      | cons Q Qs =>
          simp only [ActualStrictDescending] at hDesc
          have hTailDesc : ActualStrictDescending (Q :: Qs) := hDesc.2
          have hTail := ih hTailDesc
          rcases hTail with hTailZero | hTailExact
          · by_cases hRowZero : R.defect = 0
            · left
              calc
                ferrersWeightedDefect (R :: Q :: Qs) =
                    R.defect + 3 * ferrersWeightedDefect (Q :: Qs) := rfl
                _ = 0 := by
                  rw [hRowZero, hTailZero]
            · right
              refine ⟨R.actual, by simp, ?_⟩
              have hExact := R.exactTwoPower_defect_of_ne_zero hRowZero
              simpa only [ferrersWeightedDefect_cons, hTailZero, mul_zero, add_zero] using hExact
          · rcases hTailExact with ⟨a, haQ, hExactTail⟩
            have haR : a + 1 ≤ R.actual := by
              simp at haQ
              omega
            have hHeadPow : 2 ^ R.actual ∣ R.defect :=
              R.twoPow_actual_dvd_defect
            have hHighHead : 2 ^ (a + 1) ∣ R.defect :=
              (twoPow_dvd_twoPow_of_le haR).trans hHeadPow
            have hExactThree :
                ExactTwoPower a (3 * ferrersWeightedDefect (Q :: Qs)) :=
              hExactTail.mul_three
            right
            refine ⟨a, ?_, ?_⟩
            · simp
              omega
            · simpa only [ferrersWeightedDefect_cons] using
                exactTwoPower_add_of_high_dvd hHighHead hExactThree

/--
strict descending actual depth と H-bit range の下で、positive weighted defect は
`2^H` の倍数にはならない。
-/
theorem weightedDefect_not_modulus_dvd_of_pos
    {H : ℕ}
    {rows : List FerrersRow}
    (hDesc : ActualStrictDescending rows)
    (hInside : RowsInsideBitWidth H rows)
    (hPos : 0 < ferrersWeightedDefect rows) :
    ¬ 2 ^ H ∣ ferrersWeightedDefect rows := by
  have hNonempty : rows ≠ [] := by
    intro hNil
    subst rows
    simp at hPos
  cases rows with
  | nil => contradiction
  | cons R Rs =>
      have hExactRaw := weightedDefect_zero_or_exactTwoPower hDesc
      rcases hExactRaw with hZero | hExact
      · omega
      · rcases hExact with ⟨a, haR, hTwo⟩
        simp only at haR
        have hRInside : R.boundary < H := hInside R (by simp)
        have hActualLt : R.actual < H :=
          lt_of_le_of_lt R.actual_le_boundary hRInside
        have haLt : a < H := lt_of_le_of_lt haR hActualLt
        intro hMod
        have hStep : a + 1 ≤ H := by omega
        have hPowDvd : 2 ^ (a + 1) ∣ 2 ^ H :=
          twoPow_dvd_twoPow_of_le hStep
        exact hTwo.2 (hPowDvd.trans hMod)

namespace CriticalCarryRows

/-- combined row condition から row 数を読む。 -/
theorem length_eq
    {P : ℕ}
    {rows : List FerrersRow}
    (h : CriticalCarryRows P rows) :
    rows.length = P :=
  h.1.length_eq

/-- combined row condition から weighted defect 上界を読む。 -/
theorem weightedDefect_le_upper
    {P : ℕ}
    {rows : List FerrersRow}
    (h : CriticalCarryRows P rows) :
    ferrersWeightedDefect rows ≤ criticalWeightedDefectUpper P :=
  h.1.weightedDefect_le_upper

/-- combined row condition から 4 divisibility を読む。 -/
theorem four_dvd_weightedDefect
    {P : ℕ}
    {rows : List FerrersRow}
    (h : CriticalCarryRows P rows) :
    4 ∣ ferrersWeightedDefect rows :=
  h.1.four_dvd_weightedDefect

/-- combined row condition から H-bit range を読む。 -/
theorem insideBitWidth
    {P : ℕ}
    {rows : List FerrersRow}
    (h : CriticalCarryRows P rows) :
    RowsInsideBitWidth (criticalTwoDepth P) rows :=
  h.1.insideBitWidth

end CriticalCarryRows

end CSTCarry
end Collatz3
