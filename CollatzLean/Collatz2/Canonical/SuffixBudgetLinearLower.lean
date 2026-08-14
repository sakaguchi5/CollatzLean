import CollatzLean.Collatz2.Canonical.PositiveSuffixBudget

/-!
# Collatz2 Canonical: suffix budget の全長線形 lower bound

`suffixBudgetExcess`

  K = p * 2^H - 3B

は、all-suffix-contracting word では全 nonempty suffix gap の
prefix-two-depth weighted sumに一致する。

隣接する2 suffix gap を束ねると full `2^H` scale の1/4より大きい量を
必ず消費するため、非空 word で

  (length - 1) * 2^H < 8 * K

を得る。

旧 `SuffixSlopeProfile` の評価を、現在の determinant-profile 定義へ移植したもの。
-/

namespace Collatz2
namespace Word

/-- 全 nonempty suffix gap の recursive weighted budget。 -/
def suffixGapBudgetRec : Word → ℕ
  | [] => 0
  | e :: w =>
      (2 ^ twoSteps (e :: w) -
        3 ^ oddSteps (e :: w)) +
      2 ^ e * suffixGapBudgetRec w

@[simp] theorem suffixGapBudgetRec_nil :
    suffixGapBudgetRec ([] : Word) = 0 := rfl

@[simp] theorem suffixGapBudgetRec_cons
    (e : ℕ) (w : Word) :
    suffixGapBudgetRec (e :: w) =
      (2 ^ twoSteps (e :: w) -
        3 ^ oddSteps (e :: w)) +
      2 ^ e * suffixGapBudgetRec w := rfl

/--
all-suffix-contracting では recursive budget が affine exact excess を与える。
-/
theorem AllSuffixesContracting.three_mul_affineConst_add_suffixGapBudgetRec
    {w : Word}
    (hAll : AllSuffixesContracting w) :
    3 * affineConst w + suffixGapBudgetRec w =
      oddSteps w * 2 ^ twoSteps w := by
  induction w with
  | nil =>
      simp [suffixGapBudgetRec, affineConst, oddSteps, twoSteps]
  | cons e w ih =>
      have hWhole :
          Contracting (e :: w) :=
        hAll.whole_contracting (by simp)
      have hTail :
          AllSuffixesContracting w :=
        AllSuffixesNegativeDeterminant.tail hAll
      have hi := ih hTail
      have hPow :
          3 ^ oddSteps (e :: w) +
              (2 ^ twoSteps (e :: w) -
                3 ^ oddSteps (e :: w)) =
            2 ^ twoSteps (e :: w) := by
        have hlt :
            3 ^ oddSteps (e :: w) <
              2 ^ twoSteps (e :: w) :=
          (contracting_iff_threePow_lt_twoPow).1 hWhole
        exact Nat.add_sub_of_le (Nat.le_of_lt hlt)
      calc
        3 * affineConst (e :: w) +
            suffixGapBudgetRec (e :: w)
            =
          3 * (3 ^ oddSteps w + 2 ^ e * affineConst w) +
            ((2 ^ twoSteps (e :: w) -
                3 ^ oddSteps (e :: w)) +
              2 ^ e * suffixGapBudgetRec w) := by
                simp only [affineConst_cons, suffixGapBudgetRec_cons]
        _ =
          3 ^ oddSteps (e :: w) +
            (2 ^ twoSteps (e :: w) -
              3 ^ oddSteps (e :: w)) +
            2 ^ e *
              (3 * affineConst w +
                suffixGapBudgetRec w) := by
                  simp only [oddSteps_cons, pow_succ]
                  ring
        _ =
          2 ^ twoSteps (e :: w) +
            2 ^ e *
              (oddSteps w * 2 ^ twoSteps w) := by
                rw [hPow, hi]
        _ =
          oddSteps (e :: w) *
            2 ^ twoSteps (e :: w) := by
              simp only [oddSteps_cons, twoSteps_cons, pow_add]
              ring

/-- recursive budget と `suffixBudgetExcess` は一致。 -/
theorem AllSuffixesContracting.suffixGapBudgetRec_eq_suffixBudgetExcess
    {w : Word}
    (hAll : AllSuffixesContracting w) :
    suffixGapBudgetRec w = suffixBudgetExcess w := by
  have hRec :=
    hAll.three_mul_affineConst_add_suffixGapBudgetRec
  by_cases hne : w = []
  · subst w
    simp [suffixGapBudgetRec, suffixBudgetExcess,
      affineConst, oddSteps, twoSteps]
  · have hlt :=
      hAll.three_mul_affineConst_lt_oddSteps_mul_twoPow hne
    have hEx :
        3 * affineConst w + suffixBudgetExcess w =
          oddSteps w * 2 ^ twoSteps w := by
      unfold suffixBudgetExcess
      omega
    omega

/-- 先頭2 suffix の budget。 -/
private def firstTwoSuffixBudget
    (e f : ℕ) (w : Word) : ℕ :=
  (2 ^ twoSteps (e :: f :: w) -
      3 ^ oddSteps (e :: f :: w)) +
    2 ^ e *
      (2 ^ twoSteps (f :: w) -
        3 ^ oddSteps (f :: w))

/--
隣接する2 contracting suffix は full scale の1/4より大きい budget を消費する。
-/
private theorem four_mul_firstTwoSuffixBudget_gt_twoPow
    {e f : ℕ} {w : Word}
    (hAll : AllSuffixesContracting (e :: f :: w)) :
    2 ^ twoSteps (e :: f :: w) <
      4 * firstTwoSuffixBudget e f w := by
  have hWhole :
      Contracting (e :: f :: w) :=
    hAll.whole_contracting (by simp)
  have hTailAll :
      AllSuffixesContracting (f :: w) :=
    AllSuffixesNegativeDeterminant.tail hAll
  have hTail :
      Contracting (f :: w) :=
    hTailAll.whole_contracting (by simp)
  let P := 2 ^ e
  let A := 2 ^ twoSteps (f :: w)
  let C := 3 ^ oddSteps (f :: w)
  let G := P * A - 3 * C
  let g := A - C
  have hWhole' : 3 * C < P * A := by
    simpa [P, A, C, twoSteps_cons, oddSteps_cons,
      pow_add, pow_succ, Nat.mul_assoc, Nat.mul_comm,
      Nat.mul_left_comm] using
      (contracting_iff_threePow_lt_twoPow).1 hWhole
  have hTail' : C < A := by
    simpa [A, C] using
      (contracting_iff_threePow_lt_twoPow).1 hTail
  have hG : 3 * C + G = P * A := by
    dsimp [G]
    exact Nat.add_sub_of_le (Nat.le_of_lt hWhole')
  have hg : C + g = A := by
    dsimp [g]
    exact Nat.add_sub_of_le (Nat.le_of_lt hTail')
  have hPpos : 0 < P := by
    dsimp [P]
    exact Nat.pow_pos (by omega)
  have hquarter :
      P * A < 4 * (G + P * g) := by
    by_cases he0 : e = 0
    · subst e
      norm_num [P] at hWhole' hG hPpos ⊢
      nlinarith
    · by_cases he1 : e = 1
      · subst e
        norm_num [P] at hWhole' hG hPpos ⊢
        nlinarith
      · have heTwo : 2 ≤ e := by omega
        have hPfour : 4 ≤ P := by
          have hp :=
            Nat.pow_le_pow_right
              (by omega : 0 < (2 : ℕ)) heTwo
          norm_num at hp
          simpa [P] using hp
        have hPC_lt_PA :
            P * C < P * A :=
          (Nat.mul_lt_mul_left hPpos).2 hTail'
        have h4C_le_PC : 4 * C ≤ P * C := by
          have hm :=
            Nat.mul_le_mul_right C hPfour
          simpa [Nat.mul_comm, Nat.mul_left_comm,
            Nat.mul_assoc] using hm
        nlinarith
  simpa [firstTwoSuffixBudget, P, A, C, G, g,
    twoSteps_cons, oddSteps_cons, pow_add, pow_succ,
    Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      hquarter

/-- 2文字 prepend 時の full two-power scale。 -/
private theorem twoPow_twoSteps_cons_cons
    (e f : ℕ) (u : Word) :
    2 ^ twoSteps (e :: f :: u) =
      2 ^ (e + f) * 2 ^ twoSteps u := by
  simp only [twoSteps_cons, pow_add]
  ring

/-- recursive budget の2文字 decomposition。 -/
private theorem suffixGapBudgetRec_cons_cons
    (e f : ℕ) (u : Word) :
    suffixGapBudgetRec (e :: f :: u) =
      firstTwoSuffixBudget e f u +
        2 ^ (e + f) * suffixGapBudgetRec u := by
  simp only [suffixGapBudgetRec_cons,
    firstTwoSuffixBudget, twoSteps_cons,
    oddSteps_cons, pow_add]
  ring

/--
first two suffix budget の既存 bound を 8 倍側へ整形する。
-/
theorem eight_mul_firstTwoSuffixBudget_gt_two_mul_twoPow
    {e f : ℕ}
    {u : Word}
    (hAll : AllSuffixesContracting (e :: f :: u)) :
    2 * 2 ^ twoSteps (e :: f :: u) <
      8 * firstTwoSuffixBudget e f u := by
  have hPair :=
    four_mul_firstTwoSuffixBudget_gt_twoPow
      (e := e) (f := f) (w := u) hAll
  nlinarith

/--
all-suffix-contracting singleton の全長 lower bound。
-/
theorem AllSuffixesContracting.singleton_length_bound
    {e : ℕ}
    (hAll : AllSuffixesContracting ([e] : Word)) :
    (([e] : Word).length - 1) *
        2 ^ twoSteps ([e] : Word) <
      8 * suffixGapBudgetRec ([e] : Word) := by
  have hWhole :
      Contracting ([e] : Word) :=
    hAll.whole_contracting (by simp)
  have hgap :
      0 <
        2 ^ twoSteps ([e] : Word) -
          3 ^ oddSteps ([e] : Word) :=
    Nat.sub_pos_of_lt
      ((contracting_iff_threePow_lt_twoPow).1 hWhole)
  have hgap' :
      0 < 2 ^ e - 3 := by
    simpa [twoSteps, oddSteps] using hgap
  have hBudgetPos :
      0 < suffixGapBudgetRec ([e] : Word) := by
    simpa [suffixGapBudgetRec] using hgap'
  have hEightBudgetPos :
      0 < 8 * suffixGapBudgetRec ([e] : Word) := by
    exact Nat.mul_pos (by omega) hBudgetPos
  simpa using hEightBudgetPos

/--
all-suffix-contracting 2文字 word の全長 lower bound。
-/
theorem AllSuffixesContracting.pair_length_bound
    {e f : ℕ}
    (hAll : AllSuffixesContracting ([e, f] : Word)) :
    (([e, f] : Word).length - 1) *
        2 ^ twoSteps ([e, f] : Word) <
      8 * suffixGapBudgetRec ([e, f] : Word) := by
  have hPair8 :
      2 * 2 ^ twoSteps ([e, f] : Word) <
        8 * firstTwoSuffixBudget e f [] :=
    eight_mul_firstTwoSuffixBudget_gt_two_mul_twoPow
      (e := e) (f := f) (u := []) hAll
  have hPair8' :
      2 * 2 ^ (e + f) <
        8 * firstTwoSuffixBudget e f [] := by
    simpa [twoSteps] using hPair8
  have hPowPos :
      0 < 2 ^ (e + f) :=
    Nat.pow_pos (by omega)
  have hBudget :=
    suffixGapBudgetRec_cons_cons e f []
  rw [hBudget]
  simp
  omega

/--
`u` が非空で、その tail に全長 bound が成立していれば、
先頭2文字 `e,f` を付けた word にも全長 bound が成立する。
-/
theorem AllSuffixesContracting.cons_cons_length_bound_of_tail_bound
    {e f : ℕ}
    {u : Word}
    (hAll : AllSuffixesContracting (e :: f :: u))
    (hu : u ≠ [])
    (hTail :
      (u.length - 1) * 2 ^ twoSteps u <
        8 * suffixGapBudgetRec u) :
    ((e :: f :: u).length - 1) *
        2 ^ twoSteps (e :: f :: u) <
      8 * suffixGapBudgetRec (e :: f :: u) := by
  have hPair8 :
      2 * 2 ^ twoSteps (e :: f :: u) <
        8 * firstTwoSuffixBudget e f u :=
    eight_mul_firstTwoSuffixBudget_gt_two_mul_twoPow
      (e := e) (f := f) (u := u) hAll
  have hScalePos :
      0 < 2 ^ (e + f) :=
    Nat.pow_pos (by omega)
  have hTailScaled :
      2 ^ (e + f) *
          ((u.length - 1) * 2 ^ twoSteps u) <
        2 ^ (e + f) *
          (8 * suffixGapBudgetRec u) :=
    (Nat.mul_lt_mul_left hScalePos).2 hTail
  have hScale :=
    twoPow_twoSteps_cons_cons e f u
  have hTailScaled' :
      (u.length - 1) *
          2 ^ twoSteps (e :: f :: u) <
        8 *
          (2 ^ (e + f) *
            suffixGapBudgetRec u) := by
    rw [hScale]
    nlinarith
  have hBudget :=
    suffixGapBudgetRec_cons_cons e f u
  have huPos :
      0 < u.length :=
    List.length_pos_of_ne_nil hu
  have hLen :
      (e :: f :: u).length - 1 =
        (u.length - 1) + 2 := by
    simp only [List.length_cons]
    omega
  rw [hLen, hBudget]
  nlinarith

/--
all-suffix-contracting 非空 word の全長線形 lower bound。
-/
theorem AllSuffixesContracting.length_sub_one_mul_twoPow_lt_eight_mul_suffixGapBudgetRec
    {w : Word}
    (hAll : AllSuffixesContracting w)
    (hne : w ≠ []) :
    (w.length - 1) * 2 ^ twoSteps w <
      8 * suffixGapBudgetRec w := by
  generalize hn : w.length = n
  induction n using Nat.strong_induction_on generalizing w with
  | h n ih =>
      subst n
      cases w with
      | nil =>
          contradiction
      | cons e tail =>
          cases tail with
          | nil =>
              exact
                AllSuffixesContracting.singleton_length_bound
                  hAll
          | cons f u =>
              by_cases hu : u = []
              · subst u
                exact
                  AllSuffixesContracting.pair_length_bound
                    hAll
              · have hTailAll :
                    AllSuffixesContracting u :=
                  AllSuffixesNegativeDeterminant.tail
                    (AllSuffixesNegativeDeterminant.tail hAll)
                have huLenLt :
                    u.length <
                      (e :: f :: u).length := by
                  simp
                have hTail :
                    (u.length - 1) * 2 ^ twoSteps u <
                      8 * suffixGapBudgetRec u :=
                  ih u.length huLenLt
                    (w := u)
                    hTailAll
                    hu
                    (by rfl)
                exact
                  AllSuffixesContracting.cons_cons_length_bound_of_tail_bound
                    hAll hu hTail

/--
最終形：current `suffixBudgetExcess` そのものに対する linear lower bound。
-/
theorem AllSuffixesContracting.length_sub_one_mul_twoPow_lt_eight_mul_suffixBudgetExcess
    {w : Word}
    (hAll : AllSuffixesContracting w)
    (hne : w ≠ []) :
    (w.length - 1) * 2 ^ twoSteps w <
      8 * suffixBudgetExcess w := by
  have h :=
    hAll.length_sub_one_mul_twoPow_lt_eight_mul_suffixGapBudgetRec hne
  rw [hAll.suffixGapBudgetRec_eq_suffixBudgetExcess] at h
  exact h

end Word
end Collatz2
