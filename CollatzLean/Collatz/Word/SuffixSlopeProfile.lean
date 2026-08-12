import CollatzLean.Collatz.Word.SuffixGapBudget

/-!
# all-suffix contracting 語の suffix slope profile

末尾 `r` 文字の multiplicative slope

  `3^r / 2^K_r`

を、全体の `2^H` scale に持ち上げて足した整数 numerator を
`suffixSlopeNumerator` とする。

この量は exact に `3 * affineConst` に一致する。
また `AllSuffixesContracting` では、隣接する2つの suffix gap が
full two-power scale の `1/4` より大きい量を必ず消費する。
これを2文字ずつ束ねることで

  `(length - 1) * 2^H < 8 * suffixGapBudget`

という全長線形 lower bound を得る。
-/

namespace Collatz
namespace Word

/--
全 suffix slope を full `2^H` scale に持ち上げて足した numerator。

正規化すると

  `suffixSlopeNumerator w / 2^H`

は末尾 `r=1,...,length` の
`3^r / 2^K_r` の総和に対応する。
-/
def suffixSlopeNumerator : Collatz.Word → ℕ
  | [] => 0
  | e :: w =>
      3 ^ oddSteps (e :: w) +
        2 ^ e * suffixSlopeNumerator w

@[simp] theorem suffixSlopeNumerator_nil :
    suffixSlopeNumerator ([] : Collatz.Word) = 0 := rfl

@[simp] theorem suffixSlopeNumerator_cons
    (e : ℕ) (w : Collatz.Word) :
    suffixSlopeNumerator (e :: w) =
      3 ^ oddSteps (e :: w) +
        2 ^ e * suffixSlopeNumerator w := rfl

/--
suffix slope profile の numerator は exact に `3 * affineConst`。
-/
theorem suffixSlopeNumerator_eq_three_mul_affineConst
    (w : Collatz.Word) :
    suffixSlopeNumerator w = 3 * affineConst w := by
  induction w with
  | nil =>
      simp [suffixSlopeNumerator, affineConst]
  | cons e w ih =>
      simp only [suffixSlopeNumerator_cons, affineConst_cons,
        oddSteps_cons, ih, pow_succ]
      ring

/--
all-suffix contracting では slope numerator と gap budget が
full scale を exact に二分する。
-/
theorem AllSuffixesContracting.suffixSlopeNumerator_add_suffixGapBudget
    {w : Collatz.Word}
    (hAll : AllSuffixesContracting w) :
    suffixSlopeNumerator w + suffixGapBudget w =
      oddSteps w * 2 ^ twoSteps w := by
  have h :=
    hAll.oddSteps_mul_twoPow_eq_three_mul_affine_add_suffixGapBudget
  rw [suffixSlopeNumerator_eq_three_mul_affineConst] at ⊢
  omega

/-- 先頭2つの suffix gap だけを取り出した budget。 -/
private def firstTwoSuffixGapBudget
    (e f : ℕ) (w : Collatz.Word) : ℕ :=
  (2 ^ twoSteps (e :: f :: w) -
      3 ^ oddSteps (e :: f :: w)) +
    2 ^ e *
      (2 ^ twoSteps (f :: w) -
        3 ^ oddSteps (f :: w))

/--
隣接する2つの contracting suffix は、full two-power scale の
`1/4` より大きい gap budget を必ず消費する。

正規化 slope を `lambda_r, lambda_(r+1)` と見れば

  `(1-lambda_r) + (1-lambda_(r+1)) > 1/4`

に対応する自然数版。
-/
private theorem four_mul_firstTwoSuffixGapBudget_gt_twoPow
    {e f : ℕ} {w : Collatz.Word}
    (hAll : AllSuffixesContracting (e :: f :: w)) :
    2 ^ twoSteps (e :: f :: w) <
      4 * firstTwoSuffixGapBudget e f w := by
  change
    Contracting (e :: f :: w) ∧
      AllSuffixesContracting (f :: w) at hAll
  rcases hAll with ⟨hWhole, hTailAll⟩
  change
    Contracting (f :: w) ∧
      AllSuffixesContracting w at hTailAll
  have hTail : Contracting (f :: w) := hTailAll.1
  let P := 2 ^ e
  let A := 2 ^ twoSteps (f :: w)
  let C := 3 ^ oddSteps (f :: w)
  let G := P * A - 3 * C
  let g := A - C
  have hWhole' : 3 * C < P * A := by
    simpa [P, A, C, Contracting, twoSteps_cons, oddSteps_cons,
      pow_add, pow_succ, Nat.mul_assoc, Nat.mul_comm,
      Nat.mul_left_comm] using hWhole
  have hTail' : C < A := by
    simpa [A, C, Contracting] using hTail
  have hG : 3 * C + G = P * A := by
    dsimp [G]
    exact Nat.add_sub_of_le (Nat.le_of_lt hWhole')
  have hg : C + g = A := by
    dsimp [g]
    exact Nat.add_sub_of_le (Nat.le_of_lt hTail')
  have hPpos : 0 < P := by
    dsimp [P]
    exact Nat.pow_pos (by omega)
  have hquarter : P * A < 4 * (G + P * g) := by
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
        have hPC_lt_PA : P * C < P * A :=
          (Nat.mul_lt_mul_left hPpos).2 hTail'
        have h4C_le_PC : 4 * C ≤ P * C := by
          have hm := Nat.mul_le_mul_right C hPfour
          simpa [Nat.mul_comm, Nat.mul_left_comm,
            Nat.mul_assoc] using hm
        nlinarith
  simpa [firstTwoSuffixGapBudget, P, A, C, G, g,
    twoSteps_cons, oddSteps_cons, pow_add, pow_succ,
    Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hquarter

/--
1文字の all-suffix contracting 語では主評価が成立する。
-/
private theorem
    length_sub_one_mul_twoPow_lt_eight_mul_suffixGapBudget_singleton
    (e : ℕ)
    (hContracting : Contracting ([e] : Collatz.Word)) :
    (([e] : Collatz.Word).length - 1) *
        2 ^ twoSteps ([e] : Collatz.Word) <
      8 * suffixGapBudget ([e] : Collatz.Word) := by
  have hgap :
      0 <
        2 ^ twoSteps ([e] : Collatz.Word) -
          3 ^ oddSteps ([e] : Collatz.Word) :=
    Nat.sub_pos_of_lt hContracting
  simp only [
    List.length_cons,
    List.length_nil,
    Nat.add_zero,
    suffixGapBudget_cons,
    suffixGapBudget_nil,
    Nat.mul_zero,
    Nat.add_zero
  ]
  omega


/--
2文字の all-suffix contracting 語では、
先頭2 suffix gap の評価だけで主評価が成立する。
-/
private theorem
    length_sub_one_mul_twoPow_lt_eight_mul_suffixGapBudget_pair
    {e f : ℕ}
    (hAll : AllSuffixesContracting ([e, f] : Collatz.Word)) :
    (([e, f] : Collatz.Word).length - 1) *
        2 ^ twoSteps ([e, f] : Collatz.Word) <
      8 * suffixGapBudget ([e, f] : Collatz.Word) := by
  have hPair :=
    four_mul_firstTwoSuffixGapBudget_gt_twoPow
      (e := e) (f := f) (w := []) hAll
  have hOne :
      2 ^ twoSteps ([e, f] : Collatz.Word) <
        8 * firstTwoSuffixGapBudget e f [] := by
    nlinarith
  simpa [
    firstTwoSuffixGapBudget,
    suffixGapBudget,
    twoSteps,
    oddSteps,
    pow_add
  ] using hOne


/--
2文字を prepend すると full two-power scale は
`2^(e+f)` 倍される。
-/
private theorem twoPow_twoSteps_cons_cons
    (e f : ℕ)
    (u : Collatz.Word) :
    2 ^ twoSteps (e :: f :: u) =
      2 ^ (e + f) * 2 ^ twoSteps u := by
  simp only [twoSteps_cons, pow_add]
  ring


/--
suffix gap budget は、先頭2 suffix の寄与と
残り tail の scaled budget に分解する。
-/
private theorem suffixGapBudget_cons_cons
    (e f : ℕ)
    (u : Collatz.Word) :
    suffixGapBudget (e :: f :: u) =
      firstTwoSuffixGapBudget e f u +
        2 ^ (e + f) * suffixGapBudget u := by
  simp only [
    suffixGapBudget_cons,
    firstTwoSuffixGapBudget,
    twoSteps_cons,
    oddSteps_cons,
    pow_add
  ]
  ring


/--
非空 tail に主評価が成立しているなら、
先頭2 suffix gap の評価と合わせて
2文字 prepend 後にも主評価が成立する。
-/
private theorem
    length_sub_one_mul_twoPow_lt_eight_mul_suffixGapBudget_cons_cons
    {e f : ℕ}
    {u : Collatz.Word}
    (hu : u ≠ [])
    (hPair :
      2 * 2 ^ twoSteps (e :: f :: u) <
        8 * firstTwoSuffixGapBudget e f u)
    (hTail :
      (u.length - 1) * 2 ^ twoSteps u <
        8 * suffixGapBudget u) :
    ((e :: f :: u).length - 1) *
        2 ^ twoSteps (e :: f :: u) <
      8 * suffixGapBudget (e :: f :: u) := by
  have hScalePos :
      0 < 2 ^ (e + f) :=
    Nat.pow_pos (by omega)
  have hTailScaled :
      2 ^ (e + f) *
          ((u.length - 1) * 2 ^ twoSteps u) <
        2 ^ (e + f) *
          (8 * suffixGapBudget u) :=
    (Nat.mul_lt_mul_left hScalePos).2 hTail
  have hScale :
      2 ^ twoSteps (e :: f :: u) =
        2 ^ (e + f) * 2 ^ twoSteps u :=
    twoPow_twoSteps_cons_cons e f u
  have hTailScaled' :
      (u.length - 1) *
          2 ^ twoSteps (e :: f :: u) <
        8 * (2 ^ (e + f) * suffixGapBudget u) := by
    rw [hScale]
    nlinarith
  have hBudget :
      suffixGapBudget (e :: f :: u) =
        firstTwoSuffixGapBudget e f u +
          2 ^ (e + f) * suffixGapBudget u :=
    suffixGapBudget_cons_cons e f u
  have huPos : 0 < u.length :=
    List.length_pos_of_ne_nil hu
  have hLen :
      (e :: f :: u).length - 1 =
        (u.length - 1) + 2 := by
    simp only [List.length_cons]
    omega
  rw [hLen, hBudget]
  nlinarith

/--
all-suffix contracting な非空語では、suffix gap budget は
全長に比例して full two-power scale を消費する。

`(length - 1) * 2^H < 8 * suffixGapBudget`。

2文字ごとに、先頭2 suffix gap が `2^H/4` より大きいことを使う。
-/
theorem
    AllSuffixesContracting.length_sub_one_mul_twoPow_lt_eight_mul_suffixGapBudget
    {w : Collatz.Word}
    (hAll : AllSuffixesContracting w)
    (hne : w ≠ []) :
    (w.length - 1) * 2 ^ twoSteps w <
      8 * suffixGapBudget w := by
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
              change
                Contracting ([e] : Collatz.Word) ∧ True
                at hAll
              exact
                length_sub_one_mul_twoPow_lt_eight_mul_suffixGapBudget_singleton
                  e hAll.1
          | cons f u =>
              change
                Contracting (e :: f :: u) ∧
                  (Contracting (f :: u) ∧
                    AllSuffixesContracting u)
                at hAll
              by_cases hu : u = []
              · subst u
                exact
                  length_sub_one_mul_twoPow_lt_eight_mul_suffixGapBudget_pair
                    hAll
              · have huLen :
                    u.length < (e :: f :: u).length := by
                  simp
                have hIH :=
                  ih u.length huLen
                    (w := u)
                    hAll.2.2
                    hu
                    (by rfl)
                have hPair :=
                  four_mul_firstTwoSuffixGapBudget_gt_twoPow
                    (e := e) (f := f) (w := u) hAll
                have hPair8 :
                    2 * 2 ^ twoSteps (e :: f :: u) <
                      8 * firstTwoSuffixGapBudget e f u := by
                  nlinarith
                exact
                  length_sub_one_mul_twoPow_lt_eight_mul_suffixGapBudget_cons_cons
                    hu hPair8 hIH

end Word
end Collatz
