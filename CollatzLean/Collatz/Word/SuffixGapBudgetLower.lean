import CollatzLean.Collatz.Word.SuffixGapBudget
import CollatzLean.Collatz.Word.SuffixExponentBound
import Mathlib.Tactic.IntervalCases

/-!
# suffix gap budget の定量 lower bound

`AllSuffixesContracting` の各末尾 suffix が消費する gap を定量化する。

最後4文字だけで

  `2^H < suffixGapBudget`

最後7文字まで使えば

  `2 * 2^H < suffixGapBudget`

を得る。natural zero-replay packet の `6*n <= m` を
`6*n+2 <= m` まで強化するための純有限語層。
-/

namespace Collatz
namespace Word

private theorem four_le_of_nine_lt_twoPow
    {k : ℕ} (h : 9 < 2 ^ k) : 4 ≤ k := by
  by_contra hnot
  have hk : k ≤ 3 := by omega
  interval_cases k <;> norm_num at h

private theorem five_le_of_twentySeven_lt_twoPow
    {k : ℕ} (h : 27 < 2 ^ k) : 5 ≤ k := by
  by_contra hnot
  have hk : k ≤ 4 := by omega
  interval_cases k <;> norm_num at h

private theorem seven_le_of_eightyOne_lt_twoPow
    {k : ℕ} (h : 81 < 2 ^ k) : 7 ≤ k := by
  by_contra hnot
  have hk : k ≤ 6 := by omega
  interval_cases k <;> norm_num at h

private theorem eight_le_of_twoFortyThree_lt_twoPow
    {k : ℕ} (h : 243 < 2 ^ k) : 8 ≤ k := by
  by_contra hnot
  have hk : k ≤ 7 := by omega
  interval_cases k <;> norm_num at h

private theorem ten_le_of_sevenTwentyNine_lt_twoPow
    {k : ℕ} (h : 729 < 2 ^ k) : 10 ≤ k := by
  by_contra hnot
  have hk : k ≤ 9 := by omega
  interval_cases k <;> norm_num at h

private theorem twelve_le_of_twoThousandOneEightySeven_lt_twoPow
    {k : ℕ} (h : 2187 < 2 ^ k) : 12 ≤ k := by
  by_contra hnot
  have hk : k ≤ 11 := by omega
  interval_cases k <;> norm_num at h

/-- 最後1文字の budget は total two-power の4分の1以上。 -/
private theorem ratio_one
    (a : ℕ)
    (hAll : AllSuffixesContracting ([a] : Collatz.Word)) :
    2 ^ twoSteps ([a] : Collatz.Word) ≤
      4 * suffixGapBudget ([a] : Collatz.Word) := by
  change Contracting ([a] : Collatz.Word) ∧ True at hAll
  have hC : 3 < 2 ^ a := by
    simpa [Contracting, oddSteps, twoSteps] using hAll.1
  have hgap :
      3 + (2 ^ a - 3) = 2 ^ a :=
    Nat.add_sub_of_le (Nat.le_of_lt hC)
  simp [suffixGapBudget, twoSteps, oddSteps]
  omega

/-- 最後2文字の budget ratio: `11/16`。 -/
private theorem ratio_two
    (a b : ℕ)
    (hAll : AllSuffixesContracting ([a, b] : Collatz.Word)) :
    11 * 2 ^ twoSteps ([a, b] : Collatz.Word) ≤
      16 * suffixGapBudget ([a, b] : Collatz.Word) := by
  change
    Contracting ([a, b] : Collatz.Word) ∧
      AllSuffixesContracting ([b] : Collatz.Word) at hAll
  rcases hAll with ⟨hWhole, hTailAll⟩
  have hTail := ratio_one b hTailAll
  let A := 2 ^ twoSteps ([a, b] : Collatz.Word)
  let At := 2 ^ twoSteps ([b] : Collatz.Word)
  let G :=
    2 ^ twoSteps ([a, b] : Collatz.Word) -
      3 ^ oddSteps ([a, b] : Collatz.Word)
  let Bt := suffixGapBudget ([b] : Collatz.Word)
  have hAeq : A = 2 ^ a * At := by
    simp [A, At, twoSteps, pow_add]
  have hC : 9 < A := by
    simpa [A, Contracting, oddSteps] using hWhole
  have hk : 4 ≤ twoSteps ([a, b] : Collatz.Word) :=
    four_le_of_nine_lt_twoPow (by
      simpa [A] using hC)
  have hAmin : 16 ≤ A := by
    have hp :=
      Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hk
    simpa [A] using hp
  have hgap : 9 + G = A := by
    dsimp [G, A]
    exact Nat.add_sub_of_le (Nat.le_of_lt hC)
  have hG : 7 * A ≤ 16 * G := by
    omega
  have hTail' : At ≤ 4 * Bt := by
    simpa [At, Bt] using hTail
  have hTailScaled :
      4 * A ≤ 16 * (2 ^ a * Bt) := by
    calc
      4 * A = (4 * 2 ^ a) * At := by
        rw [hAeq]
        ring
      _ ≤ (4 * 2 ^ a) * (4 * Bt) :=
        Nat.mul_le_mul_left _ hTail'
      _ = 16 * (2 ^ a * Bt) := by ring
  have hrec :
      suffixGapBudget ([a, b] : Collatz.Word) =
        G + 2 ^ a * Bt := by
    rfl
  calc
    11 * A = 7 * A + 4 * A := by ring
    _ ≤ 16 * G + 16 * (2 ^ a * Bt) :=
      Nat.add_le_add hG hTailScaled
    _ = 16 * (G + 2 ^ a * Bt) := by ring
    _ = 16 * suffixGapBudget ([a, b] : Collatz.Word) := by
      rw [hrec]

/-- 最後3文字の budget ratio: `27/32`。 -/
private theorem ratio_three
    (a b c : ℕ)
    (hAll : AllSuffixesContracting ([a, b, c] : Collatz.Word)) :
    27 * 2 ^ twoSteps ([a, b, c] : Collatz.Word) ≤
      32 * suffixGapBudget ([a, b, c] : Collatz.Word) := by
  change
    Contracting ([a, b, c] : Collatz.Word) ∧
      AllSuffixesContracting ([b, c] : Collatz.Word) at hAll
  rcases hAll with ⟨hWhole, hTailAll⟩
  have hTail := ratio_two b c hTailAll
  let A := 2 ^ twoSteps ([a, b, c] : Collatz.Word)
  let At := 2 ^ twoSteps ([b, c] : Collatz.Word)
  let G :=
    2 ^ twoSteps ([a, b, c] : Collatz.Word) -
      3 ^ oddSteps ([a, b, c] : Collatz.Word)
  let Bt := suffixGapBudget ([b, c] : Collatz.Word)
  have hAeq : A = 2 ^ a * At := by
    simp [A, At, twoSteps, pow_add]
  have hC : 27 < A := by
    simpa [A, Contracting, oddSteps] using hWhole
  have hk : 5 ≤ twoSteps ([a, b, c] : Collatz.Word) :=
    five_le_of_twentySeven_lt_twoPow (by simpa [A] using hC)
  have hAmin : 32 ≤ A := by
    have hp :=
      Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hk
    simpa [A] using hp
  have hgap : 27 + G = A := by
    dsimp [G, A]
    exact Nat.add_sub_of_le (Nat.le_of_lt hC)
  have hG : 5 * A ≤ 32 * G := by
    omega
  have hTail' : 11 * At ≤ 16 * Bt := by
    simpa [At, Bt] using hTail
  have hTailScaled :
      22 * A ≤ 32 * (2 ^ a * Bt) := by
    calc
      22 * A = (2 * 2 ^ a) * (11 * At) := by
        rw [hAeq]
        ring
      _ ≤ (2 * 2 ^ a) * (16 * Bt) :=
        Nat.mul_le_mul_left _ hTail'
      _ = 32 * (2 ^ a * Bt) := by ring
  have hrec :
      suffixGapBudget ([a, b, c] : Collatz.Word) =
        G + 2 ^ a * Bt := by
    rfl
  calc
    27 * A = 5 * A + 22 * A := by ring
    _ ≤ 32 * G + 32 * (2 ^ a * Bt) :=
      Nat.add_le_add hG hTailScaled
    _ = 32 * (G + 2 ^ a * Bt) := by ring
    _ = 32 * suffixGapBudget ([a, b, c] : Collatz.Word) := by
      rw [hrec]

/-- 最後4文字の budget ratio: `155/128 > 1`。 -/
private theorem ratio_four
    (a b c d : ℕ)
    (hAll : AllSuffixesContracting ([a, b, c, d] : Collatz.Word)) :
    155 * 2 ^ twoSteps ([a, b, c, d] : Collatz.Word) ≤
      128 * suffixGapBudget ([a, b, c, d] : Collatz.Word) := by
  change
    Contracting ([a, b, c, d] : Collatz.Word) ∧
      AllSuffixesContracting ([b, c, d] : Collatz.Word) at hAll
  rcases hAll with ⟨hWhole, hTailAll⟩
  have hTail := ratio_three b c d hTailAll
  let A := 2 ^ twoSteps ([a, b, c, d] : Collatz.Word)
  let At := 2 ^ twoSteps ([b, c, d] : Collatz.Word)
  let G :=
    2 ^ twoSteps ([a, b, c, d] : Collatz.Word) -
      3 ^ oddSteps ([a, b, c, d] : Collatz.Word)
  let Bt := suffixGapBudget ([b, c, d] : Collatz.Word)
  have hAeq : A = 2 ^ a * At := by
    simp [A, At, twoSteps, pow_add]
  have hC : 81 < A := by
    simpa [A, Contracting, oddSteps] using hWhole
  have hk : 7 ≤ twoSteps ([a, b, c, d] : Collatz.Word) :=
    seven_le_of_eightyOne_lt_twoPow (by simpa [A] using hC)
  have hAmin : 128 ≤ A := by
    have hp :=
      Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hk
    simpa [A] using hp
  have hgap : 81 + G = A := by
    dsimp [G, A]
    exact Nat.add_sub_of_le (Nat.le_of_lt hC)
  have hG : 47 * A ≤ 128 * G := by
    omega
  have hTail' : 27 * At ≤ 32 * Bt := by
    simpa [At, Bt] using hTail
  have hTailScaled :
      108 * A ≤ 128 * (2 ^ a * Bt) := by
    calc
      108 * A = (4 * 2 ^ a) * (27 * At) := by
        rw [hAeq]
        ring
      _ ≤ (4 * 2 ^ a) * (32 * Bt) :=
        Nat.mul_le_mul_left _ hTail'
      _ = 128 * (2 ^ a * Bt) := by ring
  have hrec :
      suffixGapBudget ([a, b, c, d] : Collatz.Word) =
        G + 2 ^ a * Bt := by
    rfl
  calc
    155 * A = 47 * A + 108 * A := by ring
    _ ≤ 128 * G + 128 * (2 ^ a * Bt) :=
      Nat.add_le_add hG hTailScaled
    _ = 128 * (G + 2 ^ a * Bt) := by ring
    _ = 128 * suffixGapBudget ([a, b, c, d] : Collatz.Word) := by
      rw [hrec]

/-- 最後5文字の budget ratio: `323/256`。 -/
private theorem ratio_five
    (a b c d e : ℕ)
    (hAll :
      AllSuffixesContracting
        ([a, b, c, d, e] : Collatz.Word)) :
    323 * 2 ^ twoSteps ([a, b, c, d, e] : Collatz.Word) ≤
      256 * suffixGapBudget ([a, b, c, d, e] : Collatz.Word) := by
  change
    Contracting ([a, b, c, d, e] : Collatz.Word) ∧
      AllSuffixesContracting ([b, c, d, e] : Collatz.Word)
    at hAll
  rcases hAll with ⟨hWhole, hTailAll⟩
  have hTail :=
    ratio_four b c d e hTailAll
  let A :=
    2 ^ twoSteps ([a, b, c, d, e] : Collatz.Word)
  let At :=
    2 ^ twoSteps ([b, c, d, e] : Collatz.Word)
  let G :=
    2 ^ twoSteps ([a, b, c, d, e] : Collatz.Word) -
      3 ^ oddSteps ([a, b, c, d, e] : Collatz.Word)
  let Bt :=
    suffixGapBudget ([b, c, d, e] : Collatz.Word)
  have hAeq :
      A = 2 ^ a * At := by
    dsimp only [A, At]
    rw [twoSteps_cons, pow_add]
  have hOdd :
      oddSteps ([a, b, c, d, e] : Collatz.Word) = 5 := by
    simp only [oddSteps_cons, oddSteps_nil]
  have hC0 :
      3 ^ oddSteps ([a, b, c, d, e] : Collatz.Word) <
        2 ^ twoSteps ([a, b, c, d, e] : Collatz.Word) := by
    exact hWhole
  have hC : 243 < A := by
    rw [hOdd] at hC0
    have h243 : (3 : ℕ) ^ 5 = 243 := by
      norm_num
    rw [h243] at hC0
    simpa only [A] using hC0
  have hk :
      8 ≤ twoSteps ([a, b, c, d, e] : Collatz.Word) :=
    eight_le_of_twoFortyThree_lt_twoPow
      (by simpa only [A] using hC)
  have hAmin : 256 ≤ A := by
    have hp :=
      Nat.pow_le_pow_right
        (by norm_num : 0 < (2 : ℕ)) hk
    simpa only [A] using hp
  have hgap : 243 + G = A := by
    dsimp only [G, A]
    rw [hOdd]
    norm_num
    exact Nat.add_sub_of_le (Nat.le_of_lt hC)
  have hG : 13 * A ≤ 256 * G := by
    omega
  have hTail' :
      155 * At ≤ 128 * Bt := by
    simpa only [At, Bt] using hTail
  have hTailScaled :
      310 * A ≤ 256 * (2 ^ a * Bt) := by
    calc
      310 * A
          = (2 * 2 ^ a) * (155 * At) := by
              rw [hAeq]
              ring
      _ ≤ (2 * 2 ^ a) * (128 * Bt) :=
        Nat.mul_le_mul_left _ hTail'
      _ = 256 * (2 ^ a * Bt) := by
        ring
  have hrec :
      suffixGapBudget ([a, b, c, d, e] : Collatz.Word) =
        G + 2 ^ a * Bt := by
    simp only [suffixGapBudget_cons]
    dsimp only [G, Bt]
    rfl
  calc
    323 * A
        = 13 * A + 310 * A := by
            ring
    _ ≤ 256 * G + 256 * (2 ^ a * Bt) :=
      Nat.add_le_add hG hTailScaled
    _ = 256 * (G + 2 ^ a * Bt) := by
      ring
    _ =
      256 *
        suffixGapBudget
          ([a, b, c, d, e] : Collatz.Word) := by
      rw [hrec]

/-- 最後6文字の budget ratio: `1587/1024`。 -/
private theorem ratio_six
    (a b c d e f : ℕ)
    (hAll :
      AllSuffixesContracting
        ([a, b, c, d, e, f] : Collatz.Word)) :
    1587 * 2 ^ twoSteps ([a, b, c, d, e, f] : Collatz.Word) ≤
      1024 * suffixGapBudget ([a, b, c, d, e, f] : Collatz.Word) := by
  change
    Contracting ([a, b, c, d, e, f] : Collatz.Word) ∧
      AllSuffixesContracting ([b, c, d, e, f] : Collatz.Word)
    at hAll
  rcases hAll with ⟨hWhole, hTailAll⟩
  have hTail :=
    ratio_five b c d e f hTailAll
  let A :=
    2 ^ twoSteps ([a, b, c, d, e, f] : Collatz.Word)
  let At :=
    2 ^ twoSteps ([b, c, d, e, f] : Collatz.Word)
  let G :=
    2 ^ twoSteps ([a, b, c, d, e, f] : Collatz.Word) -
      3 ^ oddSteps ([a, b, c, d, e, f] : Collatz.Word)
  let Bt :=
    suffixGapBudget ([b, c, d, e, f] : Collatz.Word)
  have hAeq :
      A = 2 ^ a * At := by
    dsimp only [A, At]
    rw [twoSteps_cons, pow_add]
  have hOdd :
      oddSteps ([a, b, c, d, e, f] : Collatz.Word) = 6 := by
    simp only [oddSteps_cons, oddSteps_nil]
  have hC0 :
      3 ^ oddSteps ([a, b, c, d, e, f] : Collatz.Word) <
        2 ^ twoSteps ([a, b, c, d, e, f] : Collatz.Word) := by
    exact hWhole
  have hC : 729 < A := by
    rw [hOdd] at hC0
    have h729 : (3 : ℕ) ^ 6 = 729 := by
      norm_num
    rw [h729] at hC0
    simpa only [A] using hC0
  have hk :
      10 ≤ twoSteps ([a, b, c, d, e, f] : Collatz.Word) :=
    ten_le_of_sevenTwentyNine_lt_twoPow
      (by simpa only [A] using hC)
  have hAmin : 1024 ≤ A := by
    have hp :=
      Nat.pow_le_pow_right
        (by norm_num : 0 < (2 : ℕ)) hk
    simpa only [A] using hp
  have hgap : 729 + G = A := by
    have h729 : (3 : ℕ) ^ 6 = 729 := by
      norm_num
    dsimp only [G, A]
    rw [hOdd, h729]
    exact
      Nat.add_sub_of_le
        (Nat.le_of_lt (by
          simpa only [A] using hC))
  have hG :
      295 * A ≤ 1024 * G := by
    omega
  have hTail' :
      323 * At ≤ 256 * Bt := by
    simpa only [At, Bt] using hTail
  have hTailScaled :
      1292 * A ≤ 1024 * (2 ^ a * Bt) := by
    calc
      1292 * A
          = (4 * 2 ^ a) * (323 * At) := by
              rw [hAeq]
              ring
      _ ≤ (4 * 2 ^ a) * (256 * Bt) :=
        Nat.mul_le_mul_left _ hTail'
      _ = 1024 * (2 ^ a * Bt) := by
        ring
  have hrec :
      suffixGapBudget ([a, b, c, d, e, f] : Collatz.Word) =
        G + 2 ^ a * Bt := by
    simp only [suffixGapBudget_cons]
    dsimp only [G, Bt]
    rfl
  calc
    1587 * A
        = 295 * A + 1292 * A := by
            ring
    _ ≤ 1024 * G + 1024 * (2 ^ a * Bt) :=
      Nat.add_le_add hG hTailScaled
    _ = 1024 * (G + 2 ^ a * Bt) := by
      ring
    _ =
      1024 *
        suffixGapBudget
          ([a, b, c, d, e, f] : Collatz.Word) := by
      rw [hrec]

/-- 最後7文字の budget ratio: `8257/4096 > 2`。 -/
private theorem ratio_seven
    (a b c d e f g : ℕ)
    (hAll :
      AllSuffixesContracting
        ([a, b, c, d, e, f, g] : Collatz.Word)) :
    8257 * 2 ^ twoSteps ([a, b, c, d, e, f, g] : Collatz.Word) ≤
      4096 * suffixGapBudget ([a, b, c, d, e, f, g] : Collatz.Word) := by
  change
    Contracting ([a, b, c, d, e, f, g] : Collatz.Word) ∧
      AllSuffixesContracting ([b, c, d, e, f, g] : Collatz.Word)
    at hAll
  rcases hAll with ⟨hWhole, hTailAll⟩
  have hTail :=
    ratio_six b c d e f g hTailAll
  let A :=
    2 ^ twoSteps ([a, b, c, d, e, f, g] : Collatz.Word)
  let At :=
    2 ^ twoSteps ([b, c, d, e, f, g] : Collatz.Word)
  let G :=
    2 ^ twoSteps ([a, b, c, d, e, f, g] : Collatz.Word) -
      3 ^ oddSteps ([a, b, c, d, e, f, g] : Collatz.Word)
  let Bt :=
    suffixGapBudget ([b, c, d, e, f, g] : Collatz.Word)
  have hAeq :
      A = 2 ^ a * At := by
    dsimp only [A, At]
    rw [twoSteps_cons, pow_add]
  have hOdd :
      oddSteps ([a, b, c, d, e, f, g] : Collatz.Word) = 7 := by
    simp only [oddSteps_cons, oddSteps_nil]
  have hC0 :
      3 ^ oddSteps ([a, b, c, d, e, f, g] : Collatz.Word) <
        2 ^ twoSteps ([a, b, c, d, e, f, g] : Collatz.Word) := by
    exact hWhole
  have hC : 2187 < A := by
    rw [hOdd] at hC0
    have h2187 : (3 : ℕ) ^ 7 = 2187 := by
      norm_num
    rw [h2187] at hC0
    simpa only [A] using hC0
  have hk :
      12 ≤ twoSteps ([a, b, c, d, e, f, g] : Collatz.Word) :=
    twelve_le_of_twoThousandOneEightySeven_lt_twoPow
      (by simpa only [A] using hC)
  have hAmin : 4096 ≤ A := by
    have hp :=
      Nat.pow_le_pow_right
        (by norm_num : 0 < (2 : ℕ)) hk
    simpa only [A] using hp
  have hgap : 2187 + G = A := by
    have h2187 : (3 : ℕ) ^ 7 = 2187 := by
      norm_num
    dsimp only [G, A]
    rw [hOdd, h2187]
    exact
      Nat.add_sub_of_le
        (Nat.le_of_lt (by
          simpa only [A] using hC))
  have hG :
      1909 * A ≤ 4096 * G := by
    omega
  have hTail' :
      1587 * At ≤ 1024 * Bt := by
    simpa only [At, Bt] using hTail
  have hTailScaled :
      6348 * A ≤ 4096 * (2 ^ a * Bt) := by
    calc
      6348 * A
          = (4 * 2 ^ a) * (1587 * At) := by
              rw [hAeq]
              ring
      _ ≤ (4 * 2 ^ a) * (1024 * Bt) :=
        Nat.mul_le_mul_left _ hTail'
      _ = 4096 * (2 ^ a * Bt) := by
        ring
  have hrec :
      suffixGapBudget ([a, b, c, d, e, f, g] : Collatz.Word) =
        G + 2 ^ a * Bt := by
    simp only [suffixGapBudget_cons]
    dsimp only [G, Bt]
    rfl
  calc
    8257 * A
        = 1909 * A + 6348 * A := by
            ring
    _ ≤ 4096 * G + 4096 * (2 ^ a * Bt) :=
      Nat.add_le_add hG hTailScaled
    _ = 4096 * (G + 2 ^ a * Bt) := by
      ring
    _ =
      4096 *
        suffixGapBudget
          ([a, b, c, d, e, f, g] : Collatz.Word) := by
      rw [hrec]

/--
prefixを捨てた residual budget は、元 budget の中にその prefix 2冪を掛けて含まれる。
-/
theorem twoPow_take_mul_suffixGapBudget_drop_le
    (w : Collatz.Word) :
    ∀ k : ℕ,
      2 ^ twoSteps (w.take k) * suffixGapBudget (w.drop k) ≤
        suffixGapBudget w := by
  intro k
  induction k generalizing w with
  | zero =>
      simp [twoSteps]
  | succ k ih =>
      cases w with
      | nil =>
          simp [twoSteps]
      | cons e w =>
          have htail := ih (w := w)
          have hmul :=
            Nat.mul_le_mul_left (2 ^ e) htail
          calc
            2 ^ twoSteps ((e :: w).take (k + 1)) *
                suffixGapBudget ((e :: w).drop (k + 1))
                =
              2 ^ e *
                (2 ^ twoSteps (w.take k) *
                  suffixGapBudget (w.drop k)) := by
                    simp [twoSteps_cons, pow_add, Nat.mul_assoc]
            _ ≤ 2 ^ e * suffixGapBudget w := hmul
            _ ≤
              (2 ^ twoSteps (e :: w) - 3 ^ oddSteps (e :: w)) +
                2 ^ e * suffixGapBudget w := by
                  omega
            _ = suffixGapBudget (e :: w) := rfl

private theorem ratio_four_of_length_eq
    {w : Collatz.Word}
    (hAll : AllSuffixesContracting w)
    (hlen : w.length = 4) :
    155 * 2 ^ twoSteps w ≤ 128 * suffixGapBudget w := by
  cases w with
  | nil =>
      simp at hlen
  | cons a w =>
      cases w with
      | nil =>
          simp at hlen
      | cons b w =>
          cases w with
          | nil =>
              simp at hlen
          | cons c w =>
              cases w with
              | nil =>
                  simp at hlen
              | cons d w =>
                  cases w with
                  | nil =>
                      simpa using ratio_four a b c d hAll
                  | cons e w =>
                      simp at hlen

private theorem ratio_seven_of_length_eq
    {w : Collatz.Word}
    (hAll : AllSuffixesContracting w)
    (hlen : w.length = 7) :
    8257 * 2 ^ twoSteps w ≤ 4096 * suffixGapBudget w := by
  cases w with
  | nil => simp at hlen
  | cons a w =>
    cases w with
    | nil => simp at hlen
    | cons b w =>
      cases w with
      | nil => simp at hlen
      | cons c w =>
        cases w with
        | nil => simp at hlen
        | cons d w =>
          cases w with
          | nil => simp at hlen
          | cons e w =>
            cases w with
            | nil => simp at hlen
            | cons f w =>
              cases w with
              | nil => simp at hlen
              | cons g w =>
                cases w with
                | nil =>
                    simpa using ratio_seven a b c d e f g hAll
                | cons h w =>
                    simp at hlen

/--
all-suffix-contracting word の長さが4以上なら
`suffixGapBudget > 2^H`。
-/
theorem AllSuffixesContracting.twoPow_lt_suffixGapBudget_of_four_le_length
    {w : Collatz.Word}
    (hAll : AllSuffixesContracting w)
    (hlen : 4 ≤ w.length) :
    2 ^ twoSteps w < suffixGapBudget w := by
  let k := w.length - 4
  let v := w.drop k
  have hvlen : v.length = 4 := by
    dsimp [v, k]
    simp
    omega
  have hvAll : AllSuffixesContracting v := by
    exact hAll.drop k
  have hratio := ratio_four_of_length_eq hvAll hvlen
  have hvStrict :
      2 ^ twoSteps v < suffixGapBudget v := by
    have hApos : 0 < 2 ^ twoSteps v :=
      Nat.pow_pos (by omega)
    nlinarith
  have hweight :=
    twoPow_take_mul_suffixGapBudget_drop_le w k
  have hsplit :
      twoSteps w =
        twoSteps (w.take k) + twoSteps v := by
    dsimp [v]
    rw [← twoSteps_append, List.take_append_drop]
  have hprefPos :
      0 < 2 ^ twoSteps (w.take k) :=
    Nat.pow_pos (by omega)
  have hmul :=
    (Nat.mul_lt_mul_left hprefPos).2 hvStrict
  calc
    2 ^ twoSteps w =
        2 ^ twoSteps (w.take k) * 2 ^ twoSteps v := by
          rw [hsplit, pow_add]
    _ < 2 ^ twoSteps (w.take k) * suffixGapBudget v := hmul
    _ ≤ suffixGapBudget w := by
      simpa [v] using hweight

/--
all-suffix-contracting word の長さが7以上なら
`suffixGapBudget > 2 * 2^H`。
-/
theorem AllSuffixesContracting.two_mul_twoPow_lt_suffixGapBudget_of_seven_le_length
    {w : Collatz.Word}
    (hAll : AllSuffixesContracting w)
    (hlen : 7 ≤ w.length) :
    2 * 2 ^ twoSteps w < suffixGapBudget w := by
  let k := w.length - 7
  let v := w.drop k
  have hvlen : v.length = 7 := by
    dsimp [v, k]
    simp
    omega
  have hvAll : AllSuffixesContracting v := by
    exact hAll.drop k
  have hratio := ratio_seven_of_length_eq hvAll hvlen
  have hvStrict :
      2 * 2 ^ twoSteps v < suffixGapBudget v := by
    have hApos : 0 < 2 ^ twoSteps v :=
      Nat.pow_pos (by omega)
    nlinarith
  have hweight :=
    twoPow_take_mul_suffixGapBudget_drop_le w k
  have hsplit :
      twoSteps w =
        twoSteps (w.take k) + twoSteps v := by
    dsimp [v]
    rw [← twoSteps_append, List.take_append_drop]
  have hprefPos :
      0 < 2 ^ twoSteps (w.take k) :=
    Nat.pow_pos (by omega)
  have hmul :=
    (Nat.mul_lt_mul_left hprefPos).2 hvStrict
  calc
    2 * 2 ^ twoSteps w =
        2 ^ twoSteps (w.take k) *
          (2 * 2 ^ twoSteps v) := by
            rw [hsplit, pow_add]
            ring
    _ < 2 ^ twoSteps (w.take k) * suffixGapBudget v := hmul
    _ ≤ suffixGapBudget w := by
      simpa [v] using hweight

end Word
end Collatz
