import CollatzLean.CollatzSecondLayer.C3Cylinder
import Mathlib.Tactic.Linarith

/-!
# Cylinder Upgradeの算術還元

first-crossing語のaffine定数上界とfuture-minimum不等式をLeanで証明し、
Bridge 2を次の純粋算術入力へ還元する。

* `TwoThreeGapPolynomialBound`:
  `3^p` と `2^H` の相対差に対するBaker型逆多項式下界。
* `PolynomialBelowTwoPower`:
  固定多項式は最終的に`2^p`より小さいという初等的成長事実。

前者はmathlib 4.32.2にBaker理論が未収録であるため、明示的入力として隔離する。
後者もAPI依存をBridge本体から分離するため同じ場所に置く。
-/

namespace CollatzSecondLayer

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

/--
`2^H-3^p`が`3^p`に対して逆多項式以上であるという、2と3専用のBaker入力。
-/
def TwoThreeGapPolynomialBound : Prop :=
  ∃ K A : ℕ,
    0 < K ∧
    ∀ p H : ℕ,
      0 < p →
      3 ^ p < 2 ^ H →
      3 ^ p ≤ K * (p + 1) ^ A * (2 ^ H - 3 ^ p)

/-- 固定多項式は最終的に`2^(p+1)`より小さい。 -/
def PolynomialBelowTwoPower : Prop :=
  ∀ K A : ℕ,
    ∃ N : ℕ,
      ∀ p : ℕ, N ≤ p →
        K * (p + 1) ^ A < 2 ^ (p + 1)

/-- prefix積に許される重み付き膨張条件。 -/
def WeightedPrefixBound
    (a c : ℕ) (w : ExpWord) : Prop :=
  ∀ j : ℕ, j < w.length →
    a * 2 ^ twoSteps (w.take j) ≤ c * 3 ^ j

/--
重み付きprefix boundからaffine定数を評価する。
`a=1,c=1`でfirst-crossing語へ適用する。
-/
theorem weighted_affineConst_le
    (w : ExpWord) (a c : ℕ)
    (h : WeightedPrefixBound a c w) :
    a * affineConst w ≤ w.length * c * 3 ^ w.length := by
  induction w generalizing a c with
  | nil => simp [affineConst]
  | cons e w ih =>
      have h0 : a ≤ c := by
        have hh := h 0 (by simp)
        simpa [WeightedPrefixBound, twoSteps] using hh
      have htail : WeightedPrefixBound (a * 2 ^ e) (c * 3) w := by
        intro j hj
        have hh := h (j + 1) (by simp; omega)
        simpa [WeightedPrefixBound, List.take_succ_cons,
          twoSteps_cons, pow_add, pow_succ,
          Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hh
      have hi := ih (a := a * 2 ^ e) (c := c * 3) htail
      calc
        a * affineConst (e :: w)
            = a * 3 ^ w.length + (a * 2 ^ e) * affineConst w := by
                simp [affineConst]
                ring
        _ ≤ c * 3 ^ w.length +
              (w.length * (c * 3) * 3 ^ w.length) := by
                exact Nat.add_le_add
                  (Nat.mul_le_mul_right _ h0)
                  hi
        _ ≤ (e :: w).length * c * 3 ^ (e :: w).length := by
                simp only [List.length_cons]
                rw [pow_succ]
                nlinarith [Nat.zero_le (c * 3 ^ w.length)]

/-- 長さ以内で切ったprefixのodd step数は、そのprefix長に等しい。 -/
lemma oddSteps_take_eq
    {w : ExpWord} {j : ℕ}
    (hj : j ≤ w.length) :
    oddSteps (w.take j) = j := by
  simp [oddSteps, List.length_take, Nat.min_eq_left hj]

/-- first-crossing語の各prefixは重み1で`3^j`以下。 -/
lemma firstCrossing_weightedPrefixBound
    {w : ExpWord} (hC : FirstCrossing w) :
    WeightedPrefixBound 1 1 w := by
  intro j hj
  by_cases hj0 : j = 0
  · subst j
    simp only [
      List.take_zero,
      twoSteps_nil,
      pow_zero,
      mul_one,
      Std.le_refl
    ]
  · have hjpos : 0 < j :=
      Nat.pos_of_ne_zero hj0
    have hE :
        Expanding (w.take j) :=
      hC.properExpanding j hjpos hj
    have hbound :
        2 ^ twoSteps (w.take j) ≤
          3 ^ oddSteps (w.take j) := by
      unfold Expanding at hE
      exact Nat.le_of_lt hE
    have hodd :
        oddSteps (w.take j) = j :=
      oddSteps_take_eq (Nat.le_of_lt hj)
    simpa [WeightedPrefixBound, hodd] using hbound

/-- first-crossing語では`B_w ≤ p·3^p`。 -/
theorem affineConst_le_length_mul_threePow
    {w : ExpWord} (hC : FirstCrossing w) :
    affineConst w ≤ w.length * 3 ^ w.length := by
  have h := weighted_affineConst_le w 1 1
      (firstCrossing_weightedPrefixBound hC)
  simpa using h

/-- first-crossing cylinderの開始値へ相対gapを掛けるとaffine定数以下。 -/
theorem gap_mul_start_le_affineConst
    {O : OddOrbit} (C : FirstCrossingCylinder O) :
    (2 ^ twoSteps C.word - 3 ^ oddSteps C.word) * C.start ≤
      affineConst C.word := by
  have hrun := C.run.realizes
  have hend := C.terminal_ge_start
  have hscaled :
      2 ^ twoSteps C.word * C.start ≤
        3 ^ oddSteps C.word * C.start +
          affineConst C.word := by
    calc
      2 ^ twoSteps C.word * C.start
          ≤ 2 ^ twoSteps C.word * C.finish :=
        Nat.mul_le_mul_left _ hend
      _ = 3 ^ oddSteps C.word * C.start +
            affineConst C.word :=
        hrun
  have hcontract :
      3 ^ oddSteps C.word <
        2 ^ twoSteps C.word := by
    exact C.firstCrossing.terminalContracting
  have hsub :
      2 ^ twoSteps C.word =
        3 ^ oddSteps C.word +
          (2 ^ twoSteps C.word - 3 ^ oddSteps C.word) := by
    exact (Nat.add_sub_of_le hcontract.le).symm
  have hcancel :
      3 ^ oddSteps C.word * C.start +
          (2 ^ twoSteps C.word - 3 ^ oddSteps C.word) * C.start
        ≤
      3 ^ oddSteps C.word * C.start +
          affineConst C.word := by
    calc
      3 ^ oddSteps C.word * C.start +
          (2 ^ twoSteps C.word - 3 ^ oddSteps C.word) * C.start
          =
          (3 ^ oddSteps C.word +
            (2 ^ twoSteps C.word - 3 ^ oddSteps C.word)) *
              C.start := by
            ring
      _ = 2 ^ twoSteps C.word * C.start := by
            rw [← hsub]
      _ ≤ 3 ^ oddSteps C.word * C.start +
            affineConst C.word :=
        hscaled
  exact Nat.le_of_add_le_add_left hcancel

/-- first-crossing cylinderの語長は正である。 -/
lemma firstCrossingCylinder_word_length_pos
    {O : OddOrbit}
    (C : FirstCrossingCylinder O) :
    0 < C.word.length := by
  exact List.length_pos_of_ne_nil C.firstCrossing.nonempty


/-- first-crossing終端の乗法gapは正である。 -/
lemma firstCrossingCylinder_gap_pos
    {O : OddOrbit}
    (C : FirstCrossingCylinder O) :
    0 <
      2 ^ twoSteps C.word -
        3 ^ oddSteps C.word := by
  have hcontract :
      3 ^ oddSteps C.word <
        2 ^ twoSteps C.word :=
    C.firstCrossing.terminalContracting
  exact Nat.sub_pos_of_lt hcontract


/--
first-crossing cylinderでは、
乗法gapと開始値の積は`length * 3^length`以下である。
-/
lemma gap_mul_start_le_length_mul_threePow
    {O : OddOrbit}
    (C : FirstCrossingCylinder O) :
    (2 ^ twoSteps C.word - 3 ^ oddSteps C.word) *
        C.start
      ≤
    C.word.length * 3 ^ C.word.length := by
  calc
    (2 ^ twoSteps C.word - 3 ^ oddSteps C.word) *
          C.start
        ≤ affineConst C.word :=
      gap_mul_start_le_affineConst C
    _ ≤ C.word.length * 3 ^ C.word.length :=
      affineConst_le_length_mul_threePow C.firstCrossing


/--
`p ≤ p + 1`を用いて多項式次数を一つ増やす算術補題。
-/
lemma length_mul_polynomial_gap_le_next_power
    (p K A g : ℕ) :
    p * (K * (p + 1) ^ A * g)
      ≤
    g * (K * (p + 1) ^ (A + 1)) := by
  have hpstep :
      p * (K * (p + 1) ^ A)
        ≤
      (p + 1) * (K * (p + 1) ^ A) :=
    Nat.mul_le_mul_right
      (K * (p + 1) ^ A)
      (Nat.le_succ p)
  have hgstep :
      (p * (K * (p + 1) ^ A)) * g
        ≤
      ((p + 1) * (K * (p + 1) ^ A)) * g :=
    Nat.mul_le_mul_right g hpstep
  calc
    p * (K * (p + 1) ^ A * g)
        =
      (p * (K * (p + 1) ^ A)) * g := by
        ring
    _ ≤ ((p + 1) * (K * (p + 1) ^ A)) * g :=
      hgstep
    _ = g * (K * (p + 1) ^ (A + 1)) := by
      rw [pow_succ]
      ring


/--
gap付きの開始値評価と`3^p`のgap下界から、
開始値の多項式上界を得る。
-/
lemma start_le_polynomial_of_gap_bound
    {p g X K A : ℕ}
    (hg : 0 < g)
    (hGX :
      g * X ≤ p * 3 ^ p)
    (hthree :
      3 ^ p ≤ K * (p + 1) ^ A * g) :
    X ≤ K * (p + 1) ^ (A + 1) := by
  have hchain :
      g * X
        ≤
      g * (K * (p + 1) ^ (A + 1)) := by
    calc
      g * X
          ≤ p * 3 ^ p :=
        hGX
      _ ≤ p * (K * (p + 1) ^ A * g) :=
        Nat.mul_le_mul_left p hthree
      _ ≤ g * (K * (p + 1) ^ (A + 1)) :=
        length_mul_polynomial_gap_le_next_power
          p K A g
  exact Nat.le_of_mul_le_mul_left hchain hg

/-- cylinderに保存されたfirst-crossingは、その`word`全体で収縮する。 -/
lemma FirstCrossingCylinder.word_contracting
    {O : OddOrbit}
    (C : FirstCrossingCylinder O) :
    Contracting C.word := by
  simpa [FirstCrossingCylinder.word] using
    C.firstCrossing.terminalContracting

/--
Baker型gap下界から、
各first-crossing cylinderの開始値を多項式で抑える。
-/
theorem firstCrossing_start_polynomial
    (hBaker : TwoThreeGapPolynomialBound) :
    ∃ K A : ℕ,
      ∀ O : OddOrbit,
      ∀ C : FirstCrossingCylinder O,
        C.start ≤ K * (C.length + 1) ^ A := by
  rcases hBaker with ⟨K, A, hK, hgap⟩
  refine ⟨K, A + 1, ?_⟩
  intro O C
  let p := C.word.length
  let H := twoSteps C.word
  let g := 2 ^ H - 3 ^ p
  have hp : 0 < p := by
    dsimp [p]
    exact firstCrossingCylinder_word_length_pos C
  have hterminal : Contracting C.word :=
    C.word_contracting
  have hcontract :
      3 ^ p < 2 ^ H := by
    unfold Contracting at hterminal
    simpa [p, H, oddSteps] using hterminal
  have hg : 0 < g := by
    dsimp [g]
    exact Nat.sub_pos_of_lt hcontract
  have hg : 0 < g := by
    dsimp [g]
    exact Nat.sub_pos_of_lt hcontract
  have hGX :
      g * C.start ≤ p * 3 ^ p := by
    simpa [g, H, p, oddSteps] using
      gap_mul_start_le_length_mul_threePow C
  have hthree :
      3 ^ p ≤ K * (p + 1) ^ A * g :=
    hgap p H hp hcontract
  have hstart :
      C.start ≤ K * (p + 1) ^ (A + 1) :=
    start_le_polynomial_of_gap_bound
      hg hGX hthree
  simpa [p, FirstCrossingCylinder.word] using hstart

/-- first-crossing列の第`j`項をcylinderとして束ねる。 -/
def firstCrossingCylinderOf
    {O : OddOrbit} (F : FirstCrossingSequenceData O)
    (j : ℕ) : FirstCrossingCylinder O where
  limit := F.limit
  sequenceIndex := j
  length := F.crossingLength j
  firstCrossing := F.crossing j

/--
first-crossing cylinderの語長は、
その語の総2除算数以下である。
-/
lemma firstCrossingCylinder_length_le_twoSteps
    {O : OddOrbit}
    (C : FirstCrossingCylinder O) :
    C.length ≤ twoSteps C.word := by
  have hvalid : Valid C.word :=
    C.run.valid
  have hsteps :
      oddSteps C.word ≤ twoSteps C.word :=
    oddSteps_le_twoSteps hvalid
  simpa [FirstCrossingCylinder.word, oddSteps] using hsteps


/--
多項式上界が`2^(length+1)`より小さくなる長さでは、
first-crossing cylinderの開始値はcanonical modulusより小さい。
-/
lemma firstCrossingCylinder_start_lt_modulus_of_length_ge
    {O : OddOrbit}
    (C : FirstCrossingCylinder O)
    {K A N : ℕ}
    (hheight :
      C.start ≤ K * (C.length + 1) ^ A)
    (hpow :
      ∀ m : ℕ,
        N ≤ m →
        K * (m + 1) ^ A < 2 ^ (m + 1))
    (hlen : N ≤ C.length) :
    C.start < residueModulus C.word := by
  have hpoly :
      K * (C.length + 1) ^ A <
        2 ^ (C.length + 1) :=
    hpow C.length hlen
  have hsteps :
      C.length ≤ twoSteps C.word :=
    firstCrossingCylinder_length_le_twoSteps C
  have hexponent :
      C.length + 1 ≤ twoSteps C.word + 1 := by
    omega
  have hpowle :
      2 ^ (C.length + 1) ≤
        2 ^ (twoSteps C.word + 1) := by
    exact Nat.pow_le_pow_right
      (by omega : 0 < (2 : ℕ))
      hexponent
  calc
    C.start
        ≤ K * (C.length + 1) ^ A :=
      hheight
    _ < 2 ^ (C.length + 1) :=
      hpoly
    _ ≤ 2 ^ (twoSteps C.word + 1) :=
      hpowle
    _ = residueModulus C.word := by
      rfl


/--
first-crossing列を位置`J`だけ後ろへずらして得るcylinder列。
-/
def shiftedFirstCrossingCylinder
    {O : OddOrbit}
    (F : FirstCrossingSequenceData O)
    (J j : ℕ) :
    FirstCrossingCylinder O :=
  firstCrossingCylinderOf F (J + j)


/--
任意の閾値`N`に対して、列を十分後ろへずらせば、
すべてのcylinder長を`N`以上にできる。
-/
lemma exists_shift_all_firstCrossing_lengths_ge
    {O : OddOrbit}
    (F : FirstCrossingSequenceData O)
    (N : ℕ) :
    ∃ J : ℕ,
      ∀ j : ℕ,
        N ≤ (shiftedFirstCrossingCylinder F J j).length := by
  obtain ⟨J, hJ⟩ :=
    F.lengths_tend_to_infinity N
  refine ⟨J, ?_⟩
  intro j
  have hlength :
      N <
        (firstCrossingCylinderOf F (J + j)).length := by
    have h :=
      hJ (J + j) (by omega)
    simpa [firstCrossingCylinderOf] using h
  simpa [shiftedFirstCrossingCylinder] using
    Nat.le_of_lt hlength


/--
first-crossing列を有限位置だけずらしても、
cylinder長が無限大へ進む性質は保存される。
-/
lemma shiftedFirstCrossing_lengths_tend_to_infinity
    {O : OddOrbit}
    (F : FirstCrossingSequenceData O)
    (J : ℕ) :
    ∀ M : ℕ,
      ∃ J₂ : ℕ,
        ∀ j : ℕ,
          J₂ ≤ j →
          M < (shiftedFirstCrossingCylinder F J j).length := by
  intro M
  obtain ⟨J₂, hJ₂⟩ :=
    F.lengths_tend_to_infinity M
  refine ⟨J₂, ?_⟩
  intro j hj
  have h :=
    hJ₂ (J + j) (by omega)
  simpa [
    shiftedFirstCrossingCylinder,
    firstCrossingCylinderOf
  ] using h


/--
元のfirst-crossing cylinderに対する一様な多項式上界は、
有限位置だけずらした列にも保存される。
-/
lemma shiftedFirstCrossing_polynomialSmall
    {O : OddOrbit}
    (F : FirstCrossingSequenceData O)
    (J K A : ℕ)
    (hheight :
      ∀ C : FirstCrossingCylinder O,
        C.start ≤ K * (C.length + 1) ^ A) :
    ∀ j : ℕ,
      (shiftedFirstCrossingCylinder F J j).start ≤
        K *
          ((shiftedFirstCrossingCylinder F J j).length + 1) ^ A := by
  intro j
  exact hheight (shiftedFirstCrossingCylinder F J j)

/--
Baker型gap下界と初等的指数優越から
Cylinder Upgradeを構成する。
-/
theorem cylinderUpgradePrinciple_of_arithmetic
    (hBaker : TwoThreeGapPolynomialBound)
    (hPow : PolynomialBelowTwoPower) :
    CylinderUpgradePrinciple := by
  obtain ⟨K, A, hheight⟩ :=
    firstCrossing_start_polynomial hBaker
  intro O F
  obtain ⟨N, hN⟩ :=
    hPow K A
  obtain ⟨J, hlength⟩ :=
    exists_shift_all_firstCrossing_lengths_ge F N
  let C : ℕ → FirstCrossingCylinder O :=
    fun j => shiftedFirstCrossingCylinder F J j
  have hcanonical :
      ∀ j : ℕ,
        (C j).start < residueModulus (C j).word := by
    intro j
    apply firstCrossingCylinder_start_lt_modulus_of_length_ge
      (C := C j)
      (K := K)
      (A := A)
      (N := N)
    · exact hheight O (C j)
    · exact hN
    · simpa [C] using hlength j
  let CC : ℕ → CanonicalC3Cylinder O :=
    fun j =>
      {
        C j with
        start_lt_modulus := hcanonical j
      }
  refine ⟨{
    cylinder := CC

    lengths_tend_to_infinity := by
      intro M
      obtain ⟨J₂, hJ₂⟩ :=
        shiftedFirstCrossing_lengths_tend_to_infinity F J M
      refine ⟨J₂, ?_⟩
      intro j hj
      have hlengthC :
          M < (C j).length := by
        simpa [C] using hJ₂ j hj
      simpa [CC] using hlengthC

    polynomialSmall := by
      refine ⟨K, A, ?_⟩
      intro j
      have hsmall :
          (C j).start ≤
            K * ((C j).length + 1) ^ A :=
        hheight O (C j)
      simpa [CC] using hsmall
  }⟩

end CollatzSecondLayer
