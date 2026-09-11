import CollatzLean.Collatz3.Experimental2.GenericRecordFerrers.OstrowskiRecordFerrers
import Mathlib.Algebra.ContinuedFractions.Computation.ApproximationCorollaries
import Mathlib.NumberTheory.DiophantineApproximation.ContinuedFractions
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Linarith

/-!
# Collatz3 Experimental2: 任意無理回転に対する RotationOstrowskiSystem の存在

`RotationOstrowskiSystem α` はこれまで、任意無理回転 `α ∈ (0,1)` に対する
Ostrowski / continued-fraction certificate として外から与えていた。

このファイルでは、その存在を `mathlib` の正規連分数 `GenContFract.of` から構成する。

`σ = 1 + α` とおくと `1 < σ < 2` かつ `σ` は無理数である。
従って正規連分数は

`[1; a₀, a₁, ...]`

という無限展開を持つ。各 partial quotient を自然数 `a n` として取り出し、

* `P 0 = 1`, `Q 0 = 1`,
* `P 1 = a 0`, `Q 1 = a 0 + 1`,
* `P (n+2) = a (n+1) P (n+1) + P n`,
* `Q (n+2) = a (n+1) Q (n+1) + Q n`

で `UnitOstrowskiConvergentSystem` を作る。

`mathlib` の convergent とこの `(P,Q)` が exact に一致することを証明し、
continued-fraction の有限 exact error formulaから

* 偶数 index では `Q_n/P_n < σ < Q_{n+1}/P_{n+1}`、
* 奇数 index では向きが逆

を得る。さらに simple continued fraction の determinant formula を用いて
Farey determinant `±1` を回収する。

これにより `RotationOstrowskiSystem α` を実際に構成し、最後に

`IsIrrationalUnitRotation α → Nonempty (RotationOstrowskiSystem α)`

を閉じる。
-/

namespace Collatz3
namespace Experimental2
namespace GenericRecordFerrers

open GenContFract

namespace RotationOstrowskiExistence

/-- 無理数の正規連分数計算はどの有限段でも停止しない。 -/
theorem of_not_terminatedAt_of_irrational
    {σ : ℝ}
    (hσ : Irrational σ)
    (n : ℕ) :
    ¬ (GenContFract.of σ).TerminatedAt n := by
  intro hTerm
  have hEq : σ = (GenContFract.of σ).convs n :=
    GenContFract.of_correctness_of_terminatedAt hTerm
  rw [Real.convs_eq_convergent] at hEq
  exact (hσ.ne_rat (σ.convergent n)) hEq

/-- 無理数の continued-fraction stream は全 index で実値を持つ。 -/
theorem exists_streamPair
    {σ : ℝ}
    (hσ : Irrational σ)
    (n : ℕ) :
    ∃ p : GenContFract.IntFractPair ℝ,
      GenContFract.IntFractPair.stream σ n = some p := by
  cases n with
  | zero =>
      exact ⟨GenContFract.IntFractPair.of σ, rfl⟩
  | succ n =>
      have hNotTerm := of_not_terminatedAt_of_irrational hσ n
      have hNotNone :
          GenContFract.IntFractPair.stream σ (n + 1) ≠ none := by
        intro hNone
        exact hNotTerm
          ((GenContFract.of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none).2 hNone)
      exact Option.ne_none_iff_exists'.1 hNotNone

/-- 無理数の regular continued fraction stream の canonical witness。 -/
noncomputable def streamPair
    (σ : ℝ)
    (hσ : Irrational σ)
    (n : ℕ) : GenContFract.IntFractPair ℝ :=
  Classical.choose (exists_streamPair hσ n)

/-- `streamPair` は元の continued-fraction stream のその index の値。 -/
theorem streamPair_spec
    (σ : ℝ)
    (hσ : Irrational σ)
    (n : ℕ) :
    GenContFract.IntFractPair.stream σ n =
      some (streamPair σ hσ n) :=
  Classical.choose_spec (exists_streamPair hσ n)

/-- 無理数なので、どの stream residual も `0` にはならない。 -/
theorem streamPair_fr_ne_zero
    (σ : ℝ)
    (hσ : Irrational σ)
    (n : ℕ) :
    (streamPair σ hσ n).fr ≠ 0 := by
  intro hZero
  have hNone :=
    GenContFract.IntFractPair.stream_eq_none_of_fr_eq_zero
      (streamPair_spec σ hσ n) hZero
  have hTerm : (GenContFract.of σ).TerminatedAt n :=
    (GenContFract.of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none).2 hNone
  exact of_not_terminatedAt_of_irrational hσ n hTerm

/--
`[⌊σ⌋; a₀,a₁,...]` の `aₙ`。
stream の `(n+1)` 番目の整数部分を自然数化する。
-/
noncomputable def partialQuotient
    (σ : ℝ)
    (hσ : Irrational σ)
    (n : ℕ) : ℕ :=
  (streamPair σ hσ (n + 1)).b.toNat

/-- regular continued fraction の partial quotient は正。 -/
theorem partialQuotient_pos
    (σ : ℝ)
    (hσ : Irrational σ)
    (n : ℕ) :
    0 < partialQuotient σ hσ n := by
  have hStream := streamPair_spec σ hσ (n + 1)
  have hb : (1 : ℤ) ≤ (streamPair σ hσ (n + 1)).b :=
    GenContFract.IntFractPair.one_le_succ_nth_stream_b hStream
  have hb0 : (0 : ℤ) ≤ (streamPair σ hσ (n + 1)).b := by
    omega
  have hbNat :
      (1 : ℤ) ≤ ((partialQuotient σ hσ n : ℕ) : ℤ) := by
    unfold partialQuotient
    rw [Int.toNat_of_nonneg hb0]
    exact hb
  exact_mod_cast hbNat

/-- partial quotient の自然数化を実数へ戻すと元の stream 整数部分になる。 -/
theorem partialQuotient_cast
    (σ : ℝ)
    (hσ : Irrational σ)
    (n : ℕ) :
    (partialQuotient σ hσ n : ℝ) =
      ((streamPair σ hσ (n + 1)).b : ℝ) := by
  have hStream := streamPair_spec σ hσ (n + 1)
  have hb : (1 : ℤ) ≤ (streamPair σ hσ (n + 1)).b :=
    GenContFract.IntFractPair.one_le_succ_nth_stream_b hStream
  have hb0 : (0 : ℤ) ≤ (streamPair σ hσ (n + 1)).b := by
    omega
  have hInt :
      ((partialQuotient σ hσ n : ℕ) : ℤ) =
        (streamPair σ hσ (n + 1)).b := by
    unfold partialQuotient
    exact Int.toNat_of_nonneg hb0
  exact_mod_cast hInt

/-- regular continued fraction の denominator 側 recurrence。 -/
def regularP
    (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | 1 => a 0
  | n + 2 => a (n + 1) * regularP a (n + 1) + regularP a n

/-- regular continued fraction の numerator 側 recurrence。 -/
def regularQ
    (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | 1 => a 0 + 1
  | n + 2 => a (n + 1) * regularQ a (n + 1) + regularQ a n

/--
無理数 `σ` の regular continued fraction から、repo の自然数 recurrence 形式の
`UnitOstrowskiConvergentSystem` を構成する。
-/
noncomputable def convergentSystem
    (σ : ℝ)
    (hσ : Irrational σ) :
    UnitOstrowskiConvergentSystem where
  a := partialQuotient σ hσ
  P := regularP (partialQuotient σ hσ)
  Q := regularQ (partialQuotient σ hσ)
  a_pos := partialQuotient_pos σ hσ
  q_zero := rfl
  q_one := rfl
  q_rec := by
    intro n
    rfl
  p_zero := rfl
  p_one := rfl
  p_rec := by
    intro n
    rfl

/-- `mathlib` の GCF sequence coefficient は `partialQuotient` と一致する。 -/
theorem of_s_eq_partialQuotient
    (σ : ℝ)
    (hσ : Irrational σ)
    (n : ℕ) :
    (GenContFract.of σ).s.get? n =
      some ⟨(1 : ℝ), (partialQuotient σ hσ n : ℝ)⟩ := by
  have hStream := streamPair_spec σ hσ (n + 1)
  have h :=
    GenContFract.get?_of_eq_some_of_succ_get?_intFractPair_stream hStream
  rw [partialQuotient_cast σ hσ n]
  exact h

/--
`floor σ = 1` のとき、mathlib convergent の numerator は `regularQ` と一致する。
-/
theorem of_nums_eq_regularQ
    (σ : ℝ)
    (hσ : Irrational σ)
    (hFloor : ⌊σ⌋ = (1 : ℤ)) :
    ∀ n : ℕ,
      (GenContFract.of σ).nums n =
        (regularQ (partialQuotient σ hσ) n : ℝ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with (_ | _ | n)
      · simp [regularQ, hFloor]
      · have hS := of_s_eq_partialQuotient σ hσ 0
        have hFirst := GenContFract.first_num_eq hS
        rw [GenContFract.of_h_eq_floor, hFloor] at hFirst
        simpa [regularQ] using hFirst
      · have hPrev := ih n (by omega)
        have hCurrent := ih (n + 1) (by omega)
        have hS := of_s_eq_partialQuotient σ hσ (n + 1)
        have hRec :=
          GenContFract.nums_recurrence hS hPrev hCurrent
        simpa [regularQ] using hRec

/--
任意の無理数 `σ` について、mathlib convergent の denominator は
`regularP (partialQuotient σ hσ)` と一致する。
-/
theorem of_dens_eq_regularP
    (σ : ℝ)
    (hσ : Irrational σ) :
    ∀ n : ℕ,
      (GenContFract.of σ).dens n =
        (regularP (partialQuotient σ hσ) n : ℝ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with (_ | _ | n)
      · simp [regularP]
      · have hS := of_s_eq_partialQuotient σ hσ 0
        have hFirst := GenContFract.first_den_eq hS
        simpa [regularP] using hFirst
      · have hPrev := ih n (by omega)
        have hCurrent := ih (n + 1) (by omega)
        have hS := of_s_eq_partialQuotient σ hσ (n + 1)
        have hRec :=
          GenContFract.dens_recurrence hS hPrev hCurrent
        simpa [regularP] using hRec

/-- mathlib convergent は構成した `(P,Q)` の比 `Q/P` そのもの。 -/
theorem of_convs_eq_regularQ_div_regularP
    (σ : ℝ)
    (hσ : Irrational σ)
    (hFloor : ⌊σ⌋ = (1 : ℤ))
    (n : ℕ) :
    (GenContFract.of σ).convs n =
      (regularQ (partialQuotient σ hσ) n : ℝ) /
        (regularP (partialQuotient σ hσ) n : ℝ) := by
  rw [GenContFract.conv_eq_num_div_den,
    of_nums_eq_regularQ σ hσ hFloor n,
    of_dens_eq_regularP σ hσ n]

/-- `sub_convs_eq` に現れる現在 denominator は正。 -/
theorem current_contsAux_den_pos
    (σ : ℝ)
    (hσ : Irrational σ)
    (n : ℕ) :
    0 < ((GenContFract.of σ).contsAux (n + 1)).b := by
  rw [← GenContFract.nth_cont_eq_succ_nth_contAux]
  rw [← GenContFract.den_eq_conts_b]
  rw [of_dens_eq_regularP σ hσ n]
  exact_mod_cast (convergentSystem σ hσ).p_pos n

/-- 偶数 convergent は無理数 `σ` の strict lower approximation。 -/
theorem conv_lt_of_even
    (σ : ℝ)
    (hσ : Irrational σ)
    {n : ℕ}
    (hn : Even n) :
    (GenContFract.of σ).convs n < σ := by
  let p := streamPair σ hσ n
  have hp : GenContFract.IntFractPair.stream σ n = some p := by
    simpa [p] using streamPair_spec σ hσ n
  have hfr0 : p.fr ≠ 0 := by
    simpa [p] using streamPair_fr_ne_zero σ hσ n
  have hfrNonneg : 0 ≤ p.fr :=
    GenContFract.IntFractPair.nth_stream_fr_nonneg hp
  have hfrPos : 0 < p.fr :=
    lt_of_le_of_ne hfrNonneg (Ne.symm hfr0)
  have hB : 0 < ((GenContFract.of σ).contsAux (n + 1)).b :=
    current_contsAux_den_pos σ hσ n
  have hpB : 0 ≤ ((GenContFract.of σ).contsAux n).b := by
    simpa using
      (GenContFract.zero_le_of_contsAux_b (v := σ) (n := n))
  have hDen :
      0 <
        ((GenContFract.of σ).contsAux (n + 1)).b *
          (p.fr⁻¹ * ((GenContFract.of σ).contsAux (n + 1)).b +
            ((GenContFract.of σ).contsAux n).b) := by
    have hInv : 0 < p.fr⁻¹ := inv_pos.mpr hfrPos
    positivity
  have hErr := GenContFract.sub_convs_eq (v := σ) (n := n) hp
  have hPow : ((-1 : ℝ) ^ n) = 1 := hn.neg_one_pow
  have hErr' :
      σ - (GenContFract.of σ).convs n =
        1 /
          (((GenContFract.of σ).contsAux (n + 1)).b *
            (p.fr⁻¹ * ((GenContFract.of σ).contsAux (n + 1)).b +
              ((GenContFract.of σ).contsAux n).b)) := by
    simpa [hfr0, hPow] using hErr
  have hPos : 0 < σ - (GenContFract.of σ).convs n := by
    rw [hErr']
    positivity
  linarith

/-- 奇数 convergent は無理数 `σ` の strict upper approximation。 -/
theorem lt_conv_of_odd
    (σ : ℝ)
    (hσ : Irrational σ)
    {n : ℕ}
    (hn : Odd n) :
    σ < (GenContFract.of σ).convs n := by
  let p := streamPair σ hσ n
  have hp : GenContFract.IntFractPair.stream σ n = some p := by
    simpa [p] using streamPair_spec σ hσ n
  have hfr0 : p.fr ≠ 0 := by
    simpa [p] using streamPair_fr_ne_zero σ hσ n
  have hfrNonneg : 0 ≤ p.fr :=
    GenContFract.IntFractPair.nth_stream_fr_nonneg hp
  have hfrPos : 0 < p.fr :=
    lt_of_le_of_ne hfrNonneg (Ne.symm hfr0)
  have hB : 0 < ((GenContFract.of σ).contsAux (n + 1)).b :=
    current_contsAux_den_pos σ hσ n
  have hpB : 0 ≤ ((GenContFract.of σ).contsAux n).b := by
    simpa using
      (GenContFract.zero_le_of_contsAux_b (v := σ) (n := n))
  have hDen :
      0 <
        ((GenContFract.of σ).contsAux (n + 1)).b *
          (p.fr⁻¹ * ((GenContFract.of σ).contsAux (n + 1)).b +
            ((GenContFract.of σ).contsAux n).b) := by
    have hInv : 0 < p.fr⁻¹ := inv_pos.mpr hfrPos
    positivity
  have hErr := GenContFract.sub_convs_eq (v := σ) (n := n) hp
  have hPow : ((-1 : ℝ) ^ n) = -1 := hn.neg_one_pow
  have hErr' :
      σ - (GenContFract.of σ).convs n =
        (-1 : ℝ) /
          (((GenContFract.of σ).contsAux (n + 1)).b *
            (p.fr⁻¹ * ((GenContFract.of σ).contsAux (n + 1)).b +
              ((GenContFract.of σ).contsAux n).b)) := by
    simpa [hfr0, hPow] using hErr
  have hNeg : σ - (GenContFract.of σ).convs n < 0 := by
    rw [hErr']
    exact div_neg_of_neg_of_pos (by norm_num) hDen
  linarith

/-- 偶数 index の隣接 convergent は lower Farey determinant orientation を持つ。 -/
theorem lower_determinant_of_even
    (σ : ℝ)
    (hσ : Irrational σ)
    (hFloor : ⌊σ⌋ = (1 : ℤ))
    {n : ℕ}
    (hn : Even n) :
    regularP (partialQuotient σ hσ) (n + 1) *
          regularQ (partialQuotient σ hσ) n + 1 =
      regularP (partialQuotient σ hσ) n *
          regularQ (partialQuotient σ hσ) (n + 1) := by
  have hNotTerm := of_not_terminatedAt_of_irrational hσ n
  have hDet := (SimpContFract.of σ).determinant hNotTerm
  change
    (GenContFract.of σ).nums n * (GenContFract.of σ).dens (n + 1) -
        (GenContFract.of σ).dens n * (GenContFract.of σ).nums (n + 1) =
      ((-1 : ℝ) ^ (n + 1)) at hDet
  rw [of_nums_eq_regularQ σ hσ hFloor n,
      of_dens_eq_regularP σ hσ (n + 1),
      of_dens_eq_regularP σ hσ n,
      of_nums_eq_regularQ σ hσ hFloor (n + 1)] at hDet
  have hOdd : Odd (n + 1) := hn.add_one
  rw [hOdd.neg_one_pow] at hDet
  have hDet' :
      (regularP (partialQuotient σ hσ) (n + 1) : ℝ) *
            (regularQ (partialQuotient σ hσ) n : ℝ) + 1 =
        (regularP (partialQuotient σ hσ) n : ℝ) *
            (regularQ (partialQuotient σ hσ) (n + 1) : ℝ) := by
    nlinarith [hDet]
  exact_mod_cast hDet'

/-- 奇数 index の隣接 convergent は upper Farey determinant orientation を持つ。 -/
theorem upper_determinant_of_odd
    (σ : ℝ)
    (hσ : Irrational σ)
    (hFloor : ⌊σ⌋ = (1 : ℤ))
    {n : ℕ}
    (hn : Odd n) :
    regularP (partialQuotient σ hσ) n *
          regularQ (partialQuotient σ hσ) (n + 1) + 1 =
      regularP (partialQuotient σ hσ) (n + 1) *
          regularQ (partialQuotient σ hσ) n := by
  have hNotTerm := of_not_terminatedAt_of_irrational hσ n
  have hDet := (SimpContFract.of σ).determinant hNotTerm
  change
    (GenContFract.of σ).nums n * (GenContFract.of σ).dens (n + 1) -
        (GenContFract.of σ).dens n * (GenContFract.of σ).nums (n + 1) =
      ((-1 : ℝ) ^ (n + 1)) at hDet
  rw [of_nums_eq_regularQ σ hσ hFloor n,
      of_dens_eq_regularP σ hσ (n + 1),
      of_dens_eq_regularP σ hσ n,
      of_nums_eq_regularQ σ hσ hFloor (n + 1)] at hDet
  have hEven : Even (n + 1) := hn.add_one
  rw [hEven.neg_one_pow] at hDet
  have hDet' :
      (regularP (partialQuotient σ hσ) n : ℝ) *
            (regularQ (partialQuotient σ hσ) (n + 1) : ℝ) + 1 =
        (regularP (partialQuotient σ hσ) (n + 1) : ℝ) *
            (regularQ (partialQuotient σ hσ) n : ℝ) := by
    nlinarith [hDet]
  exact_mod_cast hDet'

/-- `1+α` は `α` が無理なら無理数。 -/
theorem one_add_irrational
    {α : ℝ}
    (A : IsIrrationalUnitRotation α) :
    Irrational (1 + α) := by
  have h := A.irrational.natCast_add 1
  simpa using h

/-- `0<α<1` なら `floor(1+α)=1`。 -/
theorem floor_one_add_eq_one
    {α : ℝ}
    (A : IsIrrationalUnitRotation α) :
    ⌊(1 : ℝ) + α⌋ = (1 : ℤ) := by
  apply (Int.floor_eq_iff).2
  constructor
  · norm_num
    linarith [A.pos]
  · norm_num
    linarith [A.lt_one]

/--
任意の irrational unit rotation `α` から canonical な
`RotationOstrowskiSystem α` を構成する。
-/
noncomputable def rotationOstrowskiSystem
    (α : ℝ)
    (A : IsIrrationalUnitRotation α) :
    RotationOstrowskiSystem α := by
  let σ : ℝ := 1 + α
  have hσ : Irrational σ := by
    dsimp [σ]
    exact one_add_irrational A
  have hFloor : ⌊σ⌋ = (1 : ℤ) := by
    dsimp [σ]
    exact floor_one_add_eq_one A
  let C : UnitOstrowskiConvergentSystem := convergentSystem σ hσ
  refine
    { conv := C
      lowerBracket := ?_
      upperBracket := ?_ }
  · intro n hn
    have hEven : Even n := Nat.even_iff.mpr hn
    have hOddNext : Odd (n + 1) := hEven.add_one
    refine ⟨C.p_pos n, C.p_pos (n + 1), ?_, ?_, ?_⟩
    · change
        ((regularQ (partialQuotient σ hσ) n : ℕ) : ℝ) /
            ((regularP (partialQuotient σ hσ) n : ℕ) : ℝ) < σ
      rw [← of_convs_eq_regularQ_div_regularP σ hσ hFloor n]
      exact conv_lt_of_even σ hσ hEven
    · change
        σ <
          ((regularQ (partialQuotient σ hσ) (n + 1) : ℕ) : ℝ) /
            ((regularP (partialQuotient σ hσ) (n + 1) : ℕ) : ℝ)
      rw [← of_convs_eq_regularQ_div_regularP σ hσ hFloor (n + 1)]
      exact lt_conv_of_odd σ hσ hOddNext
    · change
        regularP (partialQuotient σ hσ) (n + 1) *
              regularQ (partialQuotient σ hσ) n + 1 =
          regularP (partialQuotient σ hσ) n *
              regularQ (partialQuotient σ hσ) (n + 1)
      exact lower_determinant_of_even σ hσ hFloor hEven
  · intro n hn
    have hOdd : Odd n := Nat.odd_iff.mpr hn
    have hEvenNext : Even (n + 1) := hOdd.add_one
    refine ⟨C.p_pos n, C.p_pos (n + 1), ?_, ?_, ?_⟩
    · change
        ((regularQ (partialQuotient σ hσ) (n + 1) : ℕ) : ℝ) /
            ((regularP (partialQuotient σ hσ) (n + 1) : ℕ) : ℝ) < σ
      rw [← of_convs_eq_regularQ_div_regularP σ hσ hFloor (n + 1)]
      exact conv_lt_of_even σ hσ hEvenNext
    · change
        σ <
          ((regularQ (partialQuotient σ hσ) n : ℕ) : ℝ) /
            ((regularP (partialQuotient σ hσ) n : ℕ) : ℝ)
      rw [← of_convs_eq_regularQ_div_regularP σ hσ hFloor n]
      exact lt_conv_of_odd σ hσ hOdd
    · change
        regularP (partialQuotient σ hσ) n *
              regularQ (partialQuotient σ hσ) (n + 1) + 1 =
          regularP (partialQuotient σ hσ) (n + 1) *
              regularQ (partialQuotient σ hσ) n
      exact upper_determinant_of_odd σ hσ hFloor hOdd

end RotationOstrowskiExistence

/--
任意の無理回転 `α ∈ (0,1)` は `RotationOstrowskiSystem α` を持つ。
これにより generic Ostrowski RecordFerrers theory の system 仮定を存在量化で消せる。
-/
theorem rotationOstrowskiSystem_nonempty
    {α : ℝ}
    (A : IsIrrationalUnitRotation α) :
    Nonempty (RotationOstrowskiSystem α) :=
  ⟨RotationOstrowskiExistence.rotationOstrowskiSystem α A⟩

/-- 全称形の公開 wrapper。 -/
theorem exists_rotationOstrowskiSystem :
    ∀ α : ℝ,
      IsIrrationalUnitRotation α →
        Nonempty (RotationOstrowskiSystem α) := by
  intro α A
  exact rotationOstrowskiSystem_nonempty A

/--
存在定理を既存の Ostrowski / RecordFerrers exact bridge と合成した形。
任意の無理回転では、外部から system certificate を仮定せずとも、
ある canonical `RotationOstrowskiSystem` に対する threshold law で
RecordFerrers 性を特徴付けられる。
-/
theorem exists_ostrowski_characterization
    {α : ℝ}
    (A : IsIrrationalUnitRotation α)
    {m : ℕ}
    {height : ℕ → ℕ} :
    ∃ D : RotationOstrowskiSystem α,
      IsRecordFerrersPath (irrationalRotationRoof α) m height ↔
        IsAdmissibleRoofPath (irrationalRotationRoof α) m height ∧
          1 < m ∧
            D.CanonicalOstrowskiThresholdCompatible m height := by
  let D : RotationOstrowskiSystem α :=
    RotationOstrowskiExistence.rotationOstrowskiSystem α A
  exact ⟨D, D.isRecordFerrersPath_iff_ostrowski A⟩

end GenericRecordFerrers
end Experimental2
end Collatz3
