import CollatzLean.CollatzSecondLayer.CylinderConsequences

/-!
# 整合したcanonical C3 cylinder列

`C3CylinderSequence`は各有限cylinderだけを保存するため、それらが同じ
`FirstCrossingSequenceData`から順番に切り出されたという情報を忘れる。
chain抽出では実軌道上の位置関係が必要なので、Cylinder Upgradeの実際の構成を
そのまま保存する強い型を定義する。
-/

namespace CollatzSecondLayer

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

/--
一つのfirst-crossing列を有限位置だけずらして得られるcanonical C3列。

これは新しい数学的仮定ではない。`cylinderUpgradePrinciple_of_arithmetic`が
実際に構成していた由来情報を型の中へ残すための構造である。
-/
structure CoherentC3CylinderSequence (O : OddOrbit) where
  source : FirstCrossingSequenceData O
  shift : ℕ
  canonical : ∀ j : ℕ,
    (shiftedFirstCrossingCylinder source shift j).start <
      residueModulus (shiftedFirstCrossingCylinder source shift j).word
  polynomialSmall :
    ∃ K A : ℕ, ∀ j : ℕ,
      (shiftedFirstCrossingCylinder source shift j).start ≤
        K * ((shiftedFirstCrossingCylinder source shift j).length + 1) ^ A

namespace CoherentC3CylinderSequence

/-- 整合列の第`j` first-crossing cylinder。 -/
def firstCrossingCylinder
    {O : OddOrbit}
    (S : CoherentC3CylinderSequence O)
    (j : ℕ) : FirstCrossingCylinder O :=
  shiftedFirstCrossingCylinder S.source S.shift j

/-- 整合列の第`j` canonical cylinder。 -/
def cylinder
    {O : OddOrbit}
    (S : CoherentC3CylinderSequence O)
    (j : ℕ) : CanonicalC3Cylinder O :=
  {
    S.firstCrossingCylinder j with
    start_lt_modulus := S.canonical j
  }

/-- 整合列を従来の`C3CylinderSequence`へ忘却する。 -/
def toC3CylinderSequence
    {O : OddOrbit}
    (S : CoherentC3CylinderSequence O) : C3CylinderSequence O where
  cylinder := S.cylinder
  lengths_tend_to_infinity := by
    intro M
    obtain ⟨J, hJ⟩ :=
      shiftedFirstCrossing_lengths_tend_to_infinity
        S.source S.shift M
    refine ⟨J, ?_⟩
    intro j hj
    have h := hJ j hj
    simpa [cylinder, firstCrossingCylinder] using h
  polynomialSmall := by
    rcases S.polynomialSmall with ⟨K, A, hsmall⟩
    refine ⟨K, A, ?_⟩
    intro j
    simpa [cylinder, firstCrossingCylinder] using hsmall j

/-- 第`j` cylinderの実軌道上の開始位置。 -/
def startPosition
    {O : OddOrbit}
    (S : CoherentC3CylinderSequence O)
    (j : ℕ) : ℕ :=
  S.source.limit.minima.index (S.shift + j)

/-- 第`j` cylinderの長さ。 -/
def length
    {O : OddOrbit}
    (S : CoherentC3CylinderSequence O)
    (j : ℕ) : ℕ :=
  S.source.crossingLength (S.shift + j)

/-- 第`j` cylinderの終点位置。 -/
def finishPosition
    {O : OddOrbit}
    (S : CoherentC3CylinderSequence O)
    (j : ℕ) : ℕ :=
  S.startPosition j + S.length j

/-- 第`j` cylinderの開始値。 -/
def startValue
    {O : OddOrbit}
    (S : CoherentC3CylinderSequence O)
    (j : ℕ) : ℕ :=
  O.value (S.startPosition j)

/-- 第`j` cylinderの終点値。 -/
def finishValue
    {O : OddOrbit}
    (S : CoherentC3CylinderSequence O)
    (j : ℕ) : ℕ :=
  O.value (S.finishPosition j)

@[simp] theorem firstCrossingCylinder_start
    {O : OddOrbit}
    (S : CoherentC3CylinderSequence O)
    (j : ℕ) :
    (S.firstCrossingCylinder j).start = S.startValue j := by
  rfl

@[simp] theorem firstCrossingCylinder_length
    {O : OddOrbit}
    (S : CoherentC3CylinderSequence O)
    (j : ℕ) :
    (S.firstCrossingCylinder j).length = S.length j := by
  rfl

@[simp] theorem firstCrossingCylinder_finish
    {O : OddOrbit}
    (S : CoherentC3CylinderSequence O)
    (j : ℕ) :
    (S.firstCrossingCylinder j).finish = S.finishValue j := by
  rfl

/-- cylinder開始位置は狭義単調。 -/
theorem startPosition_strict
    {O : OddOrbit}
    (S : CoherentC3CylinderSequence O) :
    StrictMono S.startPosition := by
  intro i j hij
  apply S.source.limit.minima.index_strict
  omega

/-- cylinder開始値は狭義単調。 -/
theorem startValue_strict
    {O : OddOrbit}
    (S : CoherentC3CylinderSequence O) :
    StrictMono S.startValue := by
  intro i j hij
  apply S.source.limit.minima.value_strict
  omega

/-- 任意の狭義単調自然数列は添字以上に進む。 -/
lemma strictMono_nat_id_le
    (f : ℕ → ℕ)
    (hf : StrictMono f) :
    ∀ n : ℕ, n ≤ f n := by
  intro n
  induction n with
  | zero => omega
  | succ n ih =>
      have hstep : f n < f (n + 1) :=
        hf (Nat.lt_succ_self n)
      omega

/-- 整合列の開始位置は添字以上。 -/
theorem index_le_startPosition
    {O : OddOrbit}
    (S : CoherentC3CylinderSequence O)
    (j : ℕ) :
    j ≤ S.startPosition j :=
  strictMono_nat_id_le S.startPosition S.startPosition_strict j

/-- 任意の値閾値と列添字閾値を同時に越える開始点が存在する。 -/
theorem exists_later_startValue
    {O : OddOrbit}
    (S : CoherentC3CylinderSequence O)
    (M J : ℕ) :
    ∃ j : ℕ,
      J ≤ j ∧
      M < S.startValue j := by
  obtain ⟨q, hq, hvalue⟩ :=
    S.source.limit.minima.eventually_large M (S.shift + J)
  refine ⟨q - S.shift, ?_, ?_⟩
  · omega
  · have hqeq : S.shift + (q - S.shift) = q := by omega
    simpa [startValue, startPosition, hqeq] using hvalue

/--
任意の現在添字・位置閾値・値閾値より後ろにあるcylinderを選べる。
-/
theorem exists_strictly_later_cylinder
    {O : OddOrbit}
    (S : CoherentC3CylinderSequence O)
    (current positionBound valueBound : ℕ) :
    ∃ j : ℕ,
      current < j ∧
      positionBound < S.startPosition j ∧
      valueBound < S.startValue j := by
  let J := max (current + 1) (positionBound + 1)
  obtain ⟨j, hj, hvalue⟩ :=
    S.exists_later_startValue valueBound J
  refine ⟨j, ?_, ?_, hvalue⟩
  · dsimp [J] at hj
    omega
  · have hindex : j ≤ S.startPosition j :=
      S.index_le_startPosition j
    dsimp [J] at hj
    omega

/-- future-minimum性により各終点は開始値以上。 -/
theorem startValue_le_finishValue
    {O : OddOrbit}
    (S : CoherentC3CylinderSequence O)
    (j : ℕ) :
    S.startValue j ≤ S.finishValue j := by
  change
    (S.firstCrossingCylinder j).start ≤
      (S.firstCrossingCylinder j).finish
  exact (S.firstCrossingCylinder j).terminal_ge_start

/-- first-crossing性により各cylinder長は正。 -/
theorem length_pos
    {O : OddOrbit}
    (S : CoherentC3CylinderSequence O)
    (j : ℕ) :
    0 < S.length j := by
  change 0 < S.source.crossingLength (S.shift + j)
  exact (S.source.crossing (S.shift + j)).length_pos

end CoherentC3CylinderSequence

/-- 整合C3列の終点もcylinder長に対して一様に多項式小。 -/
theorem finishes_polynomialSmall
    {O : OddOrbit}
    (S : CoherentC3CylinderSequence O) :
    ∃ K A : ℕ, ∀ j : ℕ,
      S.finishValue j ≤ K * (S.length j + 1) ^ A := by
  rcases S.polynomialSmall with ⟨K, A, hstart⟩
  refine ⟨K + 1, A + 1, ?_⟩
  intro j
  let b := S.length j + 1
  have hbpos : 0 < b := by
    dsimp [b]
    omega
  have hpowA : b ^ A ≤ b ^ (A + 1) :=
    Nat.pow_le_pow_right hbpos (Nat.le_succ A)
  have hpowOne : b ≤ b ^ (A + 1) := by
    have hone : 1 ≤ A + 1 := by omega
    simpa using Nat.pow_le_pow_right hbpos hone
  have hfinish :
      S.finishValue j ≤ S.startValue j + S.length j := by
    change
      (S.firstCrossingCylinder j).finish ≤
        (S.firstCrossingCylinder j).start +
          (S.firstCrossingCylinder j).length
    exact (S.firstCrossingCylinder j).finish_le_start_add_length
  have hstartJ :
      S.startValue j ≤ K * b ^ A := by
    change
      (shiftedFirstCrossingCylinder S.source S.shift j).start ≤
        K *
          ((shiftedFirstCrossingCylinder S.source S.shift j).length + 1) ^ A
    exact hstart j
  calc
    S.finishValue j
        ≤ S.startValue j + S.length j := hfinish
    _ ≤ K * b ^ A + S.length j :=
      Nat.add_le_add_right hstartJ _
    _ ≤ K * b ^ (A + 1) + b ^ (A + 1) := by
      exact Nat.add_le_add
        (Nat.mul_le_mul_left K hpowA)
        (le_trans (by dsimp [b]; omega) hpowOne)
    _ = (K + 1) * b ^ (A + 1) := by ring
    _ = (K + 1) * (S.length j + 1) ^ (A + 1) := by rfl

/-- 算術入力から整合版Cylinder Upgradeを構成する。 -/
theorem coherentCylinderUpgrade_of_arithmetic
    (hBaker : TwoThreeGapPolynomialBound)
    (hPow : PolynomialBelowTwoPower) :
    ∀ O : OddOrbit,
    ∀ _F : FirstCrossingSequenceData O,
      Nonempty (CoherentC3CylinderSequence O) := by
  obtain ⟨K, A, hheight⟩ :=
    firstCrossing_start_polynomial hBaker
  intro O F
  obtain ⟨N, hN⟩ := hPow K A
  obtain ⟨J, hlength⟩ :=
    exists_shift_all_firstCrossing_lengths_ge F N
  refine ⟨{
    source := F
    shift := J
    canonical := by
      intro j
      apply firstCrossingCylinder_start_lt_modulus_of_length_ge
        (C := shiftedFirstCrossingCylinder F J j)
        (K := K)
        (A := A)
        (N := N)
      · exact hheight O (shiftedFirstCrossingCylinder F J j)
      · exact hN
      · exact hlength j
    polynomialSmall := by
      refine ⟨K, A, ?_⟩
      intro j
      exact hheight O (shiftedFirstCrossingCylinder F J j)
  }⟩

end CollatzSecondLayer
