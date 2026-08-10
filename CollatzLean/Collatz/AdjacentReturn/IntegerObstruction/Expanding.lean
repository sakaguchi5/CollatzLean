import CollatzLean.Collatz.AdjacentReturn.IntegerObstruction.Chain
import CollatzLean.Collatz.Selection.Cofinal

/-!
# expanding 側の整数 obstruction

whole expanding・全 proper prefix expanding・全 proper suffix contracting を
一つの純算術 package にまとめる。
-/

namespace Collatz
namespace AdjacentReturn

namespace State

/-- expanding adjacent return の上側 `2^H < 3^r`。 -/
theorem expanding_twoPow_lt_threePow
    {O : OddOrbit} (R : State O) (hE : R.IsExpanding) :
    2 ^ R.totalExponent < 3 ^ R.length := by
  have h := hE
  unfold IsExpanding Word.Expanding at h
  rw [R.oddSteps_word] at h
  simpa [State.totalExponent] using h

end State

namespace IntegerObstruction

/-- expanding adjacent block の純算術 package。 -/
structure ExpandingBlockArithmetic where
  base : BlockArithmeticData
  expanding : base.word.Expanding
  properPrefixesExpanding : base.word.ProperPrefixesExpanding
  upperBand :
    2 ^ base.totalExponent < 3 ^ base.length
  affinePrefixBound :
    base.affineConstant ≤
      base.length * 3 ^ (base.length - 1)
  affineSuffixBound :
    1 < base.length →
      3 * base.affineConstant <
        3 ^ base.length +
          (base.length - 1) * 2 ^ base.totalExponent

namespace ExpandingBlockArithmetic

/--
長さ2以上なら lower band は expanding 固有条件ではなく、
基礎の adjacent 算術だけから従う。
-/
theorem lowerBand
    (E : ExpandingBlockArithmetic)
    (hlen : 1 < E.base.length) :
    2 * 3 ^ (E.base.length - 1) < 2 ^ E.base.totalExponent :=
  E.base.two_mul_threePow_pred_lt_twoPow hlen

/-- 実際の expanding adjacent state から純算術 package を作る。 -/
def ofState
    {O : OddOrbit} (R : State O) (hE : R.IsExpanding) :
    ExpandingBlockArithmetic := by
  let B := BlockArithmeticData.ofState R
  refine {
    base := B
    expanding := ?_
    properPrefixesExpanding := ?_
    upperBand := ?_
    affinePrefixBound := ?_
    affineSuffixBound := ?_
  }
  · change R.word.Expanding
    exact hE
  · change R.word.ProperPrefixesExpanding
    exact R.properPrefixesExpanding hE
  · change 2 ^ R.totalExponent < 3 ^ R.length
    exact R.expanding_twoPow_lt_threePow hE
  · change R.affineConstant ≤ R.length * 3 ^ (R.length - 1)
    exact R.affineConstant_le_length_mul_threePow_pred hE
  · intro hlen
    change
      3 * R.affineConstant <
        3 ^ R.length + (R.length - 1) * 2 ^ R.totalExponent
    exact R.three_mul_affineConstant_lt_threePow_add_tail_twoPow hlen

end ExpandingBlockArithmetic

/--
`r > 0` なら

`4 * 3^(r-1) < 3^r`

は成立しない。
-/
theorem not_four_mul_threePow_pred_lt_threePow
    {r : ℕ}
    (hr : 0 < r) :
    ¬ 4 * 3 ^ (r - 1) < 3 ^ r := by
  intro hbad
  obtain ⟨q, hq⟩ : ∃ q : ℕ, r = q + 1 := by
    exact ⟨r - 1, by omega⟩
  rw [hq, pow_succ] at hbad
  simp only [add_tsub_cancel_right] at hbad
  have hle :
      3 ^ q * 3 ≤ 4 * 3 ^ q := by
    have h :
        3 * 3 ^ q ≤ 4 * 3 ^ q := by
      exact Nat.mul_le_mul_right (3 ^ q) (by omega)
    simpa [Nat.mul_comm] using h
  omega


/--
狭い帯

`2*3^(r-1) < 2^H < 3^r`

に属する2つの指数について、小さい方が真に小さいことはない。
-/
theorem totalExponent_not_lt_of_length
    {r H₁ H₂ : ℕ}
    (hr : 0 < r)
    (h₁low : 2 * 3 ^ (r - 1) < 2 ^ H₁)
    (h₂high : 2 ^ H₂ < 3 ^ r) :
    ¬ H₁ < H₂ := by
  intro h12
  have hsucc : H₁ + 1 ≤ H₂ := by
    omega
  have hpowLe : 2 ^ (H₁ + 1) ≤ 2 ^ H₂ := by
    exact
      Nat.pow_le_pow_right
        (by omega : 0 < (2 : ℕ))
        hsucc
  have hscaled :=
    (Nat.mul_lt_mul_left
      (by omega : 0 < (2 : ℕ))).2 h₁low
  have hlow :
      4 * 3 ^ (r - 1) < 2 ^ (H₁ + 1) := by
    calc
      4 * 3 ^ (r - 1)
          = 2 * (2 * 3 ^ (r - 1)) := by ring
      _ < 2 * 2 ^ H₁ := hscaled
      _ = 2 ^ (H₁ + 1) := by
        rw [pow_succ]
        simp [Nat.mul_comm]
  have hbad :
      4 * 3 ^ (r - 1) < 3 ^ r := by
    exact
      lt_trans
        (lt_of_lt_of_le hlow hpowLe)
        h₂high
  exact
    not_four_mul_threePow_pred_lt_threePow hr hbad


/--
狭い帯

`2*3^(r-1) < 2^H < 3^r`

に入る2冪指数は固定 `r` に対して高々一つ。
-/
theorem totalExponent_unique_of_length
    {r H₁ H₂ : ℕ}
    (hr : 0 < r)
    (h₁low : 2 * 3 ^ (r - 1) < 2 ^ H₁)
    (h₁high : 2 ^ H₁ < 3 ^ r)
    (h₂low : 2 * 3 ^ (r - 1) < 2 ^ H₂)
    (h₂high : 2 ^ H₂ < 3 ^ r) :
    H₁ = H₂ := by
  rcases lt_trichotomy H₁ H₂ with h12 | heq | h21
  · exact False.elim (
      totalExponent_not_lt_of_length
        hr h₁low h₂high h12)
  · exact heq
  · exact False.elim (
      totalExponent_not_lt_of_length
        hr h₂low h₁high h21)

/--
expanding が cofinal に現れる連続整数 chain。

`chain` は標準 adjacent return を一つも落とさず保持し、
`select` はその中の expanding block を選ぶ。
-/
structure ExpandingIntegerTower where
  chain : AdjacentIntegerChain
  select : ℕ → ℕ
  select_strict : StrictMono select
  block : ℕ → ExpandingBlockArithmetic
  block_base_eq :
    ∀ n : ℕ, (block n).base = chain.block (select n)

namespace ExpandingIntegerTower

/-- strict selector は添字自身以上。 -/
theorem select_ge
    (T : ExpandingIntegerTower) (n : ℕ) :
    n ≤ T.select n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
      have hlt := T.select_strict (Nat.lt_succ_self n)
      exact Nat.succ_le_of_lt (lt_of_le_of_lt ih hlt)

/-- selected block は共通 chain 上でも expanding。 -/
theorem selected_expanding
    (T : ExpandingIntegerTower) (n : ℕ) :
    (T.chain.block (T.select n)).word.Expanding := by
  rw [← T.block_base_eq n]
  exact (T.block n).expanding

/-- 共通 chain 上で expanding block は cofinal に現れる。 -/
theorem cofinal_expanding
    (T : ExpandingIntegerTower) :
    Selection.Cofinal
      (fun j => (T.chain.block j).word.Expanding) := by
  intro N
  refine ⟨T.select N, T.select_ge N, ?_⟩
  exact T.selected_expanding N

/-- selected start value は狭義単調。 -/
theorem startValue_strict
    (T : ExpandingIntegerTower) :
    StrictMono (fun n => (T.block n).base.startValue) := by
  intro a b hab
  dsimp
  rw [T.block_base_eq a, T.block_base_eq b]
  exact T.chain.startValue_strict (T.select_strict hab)

/-- 実際の expanding tower から、連続 chain を保った純算術 tower を作る。 -/
def ofTower
    {O : OddOrbit} (T : ExpandingTower O) : ExpandingIntegerTower := by
  refine {
    chain :=
      AdjacentIntegerChain.ofStandardFutureMinima
        T.unbounded T.minima T.standard
    select := T.select
    select_strict := T.select_strict
    block := fun n =>
      ExpandingBlockArithmetic.ofState
        (T.tower_at n) (T.at_expanding n)
    block_base_eq := ?_
  }
  intro n
  rfl

/-- expanding block 長が一様有界。 -/
def LengthsBounded (T : ExpandingIntegerTower) : Prop :=
  ∃ M : ℕ, ∀ n : ℕ, (T.block n).base.length ≤ M

/-- expanding block 長が非有界。 -/
def LengthsUnbounded (T : ExpandingIntegerTower) : Prop :=
  ∀ M : ℕ, ∃ n : ℕ, M < (T.block n).base.length

/-- 長さの有界・非有界二分法。 -/
theorem lengths_bounded_or_unbounded (T : ExpandingIntegerTower) :
    T.LengthsBounded ∨ T.LengthsUnbounded := by
  classical
  by_cases h : T.LengthsBounded
  · exact Or.inl h
  · right
    unfold LengthsBounded at h
    unfold LengthsUnbounded
    push Not at h
    exact h

end ExpandingIntegerTower
end IntegerObstruction
end AdjacentReturn
end Collatz
