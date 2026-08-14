import CollatzLean.Collatz2.Orbit.Runs
import CollatzLean.Collatz2.Local.DeterminantSign
import Mathlib.Tactic.Linarith

/-!
# Collatz2 Mountain: mountain block / decomposition

normalized odd-only exponent word では、value > 1 の一歩は

* exponent = 1 なら上昇
* exponent >= 2 なら下降

となる。

したがって standard accelerated Collatz map の一つの local minimum から
次の local minimum までの「山」は exact に

  [1, ..., 1, d]   (d >= 2)

という odd-only word で表される。

このファイルでは mountain を trajectory の新しい仮定として置かず、
word shape と actual `Runs` から導く薄い object として定義する。
-/

namespace Collatz2

namespace OddOnlyStep

/-- exponent 1 の normalized odd step は strict rise。 -/
theorem rises_of_exponent_one
    {x y : ℕ}
    (hstep : 2 * y = 3 * x + 1) :
    x < y := by
  nlinarith

/-- exponent >= 2 の normalized odd step は `x>1` なら strict drop。 -/
theorem drops_of_exponent_ge_two
    {e x y : ℕ}
    (hx : 1 < x)
    (he : 2 ≤ e)
    (hstep : 2 ^ e * y = 3 * x + 1) :
    y < x := by
  have hpow : 4 ≤ 2 ^ e := by
    have h :=
      Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) he
    norm_num at h
    exact h
  by_contra hnot
  have hxy : x ≤ y := Nat.le_of_not_gt hnot
  have h4 : 4 * x ≤ 2 ^ e * y := by
    calc
      4 * x ≤ 4 * y := Nat.mul_le_mul_left 4 hxy
      _ ≤ 2 ^ e * y := Nat.mul_le_mul_right y hpow
  rw [hstep] at h4
  nlinarith

/-- positive exponent の step は、`x>1` なら rise iff exponent=1。 -/
theorem rises_iff_exponent_eq_one
    {e x y : ℕ}
    (hx : 1 < x)
    (hePos : 0 < e)
    (hstep : 2 ^ e * y = 3 * x + 1) :
    x < y ↔ e = 1 := by
  constructor
  · intro hRise
    by_contra hne
    have heTwo : 2 ≤ e := by omega
    have hDrop := drops_of_exponent_ge_two hx heTwo hstep
    omega
  · intro he
    subst e
    norm_num at hstep
    exact rises_of_exponent_one hstep

end OddOnlyStep

namespace Word

/-- 一つの完全 mountain の exponent-word shape。 -/
structure MountainBlock (w : Word) : Type where
  riseCount : ℕ
  dropExponent : ℕ
  drop_ge_two : 2 ≤ dropExponent
  word_eq :
    w = List.replicate riseCount 1 ++ [dropExponent]

namespace MountainBlock

/-- standard map での odd-step 数。 -/
def oddRunLength
    {w : Word}
    (M : MountainBlock w) : ℕ :=
  M.riseCount + 1

/-- standard map で local maximum 後に行う even-step 数。 -/
def evenRunLength
    {w : Word}
    (M : MountainBlock w) : ℕ :=
  M.dropExponent - 1

/-- odd-run は必ず nonempty。 -/
theorem oddRunLength_pos
    {w : Word}
    (M : MountainBlock w) :
    0 < M.oddRunLength := by
  unfold oddRunLength
  omega

/-- even-run は必ず nonempty。 -/
theorem evenRunLength_pos
    {w : Word}
    (M : MountainBlock w) :
    0 < M.evenRunLength := by
  have hdrop := M.drop_ge_two
  unfold evenRunLength
  omega

/-- mountain word は nonempty。 -/
theorem nonempty
    {w : Word}
    (M : MountainBlock w) :
    w ≠ [] := by
  rw [M.word_eq]
  simp

/-- mountain の odd-only step 数。 -/
theorem oddSteps_eq
    {w : Word}
    (M : MountainBlock w) :
    Word.oddSteps w = M.oddRunLength := by
  have hsteps :
      Word.oddSteps w =
        Word.oddSteps
          (List.replicate M.riseCount 1 ++ [M.dropExponent]) :=
    congrArg Word.oddSteps M.word_eq
  calc
    Word.oddSteps w =
        Word.oddSteps
          (List.replicate M.riseCount 1 ++ [M.dropExponent]) :=
      hsteps
    _ = M.oddRunLength := by
      simp [Word.oddSteps, oddRunLength]

/-- mountain の総2指数は standard odd/even step 数の和。 -/
theorem twoSteps_eq
    {w : Word}
    (M : MountainBlock w) :
    Word.twoSteps w = M.oddRunLength + M.evenRunLength := by
  have hsteps :
      Word.twoSteps w =
        Word.twoSteps
          (List.replicate M.riseCount 1 ++ [M.dropExponent]) :=
    congrArg Word.twoSteps M.word_eq
  have hdrop : 2 ≤ M.dropExponent :=
    M.drop_ge_two
  calc
    Word.twoSteps w =
        Word.twoSteps
          (List.replicate M.riseCount 1 ++ [M.dropExponent]) :=
      hsteps
    _ = M.oddRunLength + M.evenRunLength := by
      simp [Word.twoSteps, oddRunLength, evenRunLength]
      omega

end MountainBlock

/-- word が一つの完全 mountain だけからなること。 -/
def OneMountain (w : Word) : Prop :=
  Nonempty (MountainBlock w)

/--
word の mountain decomposition。
各 block が `[1^r,d] (d>=2)` であり、flatten が元 word に一致することだけを保持する。
-/
structure MountainDecomposition (w : Word) : Type where
  blocks : List Word
  shape : ∀ b : Word, b ∈ blocks → Nonempty (MountainBlock b)
  decomp : blocks.flatten = w

namespace MountainDecomposition

/-- mountain 個数。 -/
def mountainCount
    {w : Word}
    (D : MountainDecomposition w) : ℕ :=
  D.blocks.length

/-- decomposition が1 blockなら元 word 自身が one mountain。 -/
theorem oneMountain_of_count_eq_one
    {w : Word}
    (D : MountainDecomposition w)
    (hOne : D.mountainCount = 1) :
    OneMountain w := by
  unfold mountainCount at hOne
  cases hblocks : D.blocks with
  | nil =>
      simp [hblocks] at hOne
  | cons b bs =>
      cases bs with
      | nil =>
          have hb : b ∈ D.blocks := by
            rw [hblocks]
            simp
          obtain ⟨M⟩ := D.shape b hb
          have hdecomp : b = w := by
            simpa [hblocks] using D.decomp
          rw [← hdecomp]
          exact ⟨M⟩
      | cons c cs =>
          simp [hblocks] at hOne

/-- nonempty word の mountain decomposition は0 mountainではない。 -/
theorem count_pos_of_word_nonempty
    {w : Word}
    (D : MountainDecomposition w)
    (hw : w ≠ []) :
    0 < D.mountainCount := by
  unfold mountainCount
  by_contra hnot
  have hzero : D.blocks.length = 0 := by
    omega
  have hnil : D.blocks = [] := by
    cases hblocks : D.blocks with
    | nil =>
        rfl
    | cons b bs =>
        simp [hblocks] at hzero
  have hdecomp : ([] : Word) = w := by
    simpa [hnil] using D.decomp
  exact hw hdecomp.symm

end MountainDecomposition

end Word

/-!
## Standard accelerated odd-run shadow

Hercher Lemma 8 の局所部分を odd-only word から回収するため、
standard map の「連続 odd step」だけを薄い relation として置く。

`StandardOddRuns k x y` は x から k 回連続で `(3n+1)/2` branch を使い y に至る。
-/

inductive StandardOddRuns : ℕ → ℕ → ℕ → Prop where
  | zero (x : ℕ) : StandardOddRuns 0 x x
  | snoc {k x y z : ℕ}
      (prev : StandardOddRuns k x y)
      (start_odd : Odd y)
      (step : 2 * z = 3 * y + 1) :
      StandardOddRuns (k + 1) x z

namespace StandardOddRuns

/-- 二つの consecutive odd-run を連結する。 -/
theorem append
    {k l x y z : ℕ}
    (h₁ : StandardOddRuns k x y)
    (h₂ : StandardOddRuns l y z) :
    StandardOddRuns (k + l) x z := by
  induction h₂ generalizing x with
  | zero y =>
      simpa using h₁
  | @snoc l y m z hprev hmOdd hstep ih =>
      have hpre : StandardOddRuns (k + l) x m := ih h₁
      have hsnoc : StandardOddRuns ((k + l) + 1) x z :=
        StandardOddRuns.snoc hpre hmOdd hstep
      simpa [Nat.add_assoc] using hsnoc

/-- 1 standard odd-step。 -/
theorem single
    {x y : ℕ}
    (hx : Odd x)
    (hstep : 2 * y = 3 * x + 1) :
    StandardOddRuns 1 x y := by
  have h := StandardOddRuns.snoc (StandardOddRuns.zero x) hx hstep
  simpa using h

/--
Hercher Lemma 8 の強化形。
k consecutive odd steps は一つの parameter `a` を持ち

  x = a*2^k - 1
  y = a*3^k - 1

となる。
-/
theorem exists_parameter
    {k x y : ℕ}
    (h : StandardOddRuns k x y) :
    ∃ a : ℕ,
      0 < a ∧
      x = a * 2 ^ k - 1 ∧
      y = a * 3 ^ k - 1 := by
  induction h with
  | zero x =>
      refine ⟨x + 1, by omega, ?_, ?_⟩
      · simp
      · simp
  | @snoc k x y z hprev hyOdd hstep ih =>
      obtain ⟨a, haPos, hx, hy⟩ := ih
      have hEvenProd : Even (a * 3 ^ k) := by
        rcases hyOdd with ⟨t, ht⟩
        refine ⟨t + 1, ?_⟩
        rw [hy] at ht
        omega
      have hThreeOdd : Odd (3 ^ k) :=
        (show Odd (3 : ℕ) by decide).pow
      have haEven : Even a := by
        rcases a.even_or_odd' with ⟨b, ha | ha⟩
        · refine ⟨b, ?_⟩
          omega
        · have haOdd : Odd a := by
            refine ⟨b, ?_⟩
            omega
          have hProdOdd : Odd (a * 3 ^ k) := haOdd.mul hThreeOdd
          rcases hProdOdd with ⟨u, hu⟩
          rcases hEvenProd with ⟨v, hv⟩
          omega
      rcases haEven with ⟨b, hab⟩
      have hbPos : 0 < b := by
        rw [hab] at haPos
        omega
      have hprodTwo :
          (b + b) * 2 ^ k = b * 2 ^ (k + 1) := by
        rw [pow_succ]
        ring
      have hx' : x = b * 2 ^ (k + 1) - 1 := by
        rw [hx, hab, hprodTwo]
      let q := b * 3 ^ k
      have hqPos : 0 < q := by
        dsimp [q]
        exact Nat.mul_pos hbPos (Nat.pow_pos (by omega))
      have hprodThree :
          (b + b) * 3 ^ k = 2 * q := by
        dsimp [q]
        ring
      have hy' : y = 2 * q - 1 := by
        rw [hy, hab, hprodThree]
      have hz' : z = 3 * q - 1 := by
        rw [hy'] at hstep
        omega
      have h3q : 3 * q = b * 3 ^ (k + 1) := by
        dsimp [q]
        rw [pow_succ]
        ring
      refine ⟨b, hbPos, hx', ?_⟩
      rw [hz', h3q]

/-- Hercher Lemma 8: `2^k | x+1`。 -/
theorem twoPow_dvd_start_add_one
    {k x y : ℕ}
    (h : StandardOddRuns k x y) :
    2 ^ k ∣ x + 1 := by
  obtain ⟨a, _ha, hx, _hy⟩ := h.exists_parameter
  refine ⟨a, ?_⟩
  have hprodPos : 0 < a * 2 ^ k :=
    Nat.mul_pos _ha (Nat.pow_pos (by omega))
  have hOneLe : 1 ≤ a * 2 ^ k := by omega
  rw [hx, Nat.sub_add_cancel hOneLe]
  ring

/-- Hercher Lemma 8 の lower bound `2^k - 1 <= x`。 -/
theorem twoPow_sub_one_le_start
    {k x y : ℕ}
    (h : StandardOddRuns k x y) :
    2 ^ k - 1 ≤ x := by
  obtain ⟨a, ha, hx, _hy⟩ := h.exists_parameter
  rw [hx]
  apply Nat.sub_le_sub_right
  have haOne : 1 ≤ a := by omega
  calc
    2 ^ k = 1 * 2 ^ k := by simp
    _ ≤ a * 2 ^ k := Nat.mul_le_mul_right (2 ^ k) haOne

end StandardOddRuns

namespace Runs

/-- odd-only exponent=1 の連続 run は standard-map の consecutive odd-run。 -/
theorem replicate_one_to_standardOddRuns
    {r x y : ℕ}
    (h : Runs (List.replicate r 1) x y) :
    StandardOddRuns r x y := by
  induction r generalizing x y with
  | zero =>
      cases h with
      | nil x =>
          exact StandardOddRuns.zero x
  | succ r ih =>
      change Runs (1 :: List.replicate r 1) x y at h
      have hxOdd : Odd x :=
        h.start_odd_of_ne_nil (by simp)
      cases h with
      | @cons _ _ _ m _ he hstep hmOdd htail =>
          have hsingle : StandardOddRuns 1 x m := by
            apply StandardOddRuns.single hxOdd
            simpa using hstep
          have hrest : StandardOddRuns r m y :=
            ih htail
          simpa [Nat.add_comm] using
            StandardOddRuns.append hsingle hrest

end Runs

namespace Word

/-- actual mountain run。 -/
structure MountainRun (w : Word) (x z : ℕ) : Type where
  shape : MountainBlock w
  run : Runs w x z

namespace MountainRun

/--
odd-only mountain から Hercher の standard mountain parameter を回収する。

k = riseCount+1, l = dropExponent-1 とすると

  x = a*2^k - 1
  peak = a*3^k - 1
  2^l*z = peak.
-/
theorem exists_standard_parameter
    {w : Word} {x z : ℕ}
    (M : MountainRun w x z) :
    ∃ a peak : ℕ,
      0 < a ∧
      x = a * 2 ^ M.shape.oddRunLength - 1 ∧
      peak = a * 3 ^ M.shape.oddRunLength - 1 ∧
      2 ^ M.shape.evenRunLength * z = peak := by
  let r := M.shape.riseCount
  let d := M.shape.dropExponent
  have hshape : w = List.replicate r 1 ++ [d] := M.shape.word_eq
  have hrun : Runs (List.replicate r 1 ++ [d]) x z := by
    simpa [hshape] using M.run
  obtain ⟨y, hRise, hDrop⟩ := Runs.split_append hrun
  have hStdRise : StandardOddRuns r x y :=
    hRise.replicate_one_to_standardOddRuns
  have hyOdd : Odd y :=
    hDrop.start_odd_of_ne_nil (by simp)
  cases hDrop with
  | @cons _ _ _ _ _ hdPos hstep hzOdd hnil =>
      cases hnil
      have hdTwo : 2 ≤ d := M.shape.drop_ge_two
      let peak := 2 ^ (d - 1) * z
      have hPeakStep : 2 * peak = 3 * y + 1 := by
        dsimp [peak]
        have hdEq : d = (d - 1) + 1 := by omega
        rw [hdEq, pow_succ] at hstep
        simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hstep
      have hStdLast : StandardOddRuns 1 y peak :=
        StandardOddRuns.single hyOdd hPeakStep
      have hStd : StandardOddRuns (r + 1) x peak := by
        simpa using hStdRise.append hStdLast
      obtain ⟨a, ha, hx, hpeak⟩ := hStd.exists_parameter
      refine ⟨a, peak, ha, ?_, ?_, ?_⟩
      · simpa [MountainBlock.oddRunLength, r] using hx
      · simpa [MountainBlock.oddRunLength, r] using hpeak
      · dsimp [peak]
        simp only [MountainBlock.evenRunLength, d]

/-- Hercher Lemma 8 を actual mountain へ移した lower bound。 -/
theorem start_ge_twoPow_sub_one
    {w : Word} {x z : ℕ}
    (M : MountainRun w x z) :
    2 ^ M.shape.oddRunLength - 1 ≤ x := by
  obtain ⟨a, _peak, ha, hx, _hp, _hd⟩ :=
    M.exists_standard_parameter
  have haOne : 1 ≤ a := by
    omega
  have hmul :
      2 ^ M.shape.oddRunLength ≤
        a * 2 ^ M.shape.oddRunLength := by
    calc
      2 ^ M.shape.oddRunLength
          = 1 * 2 ^ M.shape.oddRunLength := by
              simp
      _ ≤ a * 2 ^ M.shape.oddRunLength :=
        Nat.mul_le_mul_right _ haOne
  calc
    2 ^ M.shape.oddRunLength - 1
        ≤ a * 2 ^ M.shape.oddRunLength - 1 :=
      Nat.sub_le_sub_right hmul 1
    _ = x := hx.symm

/--
Hercher Lemma 20 の division-free core。
次の valley `z` は

  2^(k+1) * z < 3^k * (x+1)

を満たす。
実数 `δ=log 3/log 2` を導入する前の exact integer 版。
-/
theorem hercherLemma20_divisionFree
    {w : Word} {x z : ℕ}
    (M : MountainRun w x z) :
    2 ^ (M.shape.oddRunLength + 1) * z <
      3 ^ M.shape.oddRunLength * (x + 1) := by
  obtain ⟨a, peak, ha, hx, hpeak, hdesc⟩ :=
    M.exists_standard_parameter
  have hlPos : 0 < M.shape.evenRunLength :=
    M.shape.evenRunLength_pos
  have hpowTwo : 2 ≤ 2 ^ M.shape.evenRunLength := by
    have hOne : 1 ≤ M.shape.evenRunLength := by omega
    have hmono :=
      Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hOne
    simpa using hmono
  have htwoz : 2 * z ≤ peak := by
    calc
      2 * z ≤ 2 ^ M.shape.evenRunLength * z :=
        Nat.mul_le_mul_right z hpowTwo
      _ = peak := hdesc
  have hpeakLt : peak < a * 3 ^ M.shape.oddRunLength := by
    rw [hpeak]
    have hpos : 0 < a * 3 ^ M.shape.oddRunLength :=
      Nat.mul_pos ha (Nat.pow_pos (by omega))
    omega
  have hcore : 2 * z < a * 3 ^ M.shape.oddRunLength :=
    lt_of_le_of_lt htwoz hpeakLt
  have hxAdd : x + 1 = a * 2 ^ M.shape.oddRunLength := by
    have hpos : 0 < a * 2 ^ M.shape.oddRunLength :=
      Nat.mul_pos ha (Nat.pow_pos (by omega))
    have hx' :
        x + 1 =
          (a * 2 ^ M.shape.oddRunLength - 1) + 1 :=
      congrArg (fun t : ℕ => t + 1) hx
    calc
      x + 1 =
          (a * 2 ^ M.shape.oddRunLength - 1) + 1 :=
        hx'
      _ = a * 2 ^ M.shape.oddRunLength := by
        omega
  have hpowPos :
      0 < 2 ^ M.shape.oddRunLength :=
    Nat.pow_pos (by omega)
  have hscaled :=
    (Nat.mul_lt_mul_left hpowPos).2 hcore
  rw [hxAdd, pow_succ]
  simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hscaled

end MountainRun

end Word
end Collatz2
