import CollatzLean.Collatz2.Canonical.Replay
import CollatzLean.Collatz2.Orbit.RealizationRecovery
import CollatzLean.Collatz2.Orbit.RunDefect

/-!
# Collatz2: finite survival classification

有限 exponent word `w` を exact に辿る start のうち、全 prefix endpoint が
start 以上に残るものを二つの独立な shadow で完全分類する。

* 2-adic side:
  `x % residueModulus w = canonicalStart w`
* real / center side:
  全 contracting prefix `u` について

    `-(det u) * x <= B_u`

  が成立する。

後者は division-free な `x <= center(u)` であり、expanding prefix では
start defect が自動的に非負なので条件を課す必要がない。

従って finite survival start 全体は

  odd-start residue cylinder
    ∩
  contracting-prefix center half-lines

として exact に記述される。
-/

namespace Collatz2

namespace Word

/--
全 prefix の start defect が非負である。
actual run 上では各 prefix endpoint が start 以上であることと同値になる。
-/
def AllPrefixStartDefectsNonnegative (w : Word) (x : ℕ) : Prop :=
  ∀ u v : Word,
    u ++ v = w →
    0 ≤ startDefect u x

/--
全 contracting prefix の finite center より start が右へ出ないことを
除算なしで表す barrier 条件。

negative determinant では `G = -det > 0` なので

  `G * x <= B`

は exactly `x <= B/G` に対応する。
-/
def ContractingPrefixBarrierAt (w : Word) (x : ℕ) : Prop :=
  ∀ u v : Word,
    u ++ v = w →
    (AffineTransfer.ofWord u).determinant < 0 →
    (-(AffineTransfer.ofWord u).determinant) * (x : ℤ) ≤
      ((AffineTransfer.ofWord u).translate : ℤ)

/--
actual prefix run が存在するたび、その endpoint が共通 start 以上に残る。
full run の存在とは分離して定義し、分類定理で両者を合わせる。
-/
def AllPrefixesSurviveAt (w : Word) (x : ℕ) : Prop :=
  ∀ u v : Word,
    u ++ v = w →
    ∀ z : ℕ,
      Runs u x z →
      x ≤ z

/--
`w` を exact に辿る run が存在し、かつ全 prefix が start 以上に残る。
-/
def FiniteSurvivalStart (w : Word) (x : ℕ) : Prop :=
  (∃ y : ℕ, Runs w x y) ∧ AllPrefixesSurviveAt w x

/--
actual realization 上では、非負 start defect は non-descent と exact に同値。
strict positive-return theorem の non-strict 版。
-/
theorem Realizes.start_le_end_iff_startDefect_nonneg
    {w : Word} {x y : ℕ}
    (h : Realizes w x y) :
    x ≤ y ↔ 0 ≤ startDefect w x := by
  have hA :
      (0 : ℤ) < ((AffineTransfer.ofWord w).twoCoeff : ℤ) := by
    change (0 : ℤ) < ((2 ^ twoSteps w : ℕ) : ℤ)
    exact_mod_cast
      (Nat.pow_pos (by omega : 0 < (2 : ℕ)) : 0 < 2 ^ twoSteps w)
  have hT : (AffineTransfer.ofWord w).Realizes x y := h
  have hdef := hT.startDefect_eq_displacement
  change x ≤ y ↔ 0 ≤ (AffineTransfer.ofWord w).startDefect x
  rw [hdef]
  constructor
  · intro hxy
    have hdiff : (0 : ℤ) ≤ (y : ℤ) - (x : ℤ) := by
      omega
    exact mul_nonneg (le_of_lt hA) hdiff
  · intro hnonneg
    by_contra hxy
    have hdiff : (y : ℤ) - (x : ℤ) < 0 := by
      omega
    nlinarith

/--
全 prefix defect の非負性は、contracting prefix にだけ center barrier を課すことと同値。
expanding / zero-determinant prefix は translation の非負性だけで自動通過する。
-/
theorem allPrefixStartDefectsNonnegative_iff_contractingPrefixBarrierAt
    (w : Word) (x : ℕ) :
    AllPrefixStartDefectsNonnegative w x ↔
      ContractingPrefixBarrierAt w x := by
  constructor
  · intro hdef u v huv hneg
    have hu := hdef u v huv
    change
      0 ≤
        ((AffineTransfer.ofWord u).translate : ℤ) +
          (AffineTransfer.ofWord u).determinant * (x : ℤ)
      at hu
    nlinarith
  · intro hbar u v huv
    by_cases hneg : (AffineTransfer.ofWord u).determinant < 0
    · have hu := hbar u v huv hneg
      change
        0 ≤
          ((AffineTransfer.ofWord u).translate : ℤ) +
            (AffineTransfer.ofWord u).determinant * (x : ℤ)
      nlinarith
    · have hdet :
          0 ≤ (AffineTransfer.ofWord u).determinant :=
        le_of_not_gt hneg
      have hx : (0 : ℤ) ≤ (x : ℤ) := by
        positivity
      have hmul :
          0 ≤ (AffineTransfer.ofWord u).determinant * (x : ℤ) :=
        mul_nonneg hdet hx
      have hB :
          0 ≤ ((AffineTransfer.ofWord u).translate : ℤ) := by
        positivity
      change
        0 ≤
          ((AffineTransfer.ofWord u).translate : ℤ) +
            (AffineTransfer.ofWord u).determinant * (x : ℤ)
      exact add_nonneg hB hmul

/--
full stepwise run が与えられているとき、actual prefix survival は
全 prefix start-defect 非負性と exact に同値。
-/
theorem allPrefixesSurviveAt_iff_allPrefixStartDefectsNonnegative
    {w : Word} {x y : ℕ}
    (hrun : Runs w x y) :
    AllPrefixesSurviveAt w x ↔
      AllPrefixStartDefectsNonnegative w x := by
  constructor
  · intro hsurv u v huv
    have hsplit : Runs (u ++ v) x y := by
      rw [huv]
      exact hrun
    obtain ⟨z, hu, _hv⟩ := Runs.split_append hsplit
    have hxz : x ≤ z := hsurv u v huv z hu
    exact (hu.realizes.start_le_end_iff_startDefect_nonneg).1 hxz
  · intro hdef u v huv z hu
    exact
      (hu.realizes.start_le_end_iff_startDefect_nonneg).2
        (hdef u v huv)

/--
full run 上の actual prefix survival は、division-free contracting-center barrier
だけで完全に判定できる。
-/
theorem allPrefixesSurviveAt_iff_contractingPrefixBarrierAt
    {w : Word} {x y : ℕ}
    (hrun : Runs w x y) :
    AllPrefixesSurviveAt w x ↔
      ContractingPrefixBarrierAt w x := by
  rw [
    allPrefixesSurviveAt_iff_allPrefixStartDefectsNonnegative hrun,
    allPrefixStartDefectsNonnegative_iff_contractingPrefixBarrierAt
  ]

/--
valid nonempty word を exact に辿る run が `x` から存在することは、
`x` がその word の odd-start residue class に属することと exact に同値。

逆向きでは canonical realization を replay し、`RealizationRecovery` で
stepwise normalized `Runs` を回復する。
-/
theorem exists_runs_iff_start_mod_eq_canonicalStart
    {w : Word} {x : ℕ}
    (hvalid : w.Valid)
    (hne : w ≠ []) :
    (∃ y : ℕ, Runs w x y) ↔
      x % residueModulus w = canonicalStart w := by
  constructor
  · rintro ⟨y, hrun⟩
    exact
      hrun.realizes.start_mod_eq_canonicalStart
        (hrun.end_odd_of_ne_nil hne)
  · intro hmod
    let q : ℕ := x / residueModulus w
    let y : ℕ :=
      canonicalEnd w + 2 * 3 ^ oddSteps w * q
    have hdecomp := Nat.mod_add_div x (residueModulus w)
    have hx :
        x = canonicalStart w + residueModulus w * q := by
      rw [hmod] at hdecomp
      dsimp [q]
      simpa [Nat.mul_comm] using hdecomp.symm
    have hreal0 :
        Realizes w
          (canonicalStart w + residueModulus w * q)
          (canonicalEnd w + 2 * 3 ^ oddSteps w * q) :=
      (canonicalEnd_realizes w).replay q
    have hreal : Realizes w x y := by
      dsimp [y]
      rw [hx]
      exact hreal0
    have hyOdd : Odd y := by
      rcases canonicalEnd_odd w with ⟨k, hk⟩
      refine ⟨k + 3 ^ oddSteps w * q, ?_⟩
      dsimp [y]
      rw [hk]
      ring
    exact
      ⟨y, hreal.toRuns_of_valid_of_end_odd hvalid hyOdd⟩

/--
## Finite Survival Classification

valid nonempty exponent word `w` に対して、その word を exact に辿り、
全 prefix endpoint が start `x` 以上に残ることは、exact に次の二条件へ分解される。

1. `x` は `w` の一意な odd-start 2-adic residue class に属する。
2. `x` は全 contracting prefix の finite center の survival 側にある。

従って有限 survival start の集合は

  `oddStartClass(w) ∩ contracting-prefix center barriers`

で完全分類される。
-/
theorem finiteSurvivalClassification
    {w : Word} {x : ℕ}
    (hvalid : w.Valid)
    (hne : w ≠ []) :
    FiniteSurvivalStart w x ↔
      x % residueModulus w = canonicalStart w ∧
        ContractingPrefixBarrierAt w x := by
  constructor
  · rintro ⟨hexists, hsurv⟩
    rcases hexists with ⟨y, hrun⟩
    have hmod :
        x % residueModulus w = canonicalStart w :=
      (exists_runs_iff_start_mod_eq_canonicalStart hvalid hne).1
        ⟨y, hrun⟩
    have hbar : ContractingPrefixBarrierAt w x :=
      (allPrefixesSurviveAt_iff_contractingPrefixBarrierAt hrun).1 hsurv
    exact ⟨hmod, hbar⟩
  · rintro ⟨hmod, hbar⟩
    obtain ⟨y, hrun⟩ :=
      (exists_runs_iff_start_mod_eq_canonicalStart hvalid hne).2 hmod
    have hsurv : AllPrefixesSurviveAt w x :=
      (allPrefixesSurviveAt_iff_contractingPrefixBarrierAt hrun).2 hbar
    exact ⟨⟨y, hrun⟩, hsurv⟩

/--
canonical `q=0` layerでは residue 条件が自動なので、finite survival は
contracting-prefix center barrier だけに縮退する。
-/
theorem canonicalStart_finiteSurvival_iff_contractingPrefixBarrierAt
    {w : Word}
    (hvalid : w.Valid)
    (hne : w ≠ []) :
    FiniteSurvivalStart w (canonicalStart w) ↔
      ContractingPrefixBarrierAt w (canonicalStart w) := by
  rw [finiteSurvivalClassification hvalid hne]
  simp [Nat.mod_eq_of_lt (canonicalStart_lt_modulus w)]

end Word
end Collatz2
