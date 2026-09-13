import CollatzLean.Collatz3.Bridge.FiniteParityResidue
import CollatzLean.Collatz3.Bridge.CriticalSurvivorParity
import Mathlib.SetTheory.Cardinal.Finite

import Mathlib.Tactic.Ring

/-!
# Collatz3 Bridge: survivor parity code と actual start residue classes

`FiniteParityResidue` により positive depth `n` では

`ParityComposition n ≃ odd residues mod 2^n`

が exact に得られた。

このファイルではその equivalence を `SurvivorParityCode n` に制限する。
したがって depth `n` の survivor code は、actual start 側では pairwise disjoint な
`survivorParityCount n` 本の合同類 modulo `2^n` を与える。

さらに full block `q * 2^n` 未満では survivor residue starts の個数が exact に

`survivorParityCount n * q`

であることまで有限型 equivalence として閉じる。
これは後続の global critical-width tail を survivor residue union で一様に覆うための
counting kernel になる。
-/

namespace Collatz3
namespace Bridge

/-- odd residue が depth `n` の survivor code から来ること。 -/
def IsSurvivorParityResidue
    {n : ℕ}
    (hn : 0 < n)
    (r : OddParityResidue n) : Prop :=
  ∃ S : SurvivorParityCode n,
    parityCompositionResidue hn S.1 = r

/-- depth `n` の survivor odd residue classes。 -/
abbrev SurvivorParityResidue
    (n : ℕ)
    (hn : 0 < n) :=
  {r : OddParityResidue n // IsSurvivorParityResidue hn r}

/-- survivor code をその actual residue class へ送る。 -/
noncomputable def survivorParityCodeToResidue
    {n : ℕ}
    (hn : 0 < n) :
    SurvivorParityCode n → SurvivorParityResidue n hn :=
  fun S =>
    ⟨parityCompositionResidue hn S.1,
      ⟨S, rfl⟩⟩

/-- survivor code -> residue map は単射。 -/
theorem survivorParityCodeToResidue_injective
    {n : ℕ}
    (hn : 0 < n) :
    Function.Injective (survivorParityCodeToResidue hn) := by
  intro S T h
  apply Subtype.ext
  apply parityCompositionResidue_injective hn
  exact congrArg (fun r : SurvivorParityResidue n hn => r.1) h

/-- survivor residue の定義から map は全射。 -/
theorem survivorParityCodeToResidue_surjective
    {n : ℕ}
    (hn : 0 < n) :
    Function.Surjective (survivorParityCodeToResidue hn) := by
  intro r
  rcases r.2 with ⟨S, hS⟩
  refine ⟨S, ?_⟩
  apply Subtype.ext
  exact hS

/-- survivor code と survivor actual residue class の exact equivalence。 -/
noncomputable def survivorParityCodeEquivResidue
    (n : ℕ)
    (hn : 0 < n) :
    SurvivorParityCode n ≃ SurvivorParityResidue n hn :=
  Equiv.ofBijective
    (survivorParityCodeToResidue hn)
    ⟨survivorParityCodeToResidue_injective hn,
      survivorParityCodeToResidue_surjective hn⟩

/-- survivor residue class の本数は exactly `S_n`。 -/
theorem natCard_survivorParityResidue
    {n : ℕ}
    (hn : 0 < n) :
    Nat.card (SurvivorParityResidue n hn) = survivorParityCount n := by
  unfold survivorParityCount
  exact
    (Nat.card_congr (survivorParityCodeEquivResidue n hn)).symm

/-- 異なる survivor code は異なる residue modulo `2^n` を持つ。 -/
theorem survivorParityResidue_ne_of_code_ne
    {n : ℕ}
    (hn : 0 < n)
    {S T : SurvivorParityCode n}
    (hST : S ≠ T) :
    parityCompositionResidue hn S.1 ≠
      parityCompositionResidue hn T.1 := by
  intro h
  apply hST
  apply Subtype.ext
  exact parityCompositionResidue_injective hn h

/--
自然数 start が depth `n` の survivor residue union に属すること。
actual Collatz orbit の tail bridge ではこの述語へ包含する。
-/
def IsSurvivorResidueStart
    (n : ℕ)
    (hn : 0 < n)
    (x : ℕ) : Prop :=
  ∃ S : SurvivorParityCode n,
    x % 2 ^ n = (parityCompositionResidue hn S.1).1

/-- survivor residue class 自体を使った同値な記述。 -/
theorem isSurvivorResidueStart_iff_exists_residue
    {n x : ℕ}
    (hn : 0 < n) :
    IsSurvivorResidueStart n hn x ↔
      ∃ r : SurvivorParityResidue n hn,
        x % 2 ^ n = r.1.1 := by
  constructor
  · rintro ⟨S, hx⟩
    exact ⟨survivorParityCodeToResidue hn S, hx⟩
  · rintro ⟨r, hx⟩
    rcases r.2 with ⟨S, hS⟩
    refine ⟨S, ?_⟩
    exact hx.trans (congrArg Subtype.val hS).symm

/-- survivor residue predicate は `2^n` 周期。 -/
theorem isSurvivorResidueStart_add_period
    {n x : ℕ}
    (hn : 0 < n)
    (k : ℕ) :
    IsSurvivorResidueStart n hn x ↔
      IsSurvivorResidueStart n hn (x + 2 ^ n * k) := by
  constructor <;> rintro ⟨S, hS⟩ <;> refine ⟨S, ?_⟩
  · rw [Nat.add_mul_mod_self_left]
    exact hS
  · rw [Nat.add_mul_mod_self_left] at hS
    exact hS

/-- `B` 未満の survivor residue starts。 -/
abbrev SurvivorResidueStartBelow
    (n : ℕ)
    (hn : 0 < n)
    (B : ℕ) :=
  {x : ℕ // x < B ∧ IsSurvivorResidueStart n hn x}

/-- bounded survivor residue starts は有限。 -/
theorem survivorResidueStartBelow_finite
    (n : ℕ)
    (hn : 0 < n)
    (B : ℕ) :
    Finite (SurvivorResidueStartBelow n hn B) := by
  exact
    Finite.of_injective
      (fun x : SurvivorResidueStartBelow n hn B =>
        (⟨x.1, x.2.1⟩ : Fin B))
      (by
        intro a b h
        apply Subtype.ext
        exact congrArg Fin.val h)

/-- bounded survivor residue start count。 -/
noncomputable def survivorResidueStartCount
    (n : ℕ)
    (hn : 0 < n)
    (B : ℕ) : ℕ :=
  Nat.card (SurvivorResidueStartBelow n hn B)

/--
`S : SurvivorParityCode n` と block index `k<q` から
`q * 2^n` 未満の actual residue start を作る。
-/
noncomputable def survivorResidueBlockCodeToStart
    {n : ℕ}
    (hn : 0 < n)
    (q : ℕ) :
    (SurvivorParityCode n × Fin q) →
      SurvivorResidueStartBelow n hn (2 ^ n * q) :=
  fun code => by
    let S := code.1
    let k := code.2
    let r := (parityCompositionResidue hn S.1).1
    refine ⟨r + 2 ^ n * k.1, ?_, ?_⟩
    · have hr : r < 2 ^ n := (parityCompositionResidue hn S.1).2.1
      have hk : k.1 + 1 ≤ q := Nat.succ_le_iff.mpr k.2
      calc
        r + 2 ^ n * k.1
            < 2 ^ n + 2 ^ n * k.1 :=
          Nat.add_lt_add_right hr _
        _ = 2 ^ n * (k.1 + 1) := by ring
        _ ≤ 2 ^ n * q := Nat.mul_le_mul_left _ hk
    · refine ⟨S, ?_⟩
      dsimp [r]
      rw [Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt (parityCompositionResidue hn S.1).2.1

/-- full-block encoding は単射。 -/
theorem survivorResidueBlockCodeToStart_injective
    {n : ℕ}
    (hn : 0 < n)
    (q : ℕ) :
    Function.Injective (survivorResidueBlockCodeToStart hn q) := by
  intro A B h
  rcases A with ⟨S, k⟩
  rcases B with ⟨T, l⟩
  have hVal :
      (parityCompositionResidue hn S.1).1 + 2 ^ n * k.1 =
        (parityCompositionResidue hn T.1).1 + 2 ^ n * l.1 :=
    congrArg Subtype.val h
  have hMod := congrArg (fun x : ℕ => x % 2 ^ n) hVal
  have hResidue :
      (parityCompositionResidue hn S.1).1 =
        (parityCompositionResidue hn T.1).1 := by
    have hLeft :
        ((parityCompositionResidue hn S.1).1 + 2 ^ n * k.1) % 2 ^ n =
          (parityCompositionResidue hn S.1).1 := by
      rw [Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt (parityCompositionResidue hn S.1).2.1
    have hRight :
        ((parityCompositionResidue hn T.1).1 + 2 ^ n * l.1) % 2 ^ n =
          (parityCompositionResidue hn T.1).1 := by
      rw [Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt (parityCompositionResidue hn T.1).2.1
    rw [hLeft, hRight] at hMod
    exact hMod
  have hST : S = T := by
    apply Subtype.ext
    apply parityCompositionResidue_injective hn
    apply Subtype.ext
    exact hResidue
  subst T
  apply Prod.ext
  · rfl
  · apply Fin.ext
    have hMul : 2 ^ n * k.1 = 2 ^ n * l.1 := by
      exact Nat.add_left_cancel hVal
    exact Nat.mul_left_cancel (Arithmetic.twoPow_pos n) hMul

/-- full-block encoding は全射。 -/
theorem survivorResidueBlockCodeToStart_surjective
    {n : ℕ}
    (hn : 0 < n)
    (q : ℕ) :
    Function.Surjective (survivorResidueBlockCodeToStart hn q) := by
  intro x
  rcases x.2.2 with ⟨S, hMod⟩
  let r := (parityCompositionResidue hn S.1).1
  let k := x.1 / 2 ^ n
  have hDecomp : x.1 % 2 ^ n + 2 ^ n * k = x.1 := by
    simpa [k] using Nat.mod_add_div x.1 (2 ^ n)
  have hxEq : x.1 = r + 2 ^ n * k := by
    dsimp [r]
    rw [hMod] at hDecomp
    exact hDecomp.symm
  have hk : k < q := by
    by_contra hNot
    have hqk : q ≤ k := Nat.le_of_not_gt hNot
    have hMul : 2 ^ n * q ≤ 2 ^ n * k :=
      Nat.mul_le_mul_left _ hqk
    have hTail : 2 ^ n * k ≤ r + 2 ^ n * k := by omega
    have : 2 ^ n * q ≤ x.1 := by
      rw [hxEq]
      exact le_trans hMul hTail
    omega
  refine ⟨(S, ⟨k, hk⟩), ?_⟩
  apply Subtype.ext
  change r + 2 ^ n * k = x.1
  exact hxEq.symm

/--
最初の `q` 個の `2^n` blocks と `SurvivorParityCode n × Fin q` は exact に同値。
-/
noncomputable def survivorResidueBlockCodeEquivStartBelow
    {n : ℕ}
    (hn : 0 < n)
    (q : ℕ) :
    (SurvivorParityCode n × Fin q) ≃
      SurvivorResidueStartBelow n hn (2 ^ n * q) :=
  Equiv.ofBijective
    (survivorResidueBlockCodeToStart hn q)
    ⟨survivorResidueBlockCodeToStart_injective hn q,
      survivorResidueBlockCodeToStart_surjective hn q⟩

/--
full `q` blocks では survivor residue start count は exact に `S_n * q`。
-/
theorem survivorResidueStartCount_block_eq
    {n : ℕ}
    (hn : 0 < n)
    (q : ℕ) :
    survivorResidueStartCount n hn (2 ^ n * q) =
      survivorParityCount n * q := by
  unfold survivorResidueStartCount survivorParityCount
  calc
    Nat.card (SurvivorResidueStartBelow n hn (2 ^ n * q))
        = Nat.card (SurvivorParityCode n × Fin q) :=
      (Nat.card_congr (survivorResidueBlockCodeEquivStartBelow hn q)).symm
    _ = Nat.card (SurvivorParityCode n) * Nat.card (Fin q) :=
      Nat.card_prod _ _
    _ = Nat.card (SurvivorParityCode n) * q := by
      rw [Nat.card_fin]

/-- one period contains exactly `S_n` survivor residue starts。 -/
theorem survivorResidueStartCount_one_period
    {n : ℕ}
    (hn : 0 < n) :
    survivorResidueStartCount n hn (2 ^ n) = survivorParityCount n := by
  have h := survivorResidueStartCount_block_eq hn 1
  simpa using h

end Bridge
end Collatz3
