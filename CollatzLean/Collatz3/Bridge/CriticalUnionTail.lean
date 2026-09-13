import CollatzLean.Collatz3.Bridge.SurvivorActualResidue
import CollatzLean.Collatz3.Bridge.CriticalFirstCrossingKraft
import CollatzLean.Collatz3.Bridge.CriticalWidthDisjoint
import CollatzLean.Collatz3.Bridge.FullFirstCrossingFiniteWidthBound

import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Ring

/-!
# Collatz3 Bridge: 全幅 critical union の survivor tail

前段では positive physical depth `n` について

`ParityComposition n ≃ odd residues mod 2^n`

を actual canonical start から構成し、そのうち survivor code に対応する剰余類が
exact に `survivorParityCount n` 本であることを示した。

このファイルでは、幅 `m` の actual critical / full first-crossing start が、
より小さい幅 `L < m` の critical depth

`H_L = criticalTwoDepth L`

まで必ず survivor residue に残ることを証明する。

核心は二段階である。

1. finite parity prefix `ParityPrefixRuns u x y` と actual run `Runs v x z` が同じ始点を持ち、
   `twoSteps u ≤ twoSteps v` なら、`u` は `v` の physical prefix として block 境界が整列する。
2. full first-crossing word の proper prefix は Beatty roof 以下なので、terminal critical depth
   より手前の任意の finite parity prefix は survivor 条件を満たす。

これにより、全幅 union の high-width tail を一つの fixed-depth survivor residue union で
一様に覆える。後続の global density squeeze のための包含核である。
-/

namespace Collatz3
namespace Bridge

/--
finite parity prefix と actual odd-only run の block 境界整列。

`u` の total physical depth が `v` 以下なら、

* `u` の block 数は `v` 以下、
* `u` のすべての proper block endpoint は `v` の同じ block endpoint と一致、
* `u` の terminal depth は `v` の `length u` 番目 block endpoint 以下

となる。
-/
theorem parityPrefixRuns_aligns_with_runs
    {u v : Word}
    {x y z : ℕ}
    (hu : ParityPrefixRuns u x y)
    (hv : Runs v x z)
    (hDepth : Word.twoSteps u ≤ Word.twoSteps v) :
    Word.oddSteps u ≤ Word.oddSteps v ∧
      (∀ k : ℕ, k < Word.oddSteps u →
        Word.prefixTwoDepth u k = Word.prefixTwoDepth v k) ∧
      Word.twoSteps u ≤
        Word.prefixTwoDepth v (Word.oddSteps u) := by
  induction hu generalizing v z with
  | @single e x y he hEq =>
      cases hv with
      | nil x =>
          simp [Word.twoSteps] at hDepth
          omega
      | @cons f v x m z hHead hTail =>
          have hef : e ≤ f := by
            by_contra hNot
            have hfe : f < e := Nat.lt_of_not_ge hNot
            exact no_longer_division_after_oddStep hfe hHead hEq
          constructor
          · simp [Word.oddSteps]
          · constructor
            · intro k hk
              have hk0 : k = 0 := by
                simpa [Word.oddSteps] using hk
              subst k
              simp
            · simpa [Word.twoSteps, Word.oddSteps] using hef
  | @cons e f x m y w hHead hTail ih =>
      cases hv with
      | nil x =>
          have hPos : 0 < Word.twoSteps (e :: f :: w) := by
            have he : 0 < e := hHead.exponent_pos
            simp [Word.twoSteps, he]
          have hZero :
              Word.twoSteps (e :: f :: w) ≤ 0 := by
            simpa [Word.twoSteps] using hDepth
          omega
      | @cons g v x n z hHead' hRunTail =>
          have hDet := OddStep.deterministic hHead hHead'
          rcases hDet with ⟨heg, hmn⟩
          subst g
          subst n
          have hTailDepth :
              Word.twoSteps (f :: w) ≤ Word.twoSteps v := by
            have hDepth' :
                e + Word.twoSteps (f :: w) ≤
                  e + Word.twoSteps v := by
              simpa [Word.twoSteps] using hDepth
            omega
          have hIH := ih hRunTail hTailDepth
          constructor
          · simpa [Word.oddSteps] using
              Nat.add_le_add_right hIH.1 1
          · constructor
            · intro k hk
              cases k with
              | zero => simp
              | succ k =>
                  have hkTail : k < Word.oddSteps (f :: w) := by
                    simp [Word.oddSteps] at hk ⊢
                    omega
                  have hEqTail := hIH.2.1 k hkTail
                  simpa [Word.prefixTwoDepth_cons_succ] using
                    congrArg (fun t : ℕ => e + t) hEqTail
            · calc
                Word.twoSteps (e :: f :: w)
                    = e + Word.twoSteps (f :: w) := by
                        simp [Word.twoSteps]
                _ ≤ e +
                    Word.prefixTwoDepth v (Word.oddSteps (f :: w)) :=
                      Nat.add_le_add_left hIH.2.2 e
                _ =
                    Word.prefixTwoDepth (e :: v)
                      (Word.oddSteps (e :: f :: w)) := by
                      simp [Word.oddSteps, Word.prefixTwoDepth_cons_succ]

/--
`x mod 2^n` が composition `c` の actual parity residue と一致すれば、
`c` は始点 `x` から finite parity prefix として実現される。

最後の endpoint の奇偶は要求しないため modulus は `2^n` で十分である。
-/
theorem exists_parityPrefixRuns_of_mod_eq_residue
    {n x : ℕ}
    (hn : 0 < n)
    (c : ParityComposition n)
    (hx :
      x % 2 ^ n = (parityCompositionResidue hn c).1) :
    ∃ y : ℕ, ParityPrefixRuns c.blocks x y := by
  let M := 2 ^ n
  let R := Word.canonicalStart c.blocks
  let A := 3 ^ c.length * x + Word.affineConst c.blocks
  have hxR : x % M = R % M := by
    dsimp [M, R]
    exact hx.trans (parityCompositionResidue_val hn c)
  have hMulMod :
      (3 ^ c.length * x) % M =
        (3 ^ c.length * R) % M := by
    calc
      (3 ^ c.length * x) % M
          = ((3 ^ c.length % M) * (x % M)) % M := by
              exact Nat.mul_mod _ _ _
      _ = ((3 ^ c.length % M) * (R % M)) % M := by
              rw [hxR]
      _ = (3 ^ c.length * R) % M := by
              exact (Nat.mul_mod _ _ _).symm
  have hNumMod :
      A % M =
        (3 ^ c.length * R + Word.affineConst c.blocks) % M := by
    dsimp [A]
    calc
      (3 ^ c.length * x + Word.affineConst c.blocks) % M
          =
        ((3 ^ c.length * x) % M +
          Word.affineConst c.blocks % M) % M := by
            exact Nat.add_mod _ _ _
      _ =
        ((3 ^ c.length * R) % M +
          Word.affineConst c.blocks % M) % M := by
            rw [hMulMod]
      _ =
        (3 ^ c.length * R + Word.affineConst c.blocks) % M := by
            exact (Nat.add_mod _ _ _).symm
  have hCan := Word.req_equation c.blocks
  have hCan' :
      M * Word.canonicalEnd c.blocks =
        3 ^ c.length * R + Word.affineConst c.blocks := by
    dsimp [M, R]
    simpa using hCan
  have hRightZero :
      (3 ^ c.length * R + Word.affineConst c.blocks) % M = 0 := by
    rw [← hCan']
    simp [M]
  have hAmod : A % M = 0 := by
    rw [hNumMod, hRightZero]
  have hDvd : M ∣ A :=
    Nat.dvd_iff_mod_eq_zero.mpr hAmod
  let y := A / M
  have hMul : M * y = A := by
    dsimp [y]
    exact Nat.mul_div_cancel' hDvd
  have hEq : Word.EndpointEquation c.blocks x y := by
    apply (Word.endpointEquation_iff c.blocks x y).2
    dsimp [M, A] at hMul
    simpa using hMul
  have hValid : Word.Valid c.blocks := by
    intro e he
    exact c.blocks_pos he
  have hNe : c.blocks ≠ [] :=
    parityComposition_blocks_ne_nil hn c
  exact ⟨y, parityPrefixRuns_of_valid_endpointEquation hValid hNe hEq⟩

/-- exact critical word を terminal-overshoot 許容の full first-crossing word として読む。 -/
def criticalWordToFullFirstCrossingWord
    {m : ℕ}
    (W : Critical.CriticalWord m) :
    Critical.FullFirstCrossingWord m := by
  refine ⟨W.1, W.2.valid, W.2.oddSteps_eq, ?_⟩
  constructor
  · rw [W.2.oddSteps_eq, W.2.twoSteps_eq]
  · intro k hk
    rw [W.2.oddSteps_eq] at hk
    exact W.2.prefixTwoDepth_le_beatty hk

/--
full first-crossing actual run の terminal critical depth より手前を読んだ
finite parity prefix は survivor である。
-/
theorem parityPrefix_survivor_of_fullFirstCrossing_before_criticalDepth
    {m n x y z : ℕ}
    (W : Critical.FullFirstCrossingWord m)
    (hRun : Runs W.1 x y)
    (c : ParityComposition n)
    (hPref : ParityPrefixRuns c.blocks x z)
    (hnLt : n < Critical.criticalTwoDepth m) :
    IsSurvivorParityComposition c := by
  have hDepthLe : Word.twoSteps c.blocks ≤ Word.twoSteps W.1 := by
    have hCritLe := W.2.criticalTwoDepth_le_twoSteps
    simpa using le_trans (Nat.le_of_lt hnLt) hCritLe
  have hAlign :=
    parityPrefixRuns_aligns_with_runs hPref hRun hDepthLe
  have hLenLe : c.length ≤ m := by
    have h := hAlign.1
    simpa [W.2.oddSteps_eq] using h
  constructor
  · have hNBeatty : n ≤ Critical.beattyIndex c.length := by
      rcases lt_or_eq_of_le hLenLe with hlt | heq
      · have hTermAlign := hAlign.2.2
        have hRoof := W.2.prefixTwoDepth_le_beatty hlt
        have hTerm : n ≤ Word.prefixTwoDepth W.1 c.length := by
          simpa using hTermAlign
        exact le_trans hTerm hRoof
      · subst m
        rw [Critical.criticalTwoDepth_eq] at hnLt
        omega
    have hPow :
        2 ^ n ≤ 2 ^ Critical.beattyIndex c.length :=
      Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hNBeatty
    exact le_trans hPow (Critical.beattyIndex_lower c.length)
  · intro k hk
    have hkM : k < m := lt_of_lt_of_le hk hLenLe
    have hAlignK := hAlign.2.1 k (by simpa using hk)
    have hRoof := W.2.prefixTwoDepth_le_beatty hkM
    have hDepth : c.sizeUpTo k ≤ Critical.beattyIndex k := by
      change Word.prefixTwoDepth c.blocks k ≤ Critical.beattyIndex k
      rw [hAlignK]
      exact hRoof
    have hPow :
        2 ^ c.sizeUpTo k ≤ 2 ^ Critical.beattyIndex k :=
      Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hDepth
    exact le_trans hPow (Critical.beattyIndex_lower k)

/-- exact critical word 版。 -/
theorem parityPrefix_survivor_of_critical_before_terminal
    {m n x y z : ℕ}
    (W : Critical.CriticalWord m)
    (hRun : Runs W.1 x y)
    (c : ParityComposition n)
    (hPref : ParityPrefixRuns c.blocks x z)
    (hnLt : n < Critical.criticalTwoDepth m) :
    IsSurvivorParityComposition c := by
  exact
    parityPrefix_survivor_of_fullFirstCrossing_before_criticalDepth
      (criticalWordToFullFirstCrossingWord W)
      hRun c hPref hnLt

/-- critical depth は常に positive。 -/
theorem criticalTwoDepth_pos (m : ℕ) :
    0 < Critical.criticalTwoDepth m := by
  rw [Critical.criticalTwoDepth_eq]
  omega

/-- `2^n` は positive depth では偶数。 -/
theorem twoPow_even_of_pos
    {n : ℕ}
    (hn : 0 < n) :
    Even (2 ^ n) := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn) with ⟨k, rfl⟩
  refine ⟨2 ^ k, ?_⟩
  rw [pow_succ]
  ring

/--
actual start `x` が持つ odd residue modulo `2^n`。
-/
def oddParityResidueOfOddStart
    {n x : ℕ}
    (hn : 0 < n)
    (hx : Odd x) :
    OddParityResidue n :=
  ⟨x % 2 ^ n,
    Nat.mod_lt _ (Arithmetic.twoPow_pos n),
    (Odd.mod_even_iff (twoPow_even_of_pos hn)).2 hx⟩

/--
幅 `m` の actual critical start は、より小さい critical depth `H_L` では
survivor residue union に属する。
-/
theorem actualCriticalStart_tail_isSurvivorResidueStart
    {L m x : ℕ}
    (hL : 0 < L)
    (hLm : L < m)
    (hStart : IsActualCriticalStart m x) :
    IsSurvivorResidueStart
      (Critical.criticalTwoDepth L)
      (criticalTwoDepth_pos L)
      x := by
  let n := Critical.criticalTwoDepth L
  let hn : 0 < n := criticalTwoDepth_pos L
  have hm : 0 < m := lt_trans hL hLm
  rcases hStart with ⟨W, y, hRun⟩
  have hxOdd : Odd x :=
    hRun.start_odd_of_nonempty (criticalWord_nonempty hm W)
  let r : OddParityResidue n :=
    oddParityResidueOfOddStart hn hxOdd
  let e := parityCompositionEquivOddResidue n hn
  let c : ParityComposition n := e.symm r
  have hcResidue : parityCompositionResidue hn c = r := by
    exact e.apply_symm_apply r
  have hxMod :
      x % 2 ^ n = (parityCompositionResidue hn c).1 := by
    have hVal := congrArg Subtype.val hcResidue
    dsimp [r, oddParityResidueOfOddStart] at hVal
    exact hVal.symm
  rcases exists_parityPrefixRuns_of_mod_eq_residue hn c hxMod with
    ⟨z, hPref⟩
  have hnLt : n < Critical.criticalTwoDepth m := by
    dsimp [n]
    exact criticalTwoDepth_strictMono hLm
  have hSurvivor : IsSurvivorParityComposition c :=
    parityPrefix_survivor_of_critical_before_terminal
      W hRun c hPref hnLt
  exact ⟨⟨c, hSurvivor⟩, hxMod⟩

/--
full first-crossing actual start でも同じ high-width tail containment が成立する。
terminal overshoot の大きさには依存しない。
-/
theorem fullActualCriticalStart_tail_isSurvivorResidueStart
    {L m x : ℕ}
    (hL : 0 < L)
    (hLm : L < m)
    (hStart : IsFullActualCriticalStart m x) :
    IsSurvivorResidueStart
      (Critical.criticalTwoDepth L)
      (criticalTwoDepth_pos L)
      x := by
  let n := Critical.criticalTwoDepth L
  let hn : 0 < n := criticalTwoDepth_pos L
  have hm : 0 < m := lt_trans hL hLm
  rcases hStart with ⟨W, y, hRun⟩
  have hxOdd : Odd x :=
    hRun.start_odd_of_nonempty (Critical.FullFirstCrossingWord.nonempty hm W)
  let r : OddParityResidue n :=
    oddParityResidueOfOddStart hn hxOdd
  let e := parityCompositionEquivOddResidue n hn
  let c : ParityComposition n := e.symm r
  have hcResidue : parityCompositionResidue hn c = r := by
    exact e.apply_symm_apply r
  have hxMod :
      x % 2 ^ n = (parityCompositionResidue hn c).1 := by
    have hVal := congrArg Subtype.val hcResidue
    dsimp [r, oddParityResidueOfOddStart] at hVal
    exact hVal.symm
  rcases exists_parityPrefixRuns_of_mod_eq_residue hn c hxMod with
    ⟨z, hPref⟩
  have hnLt : n < Critical.criticalTwoDepth m := by
    dsimp [n]
    exact criticalTwoDepth_strictMono hLm
  have hSurvivor : IsSurvivorParityComposition c :=
    parityPrefix_survivor_of_fullFirstCrossing_before_criticalDepth
      W hRun c hPref hnLt
  exact ⟨⟨c, hSurvivor⟩, hxMod⟩

end Bridge
end Collatz3
