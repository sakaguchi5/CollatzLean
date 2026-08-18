import CollatzLean.Collatz2.CSTMicro.CarryGeometry.ExactNormalizedFerrersLedger
import CollatzLean.Collatz2.CSTMicro.BinaryFerrersOrder

/-!
# Ferrers cell residue potential

`ExactNormalizedFerrersLedger` では一つの adjacent Ferrers cell の contribution を
canonical Farey residue `D` として持ち、chain 全体で

  q_finish - q_start
    = sum D - G * noCarryCount

を得た。

このファイルでは `D` が chain の履歴ではなく Ferrers cell 座標だけで決まることを
明示し、その cell weight を prefix-height diagram 全体へ積分する potential を作る。

binary Ferrers step `01 -> 10` は prefix height を `position + 1` の一箇所だけ
1 増やす。その一セルの座標は

  i = position
  a = oddCount(leftContext) + 1

であり、Farey residue も共通 endpoint `(k,m)` と `(i,a)` だけから復元できる。

したがって

  Potential(upper) = Potential(lower) + D

であり、任意の Ferrers chain について

  normalizedCellResidueSum C
    = Potential(finish) - Potential(start)

を得る。特に integer `sum D` 自体が chain-independent になる。
-/

namespace Collatz2
namespace CSTMicro

open scoped BigOperators

/-! ## 1. cell coordinate だけから Farey residue を再構成 -/

/--
共通 endpoint `(k,m)` と Ferrers cell 座標 `(i,a)` から作る canonical residue。

actual adjacent cell では

  d = k - i,
  r = m - a,
  u = 3^(-a) mod 2^d,
  h = 2^d - u,
  s = 3^a - (3^a*u)/2^d,
  D = 2^i*h - 3^r*s.
-/
def ferrersCellResidueWeight
    (k m i a : ℕ) : ℤ :=
  let d := k - i
  let r := m - a
  let u : ℕ := (invThreePow d a).val
  let q : ℕ := (3 ^ a * u) / (2 ^ d)
  let h : ℕ := 2 ^ d - u
  let s : ℤ := (3 : ℤ) ^ a - (q : ℤ)
  (2 : ℤ) ^ i * (h : ℤ) - (3 : ℤ) ^ r * s

namespace AdjacentFerrersSwap

/-- actual adjacent cell の Farey residue は cell coordinate weight に一致する。 -/
theorem fareyResidue_eq_ferrersCellResidueWeight
    (S : AdjacentFerrersSwap) :
    S.toFareyCellPacket.residue =
      ferrersCellResidueWeight
        S.length S.oddTotal S.position S.fareyLeftExponent := by
  have hd :
      S.length - S.position = S.fareyTailDepth := by
    rw [S.length_eq_position_add_fareyTailDepth]
    omega
  have hr :
      S.oddTotal - S.fareyLeftExponent =
        S.fareyRightExponent := by
    rw [S.oddTotal_eq_fareyLeftExponent_add_fareyRightExponent]
    omega
  have hResidue :
      S.toFareyCellPacket.residue =
        (2 : ℤ) ^ S.position * (S.fareyH : ℤ) -
          (3 : ℤ) ^ S.fareyRightExponent * S.fareyS := by
    unfold FareyCellPacket.residue
    dsimp [AdjacentFerrersSwap.toFareyCellPacket]
  have hWeight :
      ferrersCellResidueWeight
          S.length
          S.oddTotal
          S.position
          S.fareyLeftExponent
        =
      (2 : ℤ) ^ S.position * (S.fareyH : ℤ) -
        (3 : ℤ) ^ S.fareyRightExponent * S.fareyS := by
    unfold ferrersCellResidueWeight
    dsimp
    rw [hd, hr]
    unfold AdjacentFerrersSwap.fareyH
      AdjacentFerrersSwap.fareyS
      AdjacentFerrersSwap.fareyLocalQuotient
      AdjacentFerrersSwap.fareyLocalInverse
    rfl
  exact hResidue.trans hWeight.symm

/-- lower word の swap column height は `a-1`。 -/
theorem lower_prefixOddCount_at_cell
    (S : AdjacentFerrersSwap) :
    prefixOddCount S.lowerWord (S.position + 1) + 1 =
      S.fareyLeftExponent := by
  change
    prefixOddCount
        (S.leftContext ++ false :: true :: S.rightContext)
        (S.leftContext.length + 1) + 1 =
      oddCount S.leftContext + 1
  rw [prefixOddCount_append_cons_at]
  simp [bitNat]

/-- upper word の swap column height は exact に `a`。 -/
theorem upper_prefixOddCount_at_cell
    (S : AdjacentFerrersSwap) :
    prefixOddCount S.upperWord (S.position + 1) =
      S.fareyLeftExponent := by
  have h := S.upper_prefix_eq_lower_prefix_add_one
  have hl := S.lower_prefixOddCount_at_cell
  omega

end AdjacentFerrersSwap

/-! ## 2. prefix-height Ferrers potential -/

/-- 一つの prefix column `i+1` の cell-weight sum。 -/
def ferrersCellResidueColumn
    (v : ParityWord)
    (i : ℕ) : ℤ :=
  Finset.sum
    (Finset.range (prefixOddCount v (i + 1)))
    (fun h =>
      ferrersCellResidueWeight
        v.length (oddCount v) i (h + 1))

/--
word の Ferrers diagram 下にある全 cell residue の potential。

column `i` では height `prefixOddCount v (i+1)` までを積む。
-/
def ferrersCellResiduePotential
    (v : ParityWord) : ℤ :=
  Finset.sum
    (Finset.range v.length)
    (fun i =>
      ferrersCellResidueColumn v i)

namespace AdjacentFerrersSwap

private theorem position_lt_length
    (S : AdjacentFerrersSwap) :
    S.position < S.length := by
  unfold AdjacentFerrersSwap.position AdjacentFerrersSwap.length
  omega

/-- swap column 以外では lower / upper の prefix height は同じ。 -/
theorem prefixOddCount_upper_eq_lower_of_ne_position
    (S : AdjacentFerrersSwap)
    {i : ℕ}
    (hi : i ≠ S.position) :
    prefixOddCount S.upperWord (i + 1) =
      prefixOddCount S.lowerWord (i + 1) := by
  have hi' : i ≠ S.leftContext.length := by
    simpa [AdjacentFerrersSwap.position] using hi
  have h :
      prefixOddCount S.upperWord (i + 1) =
        prefixOddCount S.lowerWord (i + 1) +
          (if i = S.leftContext.length then 1 else 0) := by
    simpa [
      AdjacentFerrersSwap.upperWord,
      AdjacentFerrersSwap.lowerWord
    ] using
      prefixOddCount_swap_exact
        S.leftContext S.rightContext (i + 1)
  simpa [hi'] using h

/-- swap column 以外では cell-residue column sum も同じ。 -/
theorem ferrersCellResidueColumn_upper_eq_lower_of_ne_position
    (S : AdjacentFerrersSwap)
    {i : ℕ}
    (hi : i ≠ S.position) :
    ferrersCellResidueColumn S.upperWord i =
      ferrersCellResidueColumn S.lowerWord i := by
  unfold ferrersCellResidueColumn
  rw [S.prefixOddCount_upper_eq_lower_of_ne_position hi]
  rw [S.upperWord_length, S.lowerWord_length]
  rw [S.upperWord_oddCount, S.lowerWord_oddCount]

/-- swap column では column sum が exact に Farey residue `D` だけ増える。 -/
theorem ferrersCellResidueColumn_upper_eq_lower_add_residue_at_position
    (S : AdjacentFerrersSwap) :
    ferrersCellResidueColumn S.upperWord S.position =
      ferrersCellResidueColumn S.lowerWord S.position +
        S.toFareyCellPacket.residue := by
  unfold ferrersCellResidueColumn
  rw [S.upper_prefixOddCount_at_cell]
  have hl := S.lower_prefixOddCount_at_cell
  have haPos : 0 < S.fareyLeftExponent := by
    unfold AdjacentFerrersSwap.fareyLeftExponent
    omega
  have hpred :
      prefixOddCount S.lowerWord (S.position + 1) =
        S.fareyLeftExponent - 1 := by
    omega
  rw [hpred]
  rw [S.upperWord_length, S.lowerWord_length]
  rw [S.upperWord_oddCount, S.lowerWord_oddCount]
  have ha : S.fareyLeftExponent = (S.fareyLeftExponent - 1) + 1 := by
    omega
  rw [ha, Finset.sum_range_succ]
  have hlast :
      (S.fareyLeftExponent - 1) + 1 = S.fareyLeftExponent := by
    omega
  rw [hlast]
  have hWeight := S.fareyResidue_eq_ferrersCellResidueWeight
  rw [← hWeight]

/--
一つの adjacent Ferrers move は global cell potential を Farey residue `D` だけ増やす。
-/
theorem ferrersCellResiduePotential_upper_eq_lower_add_residue
    (S : AdjacentFerrersSwap) :
    ferrersCellResiduePotential S.upperWord =
      ferrersCellResiduePotential S.lowerWord +
        S.toFareyCellPacket.residue := by
  unfold ferrersCellResiduePotential
  rw [S.upperWord_length, S.lowerWord_length]
  let p := S.position
  have hp : p < S.length := by
    simpa [p] using S.position_lt_length
  have hpMem : p ∈ Finset.range S.length := by
    exact Finset.mem_range.mpr hp
  have hPointwise :
      ∀ i ∈ Finset.range S.length,
        ferrersCellResidueColumn S.upperWord i =
          ferrersCellResidueColumn S.lowerWord i +
            (if i = p then S.toFareyCellPacket.residue else 0) := by
    intro i hi
    by_cases hip : i = p
    · subst i
      rw [
        S.ferrersCellResidueColumn_upper_eq_lower_add_residue_at_position
      ]
      simp [p]
    · have hcol :=
        S.ferrersCellResidueColumn_upper_eq_lower_of_ne_position
          (by simpa [p] using hip)
      rw [hcol]
      simp [hip]
  calc
    Finset.sum
        (Finset.range S.length)
        (fun i =>
          ferrersCellResidueColumn S.upperWord i)
        =
      Finset.sum
        (Finset.range S.length)
        (fun i =>
          ferrersCellResidueColumn S.lowerWord i +
            (if i = p then S.toFareyCellPacket.residue else 0)) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hPointwise i hi
    _ =
      Finset.sum
          (Finset.range S.length)
          (fun i =>
            ferrersCellResidueColumn S.lowerWord i)
        +
      Finset.sum
          (Finset.range S.length)
          (fun i =>
            if i = p then S.toFareyCellPacket.residue else 0) := by
          rw [Finset.sum_add_distrib]
    _ =
      Finset.sum
          (Finset.range S.length)
          (fun i =>
            ferrersCellResidueColumn S.lowerWord i)
        +
      S.toFareyCellPacket.residue := by
          have hSingle :
              Finset.sum
                  (Finset.range S.length)
                  (fun i =>
                    if i = p
                    then S.toFareyCellPacket.residue
                    else 0)
                =
              S.toFareyCellPacket.residue := by
            classical
            rw [Finset.sum_eq_single p]
            · simp
            · intro b hb hbp
              simp [hbp]
            · exact fun hpNot =>
                False.elim (hpNot hpMem)
          rw [hSingle]

end AdjacentFerrersSwap

namespace FerrersStep

/-- FerrersStep 版の global potential increment。 -/
theorem ferrersCellResiduePotential_upper_eq_lower_add_residue
    {lower upper : ParityWord}
    (S : FerrersStep lower upper) :
    ferrersCellResiduePotential upper =
      ferrersCellResiduePotential lower +
        S.edge.toFareyCellPacket.residue := by
  have h := S.edge.ferrersCellResiduePotential_upper_eq_lower_add_residue
  rw [← S.lower_eq, ← S.upper_eq] at h
  exact h

end FerrersStep

/-! ## 3. chain telescope / integer path-independence -/

namespace FerrersChain

/--
chain の integer cell-residue sum は endpoint potential difference に exact 一致する。
-/
theorem normalizedCellResidueSum_eq_potential_sub
    {start finish : ParityWord}
    (C : FerrersChain start finish) :
    C.normalizedCellResidueSum =
      ferrersCellResiduePotential finish -
        ferrersCellResiduePotential start := by
  induction C with
  | refl =>
      simp [normalizedCellResidueSum]
  | @step u v C S ih =>
      have hStep := S.ferrersCellResiduePotential_upper_eq_lower_add_residue
      change
        C.normalizedCellResidueSum +
            S.edge.toFareyCellPacket.residue =
          ferrersCellResiduePotential v -
            ferrersCellResiduePotential start
      rw [ih, hStep]
      ring

/--
同じ endpoints を結ぶ Ferrers chain では integer `sum D` 自体が同じ。
-/
theorem normalizedCellResidueSum_chain_independent
    {start finish : ParityWord}
    (C₁ C₂ : FerrersChain start finish) :
    C₁.normalizedCellResidueSum = C₂.normalizedCellResidueSum := by
  rw [C₁.normalizedCellResidueSum_eq_potential_sub]
  rw [C₂.normalizedCellResidueSum_eq_potential_sub]

/--
first-passage endpoints では no-carry count も chain-independent。

integer cell sum と normalized endpoint delta が共に path-independent なので、
exact ledger の `G * noCarryCount` も一意になる。
-/
theorem normalizedNoCarryCount_chain_independent
    {start finish : ParityWord}
    (C₁ C₂ : FerrersChain start finish)
    (hStartFP : IsFirstPassageWord start) :
    C₁.normalizedNoCarryCount = C₂.normalizedNoCarryCount := by
  have h₁ :=
    C₁.normalizedDelta_eq_cellResidueSum_sub_gap_mul_noCarryCount hStartFP
  have h₂ :=
    C₂.normalizedDelta_eq_cellResidueSum_sub_gap_mul_noCarryCount hStartFP
  have hSum := C₁.normalizedCellResidueSum_chain_independent C₂
  have hDelta : C₁.normalizedDelta = C₂.normalizedDelta := by
    unfold FerrersChain.normalizedDelta
    rfl
  have hContract := hStartFP.2.2
  unfold CoefficientContracting at hContract
  have hGapNat : 0 < wordTerminalGap start := by
    unfold wordTerminalGap
    exact Nat.sub_pos_of_lt hContract
  have hGap : 0 < (wordTerminalGap start : ℤ) := by
    exact_mod_cast hGapNat
  have hCountCast :
      (C₁.normalizedNoCarryCount : ℤ) =
        (C₂.normalizedNoCarryCount : ℤ) := by
    rw [hDelta, hSum] at h₁
    nlinarith [h₁, h₂]
  exact_mod_cast hCountCast

/-- `sum D` の mod `G` class は endpoint normalized delta に一致する。 -/
theorem terminalGap_dvd_cellResidueSum_sub_normalizedDelta
    {start finish : ParityWord}
    (C : FerrersChain start finish)
    (hStartFP : IsFirstPassageWord start) :
    (wordTerminalGap start : ℤ) ∣
      C.normalizedCellResidueSum - C.normalizedDelta := by
  have h :=
    C.normalizedDelta_eq_cellResidueSum_sub_gap_mul_noCarryCount hStartFP
  refine ⟨(C.normalizedNoCarryCount : ℤ), ?_⟩
  linarith

/-- 同じ endpoints の二 chain の cell sums は当然 mod `G` でも一致する。 -/
theorem terminalGap_dvd_cellResidueSum_sub_cellResidueSum
    {start finish : ParityWord}
    (C₁ C₂ : FerrersChain start finish)
    (_hStartFP : IsFirstPassageWord start) :
    (wordTerminalGap start : ℤ) ∣
      C₁.normalizedCellResidueSum - C₂.normalizedCellResidueSum := by
  rw [C₁.normalizedCellResidueSum_chain_independent C₂]
  simp

end FerrersChain

end CSTMicro
end Collatz2
