import CollatzLean.Collatz3.CSTCarry.FerrersAffineResidueBridge
import CollatzLean.Collatz3.CSTCarry.CarryLiftQuotient
import CollatzLean.Collatz3.CSTCarry.FinalWrapLowerBound

/-!
# Collatz3 CSTCarry: Ferrers residue program の proved frontier

このファイルは未証明主張を theorem として追加しない。
前段で証明した exact identities を一つに束ね、任意幅の final-wrap 排除に
本当に残っている条件だけを predicate として名前付けする。

重要な区別:

* `ferrersBinaryShift` / affine start displacement は `mod 2^H` の情報。
* final carry boundedness は quotient lift `q = F / 2^H` の情報。

従って start residue が canonical range 内でどう wrap するかだけでは `q=0` は決まらない。
残る核心は admissible/critical Ferrers geometry から、この quotient bit が `0` に
強制されることを証明すること。
-/

namespace Collatz3
namespace CSTCarry

/--
critical rows 上で final carry の lift quotient が 0 になる、という任意幅の研究目標。
`CarryBelowModulus` の quotient-normal form。
-/
def CriticalLiftZero
    (P : ℕ)
    (rows : List FerrersRow)
    (digits : List ℕ)
    (F : ℕ) : Prop :=
  ∀ _h : CarryRealizes (2 ^ Critical.criticalTwoDepth P) rows 0 digits F,
    CriticalCarryRows P rows →
      carryLiftQuotient (Critical.criticalTwoDepth P) F = 0

/-- `CriticalLiftZero` があれば final carry boundedness は直ちに得られる。 -/
theorem final_lt_modulus_of_criticalLiftZero
    {P : ℕ}
    {rows : List FerrersRow}
    {digits : List ℕ}
    {F : ℕ}
    (hLift : CriticalLiftZero P rows digits F)
    (h : CarryRealizes (2 ^ Critical.criticalTwoDepth P) rows 0 digits F)
    (hRows : CriticalCarryRows P rows) :
    F < 2 ^ Critical.criticalTwoDepth P := by
  have hZero := hLift h hRows
  exact (carryLiftQuotient_eq_zero_iff_lt_modulus
    (Critical.criticalTwoDepth P) F).1 hZero

/--
final carry の full integer lift を affine start displacement の代表値で書く。
residue 部分と quotient 部分がここで一つの exact equality に合流する。
-/
theorem CarryRealizes.final_eq_affineStartDisplacementVal_add_modulus_mul_liftQuotient
    {H : ℕ}
    {rows : List FerrersRow}
    {digits : List ℕ}
    {F : ℕ}
    (h : CarryRealizes (2 ^ H) rows 0 digits F) :
    F =
      (affineStartClassModTwoPow rows.length H (ferrersActualAffine rows) -
        affineStartClassModTwoPow rows.length H (ferrersBoundaryAffine rows)).val +
      2 ^ H * carryLiftQuotient H F := by
  rw [← ferrersBinaryShift_eq_affineStartDisplacement_val]
  exact h.final_eq_ferrersBinaryShift_add_modulus_mul_liftQuotient

/--
critical rows では quotient は既に 0/1 の二値。
従って任意幅問題は `1` branch を排除するだけでよい。
-/
theorem criticalLiftQuotient_eq_zero_or_one
    {P : ℕ}
    {rows : List FerrersRow}
    {digits : List ℕ}
    {F : ℕ}
    (h : CarryRealizes (2 ^ Critical.criticalTwoDepth P) rows 0 digits F)
    (hRows : CriticalCarryRows P rows) :
    carryLiftQuotient (Critical.criticalTwoDepth P) F = 0 ∨
      carryLiftQuotient (Critical.criticalTwoDepth P) F = 1 := by
  exact h.liftQuotient_eq_zero_or_one_of_insideBitWidth hRows.insideBitWidth

/--
critical rows で quotient=1 なら final carry は
`2^H + ferrersBinaryShift` の exact one-lift form。
-/
theorem criticalFinal_eq_modulus_add_shift_of_liftOne
    {P : ℕ}
    {rows : List FerrersRow}
    {digits : List ℕ}
    {F : ℕ}
    (h : CarryRealizes (2 ^ Critical.criticalTwoDepth P) rows 0 digits F)
    (hRows : CriticalCarryRows P rows)
    (hOne : carryLiftQuotient (Critical.criticalTwoDepth P) F = 1) :
    F = 2 ^ Critical.criticalTwoDepth P +
      ferrersBinaryShift (Critical.criticalTwoDepth P) rows := by
  have hWrap : 2 ^ Critical.criticalTwoDepth P ≤ F :=
    (h.final_wrap_iff_liftQuotient_eq_one_of_insideBitWidth
      hRows.insideBitWidth).2 hOne
  exact h.final_eq_modulus_add_ferrersBinaryShift_of_wrap
    hRows.insideBitWidth hWrap

/--
critical `q=1` branch の residue shift は正の 4 の倍数。
`F-M` と `ferrersBinaryShift` が同じであることを使う。
-/
theorem criticalLiftOne_shift_pos_and_four_dvd
    {P : ℕ}
    {rows : List FerrersRow}
    {digits : List ℕ}
    {F : ℕ}
    (h : CarryRealizes (2 ^ Critical.criticalTwoDepth P) rows 0 digits F)
    (hRows : CriticalCarryRows P rows)
    (hP : 0 < P)
    (hOne : carryLiftQuotient (Critical.criticalTwoDepth P) F = 1) :
    0 < ferrersBinaryShift (Critical.criticalTwoDepth P) rows ∧
      4 ∣ ferrersBinaryShift (Critical.criticalTwoDepth P) rows := by
  have hWrap : 2 ^ Critical.criticalTwoDepth P ≤ F :=
    (h.final_wrap_iff_liftQuotient_eq_one_of_insideBitWidth
      hRows.insideBitWidth).2 hOne
  have hOver :=
    h.finalWrap_overhang_pos_and_four_dvd_of_criticalRows hRows hP hWrap
  have hShift :=
    h.finalOverhang_eq_ferrersBinaryShift hRows.insideBitWidth hWrap
  rw [hShift] at hOver
  exact hOver

/-- critical `q=1` branch では shift は少なくとも 4。 -/
theorem four_le_criticalLiftOne_shift
    {P : ℕ}
    {rows : List FerrersRow}
    {digits : List ℕ}
    {F : ℕ}
    (h : CarryRealizes (2 ^ Critical.criticalTwoDepth P) rows 0 digits F)
    (hRows : CriticalCarryRows P rows)
    (hP : 0 < P)
    (hOne : carryLiftQuotient (Critical.criticalTwoDepth P) F = 1) :
    4 ≤ ferrersBinaryShift (Critical.criticalTwoDepth P) rows := by
  have hData := criticalLiftOne_shift_pos_and_four_dvd h hRows hP hOne
  exact Nat.le_of_dvd hData.1 hData.2

/--
critical `q=1` branch の global defect identity を binary shift だけで書いた形。

`S = M(D+1) + 3^P * shift`。
-/
theorem criticalLiftOne_defect_eq_complement_add_shift
    {P : ℕ}
    {rows : List FerrersRow}
    {digits : List ℕ}
    {F : ℕ}
    (h : CarryRealizes (2 ^ Critical.criticalTwoDepth P) rows 0 digits F)
    (hRows : CriticalCarryRows P rows)
    (hOne : carryLiftQuotient (Critical.criticalTwoDepth P) F = 1) :
    ferrersWeightedDefect rows =
      2 ^ Critical.criticalTwoDepth P *
          (ternaryComplementValue digits + 1) +
        3 ^ P * ferrersBinaryShift (Critical.criticalTwoDepth P) rows := by
  have hWrap : 2 ^ Critical.criticalTwoDepth P ≤ F :=
    (h.final_wrap_iff_liftQuotient_eq_one_of_insideBitWidth
      hRows.insideBitWidth).2 hOne
  have hEq := h.finalDefect_eq_complement_add_overhang hWrap
  have hShift :=
    h.finalOverhang_eq_ferrersBinaryShift hRows.insideBitWidth hWrap
  rw [hRows.length_eq, hShift] at hEq
  exact hEq

/--
critical rows で quotient=1 なら weighted defect は complement budget を越える。
既存 final-wrap identity を quotient 語彙へ書き直した frontier theorem。
-/
theorem not_complementBudget_of_criticalLiftOne
    {P : ℕ}
    {rows : List FerrersRow}
    {digits : List ℕ}
    {F : ℕ}
    (h : CarryRealizes (2 ^ Critical.criticalTwoDepth P) rows 0 digits F)
    (_hRows : CriticalCarryRows P rows)
    (hOne : carryLiftQuotient (Critical.criticalTwoDepth P) F = 1) :
    ¬ ComplementBudget
      (2 ^ Critical.criticalTwoDepth P) rows digits := by
  intro hBudget
  have hZero : carryLiftQuotient (Critical.criticalTwoDepth P) F = 0 :=
    (h.liftQuotient_eq_zero_iff_complementBudget).2 hBudget
  omega

/--
任意幅の中心 frontier を complement budget の形にも戻せる。
`CriticalLiftZero` を証明することと、各 realization の complement budget を証明することは同じ目標。
-/
theorem criticalLiftZero_iff_all_complementBudget
    {P : ℕ}
    {rows : List FerrersRow}
    {digits : List ℕ}
    {F : ℕ} :
    CriticalLiftZero P rows digits F ↔
      ∀ _h : CarryRealizes (2 ^ Critical.criticalTwoDepth P) rows 0 digits F,
        CriticalCarryRows P rows →
          ComplementBudget
            (2 ^ Critical.criticalTwoDepth P) rows digits := by
  constructor
  · intro hLift h hRows
    have hZero := hLift h hRows
    exact (h.liftQuotient_eq_zero_iff_complementBudget).1 hZero
  · intro hBudget h hRows
    exact (h.liftQuotient_eq_zero_iff_complementBudget).2
      (hBudget h hRows)

end CSTCarry
end Collatz3
