import CollatzLean.Collatz2.Geometry.ResidueIndexedFerrers

/-!
# Collatz2 Geometry: residue-indexed Ferrers cell sum

primitive FirstCrossing の cut-indexed Ferrers cell sum を、rank residue permutation の
inverse selector `residueCut` で完全に residue-indexed profile へ移す。

  q_r = rankQuotient(residueCut(r))

とすると

  ferrersCellSum
    = finite sum over r<p of
        v^r * (1 + half + ... + half^(q_r-1)).

さらに `half=v^p` を使えば各 cell は `v^(r+p*j)` となるので、
Ferrers diagram の generating sum そのものとして読める。
-/

namespace Collatz2
namespace Word

/-- `k=0` も含め、proper range 全体で quotient profile は cut quotient を復元する。 -/
theorem residueRankQuotientProfile_rankResidue_eq_of_lt
    {w : Word}
    (hF : FirstCrossing w)
    (hcop : Nat.Coprime (twoSteps w) (oddSteps w))
    {k : ℕ}
    (hkLt : k < oddSteps w) :
    residueRankQuotientProfile hF hcop (rankResidue w k) =
      rankQuotient w k := by
  by_cases hk0 : k = 0
  · subst k
    simp
  · exact
      residueRankQuotientProfile_rankResidue_eq
        hF hcop (Nat.pos_of_ne_zero hk0) hkLt

/-- residue `r` の Ferrers cell column contribution。 -/
noncomputable def residueIndexedFerrersCellColumn
    {w : Word}
    (R : RankUnitData w)
    (hF : FirstCrossing w)
    (hcop : Nat.Coprime (twoSteps w) (oddSteps w))
    (r : ℕ) : ZMod (terminalGap w) :=
  inverseUnitValue R ^ r *
    halfCellColumnSum R (residueRankQuotientProfile hF hcop r)

/-- residue-indexed quotient profile だけで書いた全 Ferrers cell sum。 -/
noncomputable def residueIndexedFerrersCellSum
    {w : Word}
    (R : RankUnitData w)
    (hF : FirstCrossing w)
    (hcop : Nat.Coprime (twoSteps w) (oddSteps w)) :
    ZMod (terminalGap w) :=
  Finset.sum (Finset.range (oddSteps w))
    (fun r => residueIndexedFerrersCellColumn R hF hcop r)

/--
cut-indexed Ferrers cell sum は exact に residue-indexed cell sum と一致する。
-/
theorem RankUnitData.ferrersCellSum_eq_residueIndexedFerrersCellSum
    {w : Word}
    (R : RankUnitData w)
    (hF : FirstCrossing w)
    (hcop : Nat.Coprime (twoSteps w) (oddSteps w)) :
    ferrersCellSum R = residueIndexedFerrersCellSum R hF hcop := by
  unfold ferrersCellSum residueIndexedFerrersCellSum
  simp only [baseResidueWeight_eq_inverseUnitValue_pow]
  have hImage := hF.image_rankResidue_range_eq_range hcop
  calc
    Finset.sum (Finset.range (oddSteps w))
        (fun k =>
          inverseUnitValue R ^ rankResidue w k *
            halfCellColumnSum R (rankQuotient w k))
        = Finset.sum (Finset.range (oddSteps w))
            (fun k =>
              residueIndexedFerrersCellColumn
                R hF hcop (rankResidue w k)) := by
              apply Finset.sum_congr rfl
              intro k hk
              unfold residueIndexedFerrersCellColumn
              rw [residueRankQuotientProfile_rankResidue_eq_of_lt
                    hF hcop (Finset.mem_range.mp hk)]
    _ = Finset.sum
          ((Finset.range (oddSteps w)).image (rankResidue w))
          (fun r => residueIndexedFerrersCellColumn R hF hcop r) := by
            symm
            apply Finset.sum_image
            intro k hk l hl hEq
            exact hF.rankResidue_injective_on_range_of_coprime
              hcop
              (Finset.mem_range.mp hk)
              (Finset.mem_range.mp hl)
              hEq
    _ = Finset.sum (Finset.range (oddSteps w))
          (fun r => residueIndexedFerrersCellColumn R hF hcop r) := by
            rw [hImage]

/--
各 Ferrers cell `(r,j)` を直接 `v^(r+p*j)` として足した generating sum。
-/
noncomputable def residueIndexedFerrersPowerCellSum
    {w : Word}
    (R : RankUnitData w)
    (hF : FirstCrossing w)
    (hcop : Nat.Coprime (twoSteps w) (oddSteps w)) :
    ZMod (terminalGap w) :=
  Finset.sum (Finset.range (oddSteps w))
    (fun r =>
      Finset.sum
        (Finset.range (residueRankQuotientProfile hF hcop r))
        (fun j => inverseUnitValue R ^ (r + oddSteps w * j)))

/-- residue-indexed column formは cell generating sum と exact に一致する。 -/
theorem RankUnitData.residueIndexedFerrersCellSum_eq_powerCellSum
    {w : Word}
    (R : RankUnitData w)
    (hF : FirstCrossing w)
    (hcop : Nat.Coprime (twoSteps w) (oddSteps w)) :
    residueIndexedFerrersCellSum R hF hcop =
      residueIndexedFerrersPowerCellSum R hF hcop := by
  unfold residueIndexedFerrersCellSum residueIndexedFerrersCellColumn
  unfold residueIndexedFerrersPowerCellSum halfCellColumnSum
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [halfUnitValue_eq_inverseUnitValue_pow]
  rw [← pow_mul, ← pow_add]

/-- original Ferrers sum を path/cut-free cell generating sum まで一気に移す。 -/
theorem RankUnitData.ferrersCellSum_eq_residueIndexedFerrersPowerCellSum
    {w : Word}
    (R : RankUnitData w)
    (hF : FirstCrossing w)
    (hcop : Nat.Coprime (twoSteps w) (oddSteps w)) :
    ferrersCellSum R = residueIndexedFerrersPowerCellSum R hF hcop := by
  calc
    ferrersCellSum R = residueIndexedFerrersCellSum R hF hcop :=
      R.ferrersCellSum_eq_residueIndexedFerrersCellSum hF hcop
    _ = residueIndexedFerrersPowerCellSum R hF hcop :=
      R.residueIndexedFerrersCellSum_eq_powerCellSum hF hcop

end Word
end Collatz2
