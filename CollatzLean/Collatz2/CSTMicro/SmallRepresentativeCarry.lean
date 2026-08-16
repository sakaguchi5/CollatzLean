import CollatzLean.Collatz2.CSTMicro.ResidueCarry

/-!
# General CST: polynomially-small representative carry corridor

`PolynomialCapacity` と `ResidueCarry` を接続する。

CST failure なら

  R(P) <= Cap(P) <= K (length(P)+1)^(A+1)

なので representative は polynomially small。

さらに adjacent Ferrers edge が carry なら

  lowerR + deltaR = modulus + upperR

だから、upper が CST failure であるためには

  modulus <= lowerR + deltaR
          <= modulus + K(length+1)^(A+1)

という狭い carry corridor に入らなければならない。

もし polynomial width < 2^position なら、carry alignment は
幅 `2^position` 未満の dyadic corridor にさらに圧縮される。
-/

namespace Collatz2
namespace CSTMicro

namespace MicroObject

/--
CST failure なら least representative は capacity 以下、したがって
既存 polynomial capacity majorant 以下。
-/
theorem R_le_simpleLengthPolynomial_of_cst_failure
    (M : MicroObject)
    {K A : ℕ}
    (hGap :
      ∀ p H : ℕ,
        0 < p →
        3 ^ p < 2 ^ H →
        3 ^ p ≤
          K * (p + 1) ^ A * (2 ^ H - 3 ^ p))
    (hFail : ¬ M.CSTHolds) :
    M.R ≤ K * (M.path.length + 1) ^ (A + 1) := by
  have hRCap : M.R ≤ M.Cap := by
    by_contra hnot
    have hgt : M.R > M.Cap := by
      omega
    exact hFail ((M.cstHolds_iff_R_gt_Cap).2 hgt)
  rw [M.Cap_eq_path_capacity] at hRCap
  have hCap :=
    M.path.capacity_le_simpleLengthPolynomial_of_gap_witness hGap
  exact le_trans hRCap hCap

/--
外部 polynomial gap interface だけから、CST failure representative に
共通の polynomial bound の存在を得る。
-/
theorem exists_polynomial_R_bound_of_cst_failure
    (M : MicroObject)
    (hGap : External.TwoThreeGapPolynomialBound)
    (hFail : ¬ M.CSTHolds) :
    ∃ K D : ℕ,
      0 < K ∧ 0 < D ∧
      M.R ≤ K * (M.path.length + 1) ^ D := by
  rcases hGap with ⟨K, A, hK, hWitness⟩
  refine ⟨K, A + 1, hK, by omega, ?_⟩
  exact M.R_le_simpleLengthPolynomial_of_cst_failure hWitness hFail

end MicroObject

namespace AdjacentFerrersSwap
namespace MicroSwap

/-- upper micro object の length は edge common length。 -/
theorem upper_length_eq_edge_length (S : MicroSwap) :
    S.upper.path.length = S.edge.length := by
  unfold FirstPassagePath.length
  rw [S.upper_word]
  exact S.edge.upperWord_length

/-- lower micro object の length も edge common length。 -/
theorem lower_length_eq_edge_length (S : MicroSwap) :
    S.lower.path.length = S.edge.length := by
  unfold FirstPassagePath.length
  rw [S.lower_word]
  exact S.edge.lowerWord_length

/-- upper CST failure なら edge の upper representative は polynomially small。 -/
theorem upperR_le_polynomial_of_cst_failure
    (S : MicroSwap)
    {K A : ℕ}
    (hGap :
      ∀ p H : ℕ,
        0 < p →
        3 ^ p < 2 ^ H →
        3 ^ p ≤
          K * (p + 1) ^ A * (2 ^ H - 3 ^ p))
    (hFail : ¬ S.upper.CSTHolds) :
    S.edge.upperR ≤ K * (S.edge.length + 1) ^ (A + 1) := by
  have h :=
    S.upper.R_le_simpleLengthPolynomial_of_cst_failure hGap hFail
  rw [S.upper_R_eq] at h
  rw [S.upper_length_eq_edge_length] at h
  exact h

/--
carry + upper CST failure は polynomial-width carry corridor に入る。
-/
theorem polynomial_carry_corridor_of_upper_cst_failure
    (S : MicroSwap)
    {K A : ℕ}
    (hGap :
      ∀ p H : ℕ,
        0 < p →
        3 ^ p < 2 ^ H →
        3 ^ p ≤
          K * (p + 1) ^ A * (2 ^ H - 3 ^ p))
    (hCarry : S.edge.HasCarry)
    (hFail : ¬ S.upper.CSTHolds) :
    S.edge.modulus ≤ S.edge.lowerR + S.edge.deltaR ∧
      S.edge.lowerR + S.edge.deltaR ≤
        S.edge.modulus + K * (S.edge.length + 1) ^ (A + 1) := by
  have hR := S.upperR_le_polynomial_of_cst_failure hGap hFail
  have hsum :=
    S.edge.lowerR_add_deltaR_eq_modulus_add_upperR_of_hasCarry hCarry
  constructor
  · exact hCarry
  · calc
      S.edge.lowerR + S.edge.deltaR
          = S.edge.modulus + S.edge.upperR := hsum
      _ ≤
          S.edge.modulus + K * (S.edge.length + 1) ^ (A + 1) :=
        Nat.add_le_add_left hR S.edge.modulus

/--
高い swap position で polynomial width が `2^position` 未満なら、
carry sum は modulus の直上の dyadic corridor に入る。
-/
theorem high_position_carry_corridor_of_upper_cst_failure
    (S : MicroSwap)
    {K A : ℕ}
    (hGap :
      ∀ p H : ℕ,
        0 < p →
        3 ^ p < 2 ^ H →
        3 ^ p ≤
          K * (p + 1) ^ A * (2 ^ H - 3 ^ p))
    (hCarry : S.edge.HasCarry)
    (hFail : ¬ S.upper.CSTHolds)
    (hHigh :
      K * (S.edge.length + 1) ^ (A + 1) <
        2 ^ S.edge.position) :
    S.edge.modulus ≤ S.edge.lowerR + S.edge.deltaR ∧
      S.edge.lowerR + S.edge.deltaR <
        S.edge.modulus + 2 ^ S.edge.position := by
  have hCorr :=
    S.polynomial_carry_corridor_of_upper_cst_failure
      hGap hCarry hFail
  constructor
  · exact hCorr.1
  · exact lt_of_le_of_lt hCorr.2 (Nat.add_lt_add_left hHigh _)

/--
同じ high-position 仮定の下では carry 後 representative 自身も
`2^position` 未満になる。
-/
theorem upperR_lt_twoPow_position_of_upper_cst_failure
    (S : MicroSwap)
    {K A : ℕ}
    (hGap :
      ∀ p H : ℕ,
        0 < p →
        3 ^ p < 2 ^ H →
        3 ^ p ≤
          K * (p + 1) ^ A * (2 ^ H - 3 ^ p))
    (hFail : ¬ S.upper.CSTHolds)
    (hHigh :
      K * (S.edge.length + 1) ^ (A + 1) <
        2 ^ S.edge.position) :
    S.edge.upperR < 2 ^ S.edge.position := by
  have hR := S.upperR_le_polynomial_of_cst_failure hGap hFail
  exact lt_of_le_of_lt hR hHigh

/--
`lower` が safe で `upper` が failure なら carry は自動であり、
その carry は polynomial corridor に入る。
-/
theorem polynomial_carry_corridor_of_first_failure
    (S : MicroSwap)
    {K A : ℕ}
    (hGap :
      ∀ p H : ℕ,
        0 < p →
        3 ^ p < 2 ^ H →
        3 ^ p ≤
          K * (p + 1) ^ A * (2 ^ H - 3 ^ p))
    (hLower : S.lower.CSTHolds)
    (hUpper : ¬ S.upper.CSTHolds) :
    S.edge.HasCarry ∧
      S.edge.modulus ≤ S.edge.lowerR + S.edge.deltaR ∧
      S.edge.lowerR + S.edge.deltaR ≤
        S.edge.modulus + K * (S.edge.length + 1) ^ (A + 1) := by
  have hCarry :=
    S.hasCarry_of_lower_cstHolds_of_upper_failure hLower hUpper
  have hCorr :=
    S.polynomial_carry_corridor_of_upper_cst_failure
      hGap hCarry hUpper
  exact ⟨hCarry, hCorr.1, hCorr.2⟩

end MicroSwap
end AdjacentFerrersSwap
end CSTMicro
end Collatz2
