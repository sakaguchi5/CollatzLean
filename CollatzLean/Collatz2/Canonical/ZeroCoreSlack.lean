import CollatzLean.Collatz2.Canonical.PositiveSuffixBudget

/-!
# Collatz2 Canonical: true zero-core の fundamental slack coordinates

true `j=0` prepend-one core から最終的に得る座標

  canonicalStart(1::v) + 1 = 4*(n+d)
  canonicalStart(v)    + 1 = 6*(n+d)
  canonicalEnd(v)      + 1 = 6*n + 4*d

を、このファイルでは前提として受け取る。

ここでは 1--5 の branch extraction 自体を再実装せず、
そこから独立に従う canonical fundamental-interval arithmetic だけを保持する。

`A = 2^K`, `C = 3^m` とすると start/end dual bounds から

  A = 3*(n+d) + a
  C = 3*n + 2*d + c

となる自然数 slack `a,c` が存在する。
さらに whole `1::v` と tail `v` が contracting なら

  G + 3*c + 3*n = 2*a
  g + c = d + a

が exact に成立する。
従って whole gap `G>0` から

  3*c + 3*n < 2*a

が直ちに従う。
-/

namespace Collatz2
namespace Word

/--
true zero-core で必要になる coordinate equalities だけを薄く保持する。
branch-specific replay data は持たない。
-/
structure ZeroCoreCoordinates (v : Word) (n d : ℕ) : Prop where
  tailValid : Valid v
  fullStart_add_one :
    canonicalStart (1 :: v) + 1 = 4 * (n + d)
  tailStart_add_one :
    canonicalStart v + 1 = 6 * (n + d)
  tailEnd_add_one :
    canonicalEnd v + 1 = 6 * n + 4 * d

namespace ZeroCoreCoordinates

/-- start/end fundamental intervals から slack `a,c` を同時に抽出する。 -/
theorem exists_fundamentalSlacks
    {v : Word} {n d : ℕ}
    (Z : ZeroCoreCoordinates v n d) :
    ∃ a c : ℕ,
      2 ^ twoSteps v = 3 * (n + d) + a ∧
      3 ^ oddSteps v = 3 * n + 2 * d + c := by
  have hStartBound := canonicalStart_lt_modulus v
  have hStartBound' :
      canonicalStart v < 2 * 2 ^ twoSteps v := by
    simpa [residueModulus, pow_succ, Nat.mul_comm] using hStartBound
  have hEndBound :
      canonicalEnd v < 2 * 3 ^ oddSteps v :=
    canonicalEnd_lt_two_mul_threePow Z.tailValid
  have hTailStart :
      canonicalStart v + 1 = 6 * (n + d) :=
    Z.tailStart_add_one
  have hTailEnd :
      canonicalEnd v + 1 = 6 * n + 4 * d :=
    Z.tailEnd_add_one
  have hA : 3 * (n + d) ≤ 2 ^ twoSteps v := by
    omega
  have hC : 3 * n + 2 * d ≤ 3 ^ oddSteps v := by
    omega
  let a := 2 ^ twoSteps v - 3 * (n + d)
  let c := 3 ^ oddSteps v - (3 * n + 2 * d)
  have ha : 2 ^ twoSteps v = 3 * (n + d) + a := by
    dsimp [a]
    omega
  have hc : 3 ^ oddSteps v = 3 * n + 2 * d + c := by
    dsimp [c]
    omega
  exact ⟨a, c, ha, hc⟩

/--
whole `1::v` と tail `v` の contracting gap を slack coordinates で exact に書く。
-/
theorem exists_fundamentalSlacks_with_gapBalances
    {v : Word} {n d : ℕ}
    (Z : ZeroCoreCoordinates v n d)
    (hFull : Contracting (1 :: v))
    (hTail : Contracting v) :
    ∃ a c : ℕ,
      2 ^ twoSteps v = 3 * (n + d) + a ∧
      3 ^ oddSteps v = 3 * n + 2 * d + c ∧
      (AffineTransfer.ofWord (1 :: v)).centerGap + 3 * c + 3 * n = 2 * a ∧
      (AffineTransfer.ofWord v).centerGap + c = d + a := by
  obtain ⟨a, c, hA, hC⟩ := Z.exists_fundamentalSlacks
  have hFullNeg :
      (AffineTransfer.ofWord (1 :: v)).determinant < 0 := hFull
  have hFullLe :
      (AffineTransfer.ofWord (1 :: v)).oddCoeff ≤
        (AffineTransfer.ofWord (1 :: v)).twoCoeff := by
    unfold AffineTransfer.determinant at hFullNeg
    omega
  have hFullGapCoeff :
      (AffineTransfer.ofWord (1 :: v)).centerGap +
          (AffineTransfer.ofWord (1 :: v)).oddCoeff =
        (AffineTransfer.ofWord (1 :: v)).twoCoeff := by
    unfold AffineTransfer.centerGap
    exact Nat.sub_add_cancel hFullLe
  have hFullGap0 :
      (AffineTransfer.ofWord (1 :: v)).centerGap +
          3 ^ (oddSteps v + 1) =
        2 ^ (1 + twoSteps v) := by
    simpa [oddSteps, twoSteps] using hFullGapCoeff
  have hFullGap :
      (AffineTransfer.ofWord (1 :: v)).centerGap +
          3 * 3 ^ oddSteps v =
        2 * 2 ^ twoSteps v := by
    calc
      (AffineTransfer.ofWord (1 :: v)).centerGap +
          3 * 3 ^ oddSteps v
          =
        (AffineTransfer.ofWord (1 :: v)).centerGap +
          3 ^ (oddSteps v + 1) := by
            rw [pow_succ]
            ring
      _ = 2 ^ (1 + twoSteps v) := hFullGap0
      _ = 2 * 2 ^ twoSteps v := by
            simp [pow_add]
  have hTailNeg :
      (AffineTransfer.ofWord v).determinant < 0 := hTail
  have hTailLe :
      (AffineTransfer.ofWord v).oddCoeff ≤
        (AffineTransfer.ofWord v).twoCoeff := by
    unfold AffineTransfer.determinant at hTailNeg
    omega
  have hTailGapCoeff :
      (AffineTransfer.ofWord v).centerGap +
          (AffineTransfer.ofWord v).oddCoeff =
        (AffineTransfer.ofWord v).twoCoeff := by
    unfold AffineTransfer.centerGap
    exact Nat.sub_add_cancel hTailLe
  have hTailGap :
      (AffineTransfer.ofWord v).centerGap + 3 ^ oddSteps v =
        2 ^ twoSteps v := by
    simpa using hTailGapCoeff
  have hWholeBalance :
      (AffineTransfer.ofWord (1 :: v)).centerGap +
          3 * c + 3 * n = 2 * a := by
    rw [hA, hC] at hFullGap
    nlinarith
  have hTailBalance :
      (AffineTransfer.ofWord v).centerGap + c = d + a := by
    rw [hA, hC] at hTailGap
    nlinarith
  exact ⟨a, c, hA, hC, hWholeBalance, hTailBalance⟩

/-- whole gap positivity を slack inequality `3*c+3*n < 2*a` に翻訳する。 -/
theorem exists_fundamentalSlacks_with_strictInequality
    {v : Word} {n d : ℕ}
    (Z : ZeroCoreCoordinates v n d)
    (hFull : Contracting (1 :: v))
    (hTail : Contracting v) :
    ∃ a c : ℕ,
      2 ^ twoSteps v = 3 * (n + d) + a ∧
      3 ^ oddSteps v = 3 * n + 2 * d + c ∧
      3 * c + 3 * n < 2 * a ∧
      (AffineTransfer.ofWord v).centerGap + c = d + a := by
  obtain ⟨a, c, hA, hC, hWhole, hTailBal⟩ :=
    Z.exists_fundamentalSlacks_with_gapBalances hFull hTail
  have hGpos : 0 < (AffineTransfer.ofWord (1 :: v)).centerGap :=
    AffineTransfer.centerGap_pos_of_negative hFull
  have hstrict : 3 * c + 3 * n < 2 * a := by omega
  exact ⟨a, c, hA, hC, hstrict, hTailBal⟩

/--
true zero-core で通常得られる `AllSuffixesContracting (1::v)` から
whole/tail contracting を自動で回収した版。
-/
theorem exists_fundamentalSlacks_of_allSuffixesContracting
    {v : Word} {n d : ℕ}
    (Z : ZeroCoreCoordinates v n d)
    (hvne : v ≠ [])
    (hAll : AllSuffixesContracting (1 :: v)) :
    ∃ a c : ℕ,
      2 ^ twoSteps v = 3 * (n + d) + a ∧
      3 ^ oddSteps v = 3 * n + 2 * d + c ∧
      3 * c + 3 * n < 2 * a ∧
      (AffineTransfer.ofWord v).centerGap + c = d + a := by
  have hFull : Contracting (1 :: v) :=
    hAll.whole_contracting (by simp)
  have hTailAll : AllSuffixesContracting v := by
    exact AllSuffixesNegativeDeterminant.tail hAll
  have hTail : Contracting v :=
    hTailAll.whole_contracting hvne
  exact Z.exists_fundamentalSlacks_with_strictInequality hFull hTail

end ZeroCoreCoordinates
end Word
end Collatz2
