import CollatzLean.Collatz2.CSTMicro.FirstFailureExtraction

/-!
# General CST: global failure -> local polynomial carry corridor

first failure edge は carry を持つ。
さらに upper word が separation failure なら
polynomial 2-3 gap と first-passage affine bound から
upper representative は polynomially small。

したがって global CST failure は、一つの adjacent Ferrers edge 上の

  2^k <= R_lower + delta
      <= 2^k + K (k+1)^(A+1)

という local carry corridor に圧縮される。
-/

namespace Collatz2
namespace CSTMicro

namespace FirstFailureEdge

private theorem natPow_le_natPow_of_le_local
    {a b : ℕ} (hab : a ≤ b) :
    ∀ n : ℕ, a ^ n ≤ b ^ n
  | 0 => by simp
  | n + 1 => by
      rw [pow_succ, pow_succ]
      exact Nat.mul_le_mul (natPow_le_natPow_of_le_local hab n) hab

/-- first failure edge の upper word を `FirstPassagePath` に戻す。 -/
def upperPath (F : FirstFailureEdge) : FirstPassagePath :=
  firstPassagePathOfWord F.upper F.upper_firstPassage

@[simp] theorem upperPath_word (F : FirstFailureEdge) :
    F.upperPath.word = F.upper := rfl

/-- edge length と upper path length は一致。 -/
theorem upperPath_length_eq_edge_length (F : FirstFailureEdge) :
    F.upperPath.length = F.step.edge.length := by
  change F.upper.length = F.step.edge.length
  calc
    F.upper.length = F.step.edge.upperWord.length :=
      congrArg List.length F.step.upper_eq
    _ = F.step.edge.length :=
      F.step.edge.upperWord_length

/-- edge upperR と upper word の least representative は一致。 -/
theorem edge_upperR_eq (F : FirstFailureEdge) :
    F.step.edge.upperR = leastRepresentative F.upper := by
  unfold AdjacentFerrersSwap.upperR
  rw [← F.step.upper_eq]

/--
正の gap について

  gap * representative ≤ x ≤ bound * gap

なら representative ≤ bound。
-/
private theorem representative_le_of_gap_sandwich
    {gap representative bound x : ℕ}
    (hGapPos : 0 < gap)
    (hLower : gap * representative ≤ x)
    (hUpper : x ≤ bound * gap) :
    representative ≤ bound := by
  by_contra hnot
  have hlt : bound < representative := by
    omega
  have hmul :
      bound * gap < representative * gap :=
    (Nat.mul_lt_mul_right hGapPos).2 hlt
  have hLower' :
      representative * gap ≤ x := by
    simpa [Nat.mul_comm] using hLower
  omega


/--
first-passage path が pure separation に失敗しており、
contracting gap に polynomial witness があれば、
least representative は endpoint odd count の polynomial で抑えられる。
-/
theorem representative_le_endpointPolynomial_of_failure
    (P : FirstPassagePath)
    {K A : ℕ}
    (hFailure : ¬ WordPureSeparation P.word)
    (hGap :
      ∀ p H : ℕ,
        0 < p →
        3 ^ p < 2 ^ H →
        3 ^ p ≤
          K * (p + 1) ^ A * (2 ^ H - 3 ^ p)) :
    leastRepresentative P.word ≤
      P.endpointOddCount * K *
        (P.endpointOddCount + 1) ^ A := by
  have hB :=
    P.affineConst_le_endpointOddCount_mul_threePow
  have hFail :
      ¬ affineConst P.word <
        P.terminalGap * leastRepresentative P.word := by
    simpa [
      WordPureSeparation,
      wordTerminalGap,
      FirstPassagePath.terminalGap,
      FirstPassagePath.length,
      FirstPassagePath.endpointOddCount
    ] using hFailure
  have hGR :
      P.terminalGap * leastRepresentative P.word ≤
        affineConst P.word := by
    omega
  by_cases hm0 : P.endpointOddCount = 0
  · have hB0 : affineConst P.word = 0 := by
      apply Nat.eq_zero_of_le_zero
      simpa [hm0] using hB
    have hR0 : leastRepresentative P.word = 0 := by
      have hGapPos := P.terminalGap_pos
      rw [hB0] at hGR
      by_contra hne
      have hRPos :
          0 < leastRepresentative P.word :=
        Nat.pos_of_ne_zero hne
      have hProdPos :
          0 <
            P.terminalGap *
              leastRepresentative P.word :=
        Nat.mul_pos hGapPos hRPos
      omega
    rw [hR0]
    exact Nat.zero_le _
  · have hmPos : 0 < P.endpointOddCount :=
      Nat.pos_of_ne_zero hm0
    have hGapP :
        3 ^ P.endpointOddCount ≤
          K * (P.endpointOddCount + 1) ^ A *
            P.terminalGap := by
      have h :=
        hGap
          P.endpointOddCount
          P.length
          hmPos
          P.terminal_contracting
      simpa [
        FirstPassagePath.terminalGap,
        FirstPassagePath.length,
        FirstPassagePath.endpointOddCount
      ] using h
    have hNumerator :
        affineConst P.word ≤
          (P.endpointOddCount * K *
            (P.endpointOddCount + 1) ^ A) *
              P.terminalGap := by
      calc
        affineConst P.word
            ≤ P.endpointOddCount *
                3 ^ P.endpointOddCount :=
          hB
        _ ≤
            P.endpointOddCount *
              (K * (P.endpointOddCount + 1) ^ A *
                P.terminalGap) :=
          Nat.mul_le_mul_left
            P.endpointOddCount
            hGapP
        _ =
            (P.endpointOddCount * K *
              (P.endpointOddCount + 1) ^ A) *
                P.terminalGap := by
          ring
    exact
      representative_le_of_gap_sandwich
        P.terminalGap_pos
        hGR
        hNumerator


/--
endpointOddCount polynomial は length polynomial で一様に抑えられる。
これは failure や gap witness に依存しない純粋な combinatorial bound。
-/
theorem endpointPolynomial_le_simpleLengthPolynomial
    (P : FirstPassagePath)
    (K A : ℕ) :
    P.endpointOddCount * K *
        (P.endpointOddCount + 1) ^ A
      ≤
    K * (P.length + 1) ^ (A + 1) := by
  have hmle :
      P.endpointOddCount ≤ P.length :=
    P.endpointOddCount_le_length
  have hbase :
      P.endpointOddCount + 1 ≤ P.length + 1 := by
    omega
  have hpow :
      (P.endpointOddCount + 1) ^ A ≤
        (P.length + 1) ^ A :=
    natPow_le_natPow_of_le_local hbase A
  have hleft :
      P.endpointOddCount * K ≤
        P.length * K :=
    Nat.mul_le_mul_right K hmle
  have hpoly :
      P.endpointOddCount * K *
          (P.endpointOddCount + 1) ^ A
        ≤
      P.length * K *
          (P.length + 1) ^ A :=
    Nat.mul_le_mul hleft hpow
  have hLen :
      P.length ≤ P.length + 1 := by
    omega
  calc
    P.endpointOddCount * K *
        (P.endpointOddCount + 1) ^ A
        ≤
      P.length * K *
        (P.length + 1) ^ A :=
      hpoly
    _ =
      K * P.length *
        (P.length + 1) ^ A := by
      ring
    _ ≤
      K * (P.length + 1) *
        (P.length + 1) ^ A := by
      exact
        Nat.mul_le_mul_right
          ((P.length + 1) ^ A)
          (Nat.mul_le_mul_left K hLen)
    _ =
      K * (P.length + 1) ^ (A + 1) := by
      rw [pow_succ]
      ring


/--
FirstFailureEdge の upper path について、
failure + gap witness から直接 length polynomial bound を得る。
-/
theorem upperRepresentative_le_simpleLengthPolynomial
    (F : FirstFailureEdge)
    {K A : ℕ}
    (hGap :
      ∀ p H : ℕ,
        0 < p →
        3 ^ p < 2 ^ H →
        3 ^ p ≤
          K * (p + 1) ^ A * (2 ^ H - 3 ^ p)) :
    leastRepresentative F.upper ≤
      K * (F.upperPath.length + 1) ^ (A + 1) := by
  let P := F.upperPath
  have hPword : P.word = F.upper := by
    rfl
  have hFailure :
      ¬ WordPureSeparation P.word := by
    rw [hPword]
    exact F.upper_failure
  have hEndpoint :
      leastRepresentative P.word ≤
        P.endpointOddCount * K *
          (P.endpointOddCount + 1) ^ A :=
    representative_le_endpointPolynomial_of_failure
      P
      hFailure
      hGap
  have hEndpointLeLength :
      P.endpointOddCount * K *
          (P.endpointOddCount + 1) ^ A
        ≤
      K * (P.length + 1) ^ (A + 1) :=
    endpointPolynomial_le_simpleLengthPolynomial
      P
      K
      A
  have hLength :
      leastRepresentative P.word ≤
        K * (P.length + 1) ^ (A + 1) :=
    le_trans hEndpoint hEndpointLeLength
  have hLength' :
      leastRepresentative F.upper ≤
        K * (P.length + 1) ^ (A + 1) := by
    rw [← hPword]
    exact hLength
  simpa only [P] using hLength'


/--
separation failure と polynomial gap witness から
upper representative の explicit polynomial bound を直接得る。
-/
theorem upperR_le_simpleLengthPolynomial
    (F : FirstFailureEdge)
    {K A : ℕ}
    (hGap :
      ∀ p H : ℕ,
        0 < p →
        3 ^ p < 2 ^ H →
        3 ^ p ≤
          K * (p + 1) ^ A * (2 ^ H - 3 ^ p)) :
    F.step.edge.upperR ≤
      K * (F.step.edge.length + 1) ^ (A + 1) := by
  have hR :
      leastRepresentative F.upper ≤
        K * (F.upperPath.length + 1) ^ (A + 1) :=
    upperRepresentative_le_simpleLengthPolynomial
      F
      hGap
  rw [F.edge_upperR_eq]
  rw [← F.upperPath_length_eq_edge_length]
  exact hR

/-- first failure edge は polynomial-width carry corridor に入る。 -/
theorem polynomial_carry_corridor
    (F : FirstFailureEdge)
    {K A : ℕ}
    (hGap :
      ∀ p H : ℕ,
        0 < p →
        3 ^ p < 2 ^ H →
        3 ^ p ≤
          K * (p + 1) ^ A * (2 ^ H - 3 ^ p)) :
    F.step.edge.modulus ≤ F.step.edge.lowerR + F.step.edge.deltaR ∧
      F.step.edge.lowerR + F.step.edge.deltaR ≤
        F.step.edge.modulus + K * (F.step.edge.length + 1) ^ (A + 1) := by
  have hCarry := F.hasCarry
  have hR := F.upperR_le_simpleLengthPolynomial hGap
  have hsum :=
    F.step.edge.lowerR_add_deltaR_eq_modulus_add_upperR_of_hasCarry hCarry
  constructor
  · exact hCarry
  · calc
      F.step.edge.lowerR + F.step.edge.deltaR
          = F.step.edge.modulus + F.step.edge.upperR := hsum
      _ ≤ F.step.edge.modulus +
          K * (F.step.edge.length + 1) ^ (A + 1) :=
        Nat.add_le_add_left hR F.step.edge.modulus

/-- 高い swap position では corridor 幅は `2^position` 未満。 -/
theorem high_position_carry_corridor
    (F : FirstFailureEdge)
    {K A : ℕ}
    (hGap :
      ∀ p H : ℕ,
        0 < p →
        3 ^ p < 2 ^ H →
        3 ^ p ≤
          K * (p + 1) ^ A * (2 ^ H - 3 ^ p))
    (hHigh :
      K * (F.step.edge.length + 1) ^ (A + 1) <
        2 ^ F.step.edge.position) :
    F.step.edge.modulus ≤ F.step.edge.lowerR + F.step.edge.deltaR ∧
      F.step.edge.lowerR + F.step.edge.deltaR <
        F.step.edge.modulus + 2 ^ F.step.edge.position := by
  have hCorr := F.polynomial_carry_corridor hGap
  exact ⟨hCorr.1, lt_of_le_of_lt hCorr.2 (Nat.add_lt_add_left hHigh _)⟩

end FirstFailureEdge

/--
全 boundary safety を仮定すれば、global CST failure は
一つの local polynomial carry corridor を生成する。
-/
theorem exists_polynomial_carry_corridor_of_cst_failure
    (M : MicroObject)
    {K A : ℕ}
    (hGap :
      ∀ p H : ℕ,
        0 < p →
        3 ^ p < 2 ^ H →
        3 ^ p ≤
          K * (p + 1) ^ A * (2 ^ H - 3 ^ p))
    (hBoundarySafe :
      ∀ boundary : ParityWord,
        IsFerrersBoundary boundary → WordPureSeparation boundary)
    (hFail : ¬ M.CSTHolds) :
    ∃ F : FirstFailureEdge,
      F.step.edge.HasCarry ∧
      F.step.edge.modulus ≤ F.step.edge.lowerR + F.step.edge.deltaR ∧
      F.step.edge.lowerR + F.step.edge.deltaR ≤
        F.step.edge.modulus + K * (F.step.edge.length + 1) ^ (A + 1) := by
  rcases exists_firstFailureEdge_of_cst_failure M hFail hBoundarySafe with ⟨F⟩
  have hCorr := F.polynomial_carry_corridor hGap
  exact ⟨F, F.hasCarry, hCorr.1, hCorr.2⟩

end CSTMicro
end Collatz2
