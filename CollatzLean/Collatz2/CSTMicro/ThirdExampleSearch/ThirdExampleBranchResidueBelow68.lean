import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleLow14FirstDefect

/-!
# 第3例低枝探索 2: branch residue を全 `a < 68` へ一般化する

旧 `candidate_branch_residue` は高枝11個だけを列挙した有限 checkpoint に依存していた。
しかし左 collar の本質は

  q = 2^(a+1),  a < 68

なら `q | 2^68` であり、固定 gap inverse がその modulus 上でも逆元になることにある。

そこで 68 個だけの小さい有限 checkpoint を一度検証し、candidate residue theorem を
高枝リスト非依存の形へ一般化する。
-/
namespace Collatz2.CSTMicro.ThirdExampleSearch.CertifiedHigh

/-- `a < 68` なら branch modulus は左 collar `2^68` を割る。 -/
theorem thirdExample_branchModuli_below68_checked :
    ∀ a : Fin 68,
      branchModulus a.val ∣ leftModulus := by
  decide

/-- 固定 Newton inverse は全 `a < 68` の branch modulus 上で正しい。 -/
theorem thirdExample_branchInverses_below68_checked :
    ∀ a : Fin 68,
      gapInverse * gapResidue % branchModulus a.val = 1 := by
  decide

/-- 定義した branch residue は全 `a < 68` で affine deficit 合同を満たす。 -/
theorem thirdExample_branchResidues_below68_checked :
    ∀ a : Fin 68,
      (gapResidue * branchResidue a.val + 2 ^ a.val) %
          branchModulus a.val =
        intercept % branchModulus a.val := by
  decide

/--
`q ∣ n` のとき、Nat から来た affine 等式を
`ZMod n` から `ZMod q` へ exact に降ろす。

`ZMod.castHom` の実装詳細を後段から隠すための bridge。
-/
theorem zmodNatAffine_eq_of_dvd
    {n q x A B y : ℕ}
    (hDiv : q ∣ n)
    (h :
      (x : ZMod n) =
        (A : ZMod n) -
          (B : ZMod n) * (y : ZMod n)) :
    (x : ZMod q) =
      (A : ZMod q) -
        (B : ZMod q) * (y : ZMod q) := by
  let f : ZMod n →+* ZMod q :=
    ZMod.castHom hDiv (ZMod q)
  have hx :
      f (x : ZMod n) = (x : ZMod q) := by
    exact map_natCast f x
  have hA :
      f (A : ZMod n) = (A : ZMod q) := by
    exact map_natCast f A
  have hB :
      f (B : ZMod n) = (B : ZMod q) := by
    exact map_natCast f B
  have hy :
      f (y : ZMod n) = (y : ZMod q) := by
    exact map_natCast f y
  have hMap :
      f (x : ZMod n) =
        f ((A : ZMod n) -
          (B : ZMod n) * (y : ZMod n)) := by
    exact congrArg (fun z : ZMod n => f z) h
  calc
    (x : ZMod q) =
        f (x : ZMod n) := hx.symm
    _ =
        f ((A : ZMod n) -
          (B : ZMod n) * (y : ZMod n)) := hMap
    _ =
        f (A : ZMod n) -
          f ((B : ZMod n) * (y : ZMod n)) := by
      rw [map_sub]
    _ =
        f (A : ZMod n) -
          f (B : ZMod n) * f (y : ZMod n) := by
      rw [map_mul]
    _ =
        (A : ZMod q) -
          (B : ZMod q) * (y : ZMod q) := by
      rw [hA, hB, hy]

/--
真の exact candidate の first-defect height が `a < 68` なら、multiplier `m` は
対応する `2^(a+1)` branch residue に必ず入る。

高枝11値の membership 仮定を完全に除いた版。
-/
theorem candidate_branch_residue_of_lt_68
    (CertL : ThirdExampleCFPacketCertification thirdExampleLeftModulus)
    {w : Word}
    {deficit gap m j a : Nat}
    (C : DoubleDecomposition.ExactCriticalGapOneFerrersCertificate
      w thirdExampleTargetP thirdExampleTargetH deficit gap m)
    (F : ThirdExampleFirstCriticalDefectAt w j)
    (ha : a < 68)
    (hHeight : Word.prefixTwoDepth w j = a) :
    m % branchModulus a = branchResidue a := by
  let q := branchModulus a
  have hDiv : q ∣ leftModulus :=
    thirdExample_branchModuli_below68_checked ⟨a, ha⟩
  have hExact := thirdExampleFirstDefect_exactTwoPow C F
  rw [hHeight] at hExact
  have hdm := exactPower_mod hExact
  have hqPos : 0 < q := by
    exact Nat.pow_pos (by decide)
  have hpLt : 2 ^ a < q := by
    dsimp [q, branchModulus]
    rw [Nat.pow_succ]
    have hp : 0 < 2 ^ a := Nat.pow_pos (by decide)
    omega
  have hdq :
      (deficit : ZMod q) = (2 : ZMod q) ^ a := by
    have hh :
        (deficit : ZMod q) = ((2 ^ a : Nat) : ZMod q) := by
      apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
      rw [Nat.mod_eq_of_lt hpLt]
      exact hdm
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hh
  have hAffine := thirdExampleCertificate_deficit_affine_modTwo CertL C
  rw [thirdExampleDeficitInterceptModTwo_literal,
      thirdExampleGapModTwo_literal] at hAffine
  have hCastRaw :=
    congrArg
      (ZMod.castHom hDiv (ZMod q))
      hAffine
  have hCast :
      (deficit : ZMod q) =
        (intercept : ZMod q) -
          (gapResidue : ZMod q) * (m : ZMod q) := by
    dsimp [intercept, gapResidue]
    exact zmodNatAffine_eq_of_dvd hDiv hAffine
  have hmq :
      (gapResidue : ZMod q) * (m : ZMod q) +
          (2 : ZMod q) ^ a =
        (intercept : ZMod q) := by
    rw [hdq] at hCast
    linear_combination hCast
  have hres :
      (gapResidue : ZMod q) * (branchResidue a : ZMod q) +
          (2 : ZMod q) ^ a =
        (intercept : ZMod q) := by
    have hh :=
      (ZMod.natCast_eq_natCast_iff'
        (gapResidue * branchResidue a + 2 ^ a)
        intercept q).mpr
        (thirdExample_branchResidues_below68_checked ⟨a, ha⟩)
    simpa using hh
  have hinv :
      (gapInverse : ZMod q) * (gapResidue : ZMod q) = 1 := by
    have hh :
        (gapInverse * gapResidue : Nat) % q = 1 % q := by
      have hOne : 1 < q := by
        have hpa : 0 < 2 ^ a := Nat.pow_pos (by decide)
        dsimp [q, branchModulus]
        rw [Nat.pow_succ]
        omega
      simpa [Nat.mod_eq_of_lt hOne] using
        (thirdExample_branchInverses_below68_checked ⟨a, ha⟩)
    have hh' := (ZMod.natCast_eq_natCast_iff' _ _ _).mpr hh
    simpa using hh'
  have heq :
      (gapResidue : ZMod q) * (m : ZMod q) =
        (gapResidue : ZMod q) * (branchResidue a : ZMod q) := by
    linear_combination hmq - hres
  have hmz :
      (m : ZMod q) = (branchResidue a : ZMod q) := by
    have hh := congrArg (fun x : ZMod q => (gapInverse : ZMod q) * x) heq
    simpa only [← mul_assoc, hinv, one_mul] using hh
  have hh := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hmz
  have hrLt : branchResidue a < q := Nat.mod_lt _ hqPos
  simpa [Nat.mod_eq_of_lt hrLt] using hh

/--
低14枝では first-defect height は37以下なので、上の一般 residue theorem を常に適用できる。
-/
theorem candidate_low14_branch_residue
    (R : ThirdExampleRangeCertificate)
    (CertL : ThirdExampleCFPacketCertification thirdExampleLeftModulus)
    {w : Word}
    {deficit gap m j : Nat}
    (C : DoubleDecomposition.ExactCriticalGapOneFerrersCertificate
      w thirdExampleTargetP thirdExampleTargetH deficit gap m)
    (F : ThirdExampleFirstCriticalDefectAt w j) :
    m % branchModulus (Word.prefixTwoDepth w j) =
      branchResidue (Word.prefixTwoDepth w j) := by
  have hLe := thirdExample_firstDefect_height_le_37 R CertL C F
  exact candidate_branch_residue_of_lt_68
    CertL C F (by omega) rfl

end Collatz2.CSTMicro.ThirdExampleSearch.CertifiedHigh
