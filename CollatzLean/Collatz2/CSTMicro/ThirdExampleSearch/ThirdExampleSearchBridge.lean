import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleFirstDefectOneCell
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleRunBridge

namespace Collatz2.CSTMicro.ThirdExampleSearch.CertifiedHigh

theorem exactPower_mod {a d : Nat} (h : Word.ExactTwoPowZ a (d : ℤ)) :
    d % (2^(a+1)) = 2^a := by
  have hd : 2^a ∣ d := by exact_mod_cast h.1
  obtain ⟨t,ht⟩ := hd
  have htodd : t%2=1 := by
    by_contra ho
    have hev : 2∣t := Nat.dvd_of_mod_eq_zero (by omega)
    have hdd : 2^(a+1)∣d := by
      rw [ht, Nat.pow_succ]
      exact Nat.mul_dvd_mul_left (2^a) hev
    apply h.2
    exact_mod_cast hdd
  rw [ht,Nat.pow_succ,Nat.mul_mod_mul_left,htodd,Nat.mul_one]

/-- 既存exact deficit式から計算済みbranch剰余への接続。 -/
theorem candidate_branch_residue
    (CertL : ThirdExampleCFPacketCertification thirdExampleLeftModulus)
    {w : Word} {deficit gap m j a : Nat}
    (C : DoubleDecomposition.ExactCriticalGapOneFerrersCertificate
      w thirdExampleTargetP thirdExampleTargetH deficit gap m)
    (F : ThirdExampleFirstCriticalDefectAt w j)
    (ha : a ∈ [67, 65, 62, 59, 56, 54, 51, 48, 46, 43, 40])
    (hheight : Word.prefixTwoDepth w j = a) :
    m%branchModulus a=branchResidue a := by
  let q := branchModulus a
  have hdiv : q∣thirdExampleLeftModulus := highBranchModuli_checked a ha
  have hExact := thirdExampleFirstDefect_exactTwoPow C F
  rw [hheight] at hExact
  have hdm := exactPower_mod hExact
  have hqpos : 0<q := by exact Nat.pow_pos (by decide)
  have hpLt : 2^a<q := by
    dsimp [q,branchModulus]
    rw [Nat.pow_succ]
    have hp : 0<2^a := Nat.pow_pos (by decide)
    omega
  have hdq : (deficit:ZMod q)=(2:ZMod q)^a := by
    have hh : (deficit:ZMod q)=((2^a:Nat):ZMod q) := by
      apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
      rw [Nat.mod_eq_of_lt hpLt]
      exact hdm
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using hh
  have hAffine := thirdExampleCertificate_deficit_affine_modTwo CertL C
  rw [thirdExampleDeficitInterceptModTwo_literal,thirdExampleGapModTwo_literal] at hAffine
  have hcast := congrArg (ZMod.castHom hdiv (ZMod q)) hAffine
  simp only [map_sub,map_mul,map_natCast,map_ofNat] at hcast
  have hmq : (gapResidue:ZMod q)*(m:ZMod q)+(2:ZMod q)^a=(intercept:ZMod q) := by
    rw [hdq] at hcast
    dsimp [gapResidue,intercept]
    linear_combination hcast
  have hres : (gapResidue:ZMod q)*(branchResidue a:ZMod q)+(2:ZMod q)^a=(intercept:ZMod q) := by
    have hh := (ZMod.natCast_eq_natCast_iff' (gapResidue*branchResidue a+2^a) intercept q).mpr
      (highBranchResidues_checked a ha)
    simpa using hh
  have hinv : (gapInverse:ZMod q)*(gapResidue:ZMod q)=1 := by
    have hh : (gapInverse*gapResidue:Nat)%q=1%q := by
      have hone : 1<q := by
        have hpa : 0<2^a := Nat.pow_pos (by decide)
        omega
      simpa [Nat.mod_eq_of_lt hone] using highBranchInverses_checked a ha
    have hh' := (ZMod.natCast_eq_natCast_iff' _ _ _).mpr hh
    simpa using hh'
  have heq : (gapResidue:ZMod q)*(m:ZMod q)=(gapResidue:ZMod q)*(branchResidue a:ZMod q) := by
    linear_combination hmq-hres
  have hmz : (m:ZMod q)=(branchResidue a:ZMod q) := by
    have hh := congrArg (fun x : ZMod q => (gapInverse:ZMod q)*x) heq
    simpa only [←mul_assoc,hinv,one_mul] using hh
  have hh := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hmz
  have hrlt : branchResidue a<q := Nat.mod_lt _ hqpos
  simpa [Nat.mod_eq_of_lt hrlt] using hh

end Collatz2.CSTMicro.ThirdExampleSearch.CertifiedHigh
