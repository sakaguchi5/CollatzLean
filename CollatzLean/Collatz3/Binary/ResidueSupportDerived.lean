import CollatzLean.Collatz3.Binary.ResidueSupport


/-!
# Collatz3 Binary: residue support の反復 refinement

R1 の singleton locking を任意有限 depth まで反復するための derived theorem 群。
新しい support notion は導入しない。
-/

namespace Collatz3
namespace Binary

/-- shallow modulus は任意に深い residue-depth modulus を割る。 -/
theorem residueDepthModulus_dvd_add (K d : ℕ) :
    residueDepthModulus K ∣ residueDepthModulus (K + d) := by
  unfold residueDepthModulus
  refine ⟨3 ^ d, ?_⟩
  rw [← pow_add]
  congr 1
  omega

namespace UniqueResidueWitness

/-- unique witness は特に support witness でもある。 -/
theorem supports
    {P : ℕ → Prop} {K r : ℕ}
    (h : UniqueResidueWitness P K r) :
    SupportsResidue P K r := by
  rcases h with ⟨x, hx, hUnique⟩
  exact ⟨x, hx⟩

/-- singleton locking は任意の有限 depth だけ反復できる。 -/
theorem refine_iterate
    {P : ℕ → Prop} {K r : ℕ}
    (h : UniqueResidueWitness P K r)
    (d : ℕ) :
    ∃ s : ℕ,
      s ≡ r [MOD residueDepthModulus K] ∧
        UniqueResidueWitness P (K + d) s := by
  induction d with
  | zero =>
      refine ⟨r, ?_, ?_⟩
      · rfl
      · simpa using h
  | succ d ih =>
      rcases ih with ⟨s, hsr, hs⟩
      rcases hs.refine with ⟨q, hqLt, hqs, hqUnique⟩
      have hqsBase :
          q ≡ s [MOD residueDepthModulus K] := by
        apply Nat.ModEq.of_dvd (h := hqs)
        exact residueDepthModulus_dvd_add K d
      refine ⟨q, hqsBase.trans hsr, ?_⟩
      simpa [Nat.add_assoc] using hqUnique

end UniqueResidueWitness

namespace SupportsResidue

/-- deep support は任意の浅い depth へ射影できる。 -/
theorem of_add
    {P : ℕ → Prop} {K d r : ℕ}
    (h : SupportsResidue P (K + d) r) :
    SupportsResidue P K r := by
  rcases h with ⟨x, hxP, hx⟩
  refine ⟨x, hxP, ?_⟩
  apply Nat.ModEq.of_dvd (h := hx)
  exact residueDepthModulus_dvd_add K d

end SupportsResidue

end Binary
end Collatz3
