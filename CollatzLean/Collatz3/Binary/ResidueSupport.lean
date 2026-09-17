import CollatzLean.Collatz3.Binary.ResidueWeight
import CollatzLean.Collatz3.Binary.AlternatingWeight
import Mathlib.Data.Nat.ModEq

/-!
# Collatz3 Binary: residue support and singleton locking

特定の binary family `P : ℕ → Prop` が mod `3^(K+1)` の residue を実現するかを
薄い existential predicate として保存する。

counting object を primitive にせず、singleton locking は unique witness の refinement として述べる。
この形なら alternating-weight fiber 以外にも再利用できる。
-/

namespace Collatz3
namespace Binary

/-- family `P` が depth `K` の residue `r` を実現する。 -/
def SupportsResidue
    (P : ℕ → Prop)
    (K r : ℕ) : Prop :=
  ∃ x : ℕ,
    P x ∧ x ≡ r [MOD residueDepthModulus K]

/-- family `P` の depth `K`, residue `r` に属する witness がちょうど一つ。 -/
def UniqueResidueWitness
    (P : ℕ → Prop)
    (K r : ℕ) : Prop :=
  ∃! x : ℕ,
    P x ∧ x ≡ r [MOD residueDepthModulus K]

/-- 深い residue support は一段浅い support へ射影される。 -/
theorem SupportsResidue.of_succ
    {P : ℕ → Prop} {K r : ℕ}
    (h : SupportsResidue P (K + 1) r) :
    SupportsResidue P K r := by
  rcases h with ⟨x, hxP, hx⟩
  refine ⟨x, hxP, ?_⟩
  apply Nat.ModEq.of_dvd (h := hx)
  rw [residueDepthModulus_succ]
  exact Nat.dvd_mul_left _ _

/--
singleton residue は次 depth で canonical child residue に lock される。

child label は unique witness `x` の `mod 3^(K+2)` representative として取る。
-/
theorem UniqueResidueWitness.refine
    {P : ℕ → Prop} {K r : ℕ}
    (h : UniqueResidueWitness P K r) :
    ∃ s : ℕ,
      s < residueDepthModulus (K + 1) ∧
      s ≡ r [MOD residueDepthModulus K] ∧
      UniqueResidueWitness P (K + 1) s := by
  rcases h with ⟨x, hx, hxUnique⟩
  let s : ℕ := x % residueDepthModulus (K + 1)
  have hsLt : s < residueDepthModulus (K + 1) := by
    dsimp [s]
    exact Nat.mod_lt _ (residueDepthModulus_pos (K + 1))
  have hxsDeep : x ≡ s [MOD residueDepthModulus (K + 1)] := by
    dsimp [s]
    exact (Nat.mod_modEq x (residueDepthModulus (K + 1))).symm
  have hxsBase : x ≡ s [MOD residueDepthModulus K] := by
    apply Nat.ModEq.of_dvd (h := hxsDeep)
    rw [residueDepthModulus_succ]
    exact Nat.dvd_mul_left _ _
  have hsr : s ≡ r [MOD residueDepthModulus K] :=
    hxsBase.symm.trans hx.2
  refine ⟨s, hsLt, hsr, ?_⟩
  refine ⟨x, ⟨hx.1, hxsDeep⟩, ?_⟩
  intro y hy
  have hyBase : y ≡ r [MOD residueDepthModulus K] := by
    have hysBase : y ≡ s [MOD residueDepthModulus K] := by
      apply Nat.ModEq.of_dvd (h := hy.2)
      rw [residueDepthModulus_succ]
      exact Nat.dvd_mul_left _ _
    exact hysBase.trans hsr
  exact hxUnique y ⟨hy.1, hyBase⟩

/-- alternating-weight fiber の residue support。 -/
def AlternatingWeightSupportsResidue
    (K evenWeight oddWeight length r : ℕ) : Prop :=
  SupportsResidue
    (fun x => HasAlternatingWeight x evenWeight oddWeight length)
    K r

/-- alternating-weight fiber の singleton residue witness。 -/
def AlternatingWeightUniqueResidueWitness
    (K evenWeight oddWeight length r : ℕ) : Prop :=
  UniqueResidueWitness
    (fun x => HasAlternatingWeight x evenWeight oddWeight length)
    K r

end Binary
end Collatz3
