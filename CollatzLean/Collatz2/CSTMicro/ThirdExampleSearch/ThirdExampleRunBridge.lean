import CollatzLean.Collatz2.Local.FirstCrossing
import CollatzLean.Collatz2.Orbit.FutureMinimum
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleFiniteFamilyVerifier
import Mathlib.Tactic.Linarith

namespace Collatz2.CSTMicro.ThirdExampleSearch.CertifiedHigh

theorem OddRun.toRuns {u : List Nat} {x y : Nat} (h : OddRun u x y) : Runs u x y := by
  induction h with
  | nil x => exact .nil x
  | cons he hs ho _ ih => exact .cons he hs (Nat.odd_iff.mpr ho) ih

/-- 正規化odd-stepの一意性により、短いrunは長いrunのprefixである。 -/
theorem runs_prefix_unique {u : Word} {x y : Nat} (hu : Runs u x y)
    {w : Word} {z : Nat} (hw : Runs w x z) (hlen : u.length ≤ w.length) :
    u = w.take u.length := by
  induction hu generalizing w z with
  | nil x => simp
  | @cons e u x t y he hs ho hu ih =>
    cases hw with
    | nil => simp at hlen
    | @cons f v _ t' _ hf hs' ho' hv =>
      obtain ⟨hef,htt⟩ := OddOrbit.normalizedStep_unique hs hs' ho ho'
      subst f; subst t'
      have htail := ih hv (by simpa using hlen)
      simpa using congrArg (List.cons e) htail

/-- coefficient first crossing より前にactual runが降下することはない。 -/
theorem no_short_drop {w u : Word} {n y z : Nat}
    (hw : Runs w n z) (hf : Word.FirstCrossing w)
    (hu : Runs u n y) (hlen : u.length < w.length) (hy : y < n) : False := by
  by_cases hz : u.length=0
  · have hu0 : u=[] := List.length_eq_zero_iff.mp hz
    subst u
    cases hu
    omega
  · have hp := runs_prefix_unique hu hw (Nat.le_of_lt hlen)
    have he := hf.properExpanding (by omega : 0<u.length) hlen
    rw [←hp] at he
    have he' := Word.expanding_iff_twoPow_lt_threePow.mp he
    have hr := Word.realizes_iff _ _ _ |>.mp hu.realizes
    have hm := Nat.mul_le_mul_right n (Nat.le_of_lt he')
    have hd := Nat.mul_lt_mul_of_pos_left hy (Nat.pow_pos (by decide : 0<2) : 0<2^Word.twoSteps u)
    omega

/-- 範囲内の合同解を、欠落なくfamilyのindexへ写す。 -/
theorem branch_candidate_index {a m : Nat}
    (hm : m < cutoff) (hr : m % branchModulus a = branchResidue a) :
    ∃ i, i<branchCount a ∧ m=branchResidue a+branchModulus a*i := by
  have hq : 0<branchModulus a := by exact Nat.pow_pos (by decide)
  have he : m=branchResidue a+branchModulus a*(m/branchModulus a) := by
    rw [←hr]; exact (Nat.mod_add_div m (branchModulus a)).symm
  have hrm : branchResidue a≤m := by rw [←hr]; exact Nat.mod_le _ _
  refine ⟨m/branchModulus a,?_,he⟩
  unfold branchCount
  rw [ite_eq_left (by omega : branchResidue a<cutoff)]
  apply Nat.lt_succ_of_le
  apply (Nat.le_div_iff_mul_le hq).mpr
  rw [Nat.mul_comm]
  omega

/-- formulaで数えたindex範囲は、指定上界内の整数と正確に一致する。 -/
theorem branch_index_range_iff (a i : Nat) :
    i<branchCount a ↔ branchResidue a+branchModulus a*i<cutoff := by
  have hq : 0<branchModulus a := Nat.pow_pos (by decide)
  unfold branchCount
  split
  · constructor
    · intro hi
      have hd : i≤(cutoff-1-branchResidue a)/branchModulus a := by omega
      have hm := (Nat.le_div_iff_mul_le hq).mp hd
      rw [Nat.mul_comm] at hm
      omega
    · intro hi
      have hm : i*branchModulus a≤cutoff-1-branchResidue a := by
        rw [Nat.mul_comm]
        omega
      have hd := (Nat.le_div_iff_mul_le hq).mpr hm
      omega
  · constructor <;> intro hi <;> omega

/-- family内の異なるindexが同じ整数を表すことはない。 -/
theorem branch_index_injective (a : Nat) {i k : Nat}
    (h : branchResidue a + branchModulus a * i = branchResidue a + branchModulus a * k) : i=k := by
  exact Nat.mul_left_cancel (Nat.pow_pos (by decide) : 0<branchModulus a)
    (Nat.add_left_cancel h)

theorem branch_generated_residue (a i : Nat) :
    (branchResidue a+branchModulus a*i)%branchModulus a=branchResidue a := by
  have hq : 0<branchModulus a := Nat.pow_pos (by decide)
  have hr : branchResidue a<branchModulus a := Nat.mod_lt _ hq
  simp [Nat.add_mod,Nat.mod_eq_of_lt hr]

theorem checked_family_impossible {a m : Nat} {w : Word} {z : Nat}
    (hdrops : FamilyDrops (rootFamily a) 1000)
    (hm : m < cutoff) (hr : m % branchModulus a = branchResidue a)
    (hw : Runs w (3 * m + 1) z) (hf : Word.FirstCrossing w)
    (hlen : 1000 < w.length) : False := by
  obtain ⟨i,hi,he⟩ := branch_candidate_index hm hr
  obtain ⟨u,y,hu,hy,hb⟩ := hdrops i hi
  have hn : (rootFamily a).n0+(rootFamily a).dn*i=3*m+1 := by
    simp only [rootFamily]
    rw [he]
    ring
  have hx : (rootFamily a).x0+(rootFamily a).dx*i=3*m+1 := hn
  rw [hx] at hu
  rw [hn] at hy
  exact no_short_drop hw hf hu.toRuns (by omega) hy


end Collatz2.CSTMicro.ThirdExampleSearch.CertifiedHigh
