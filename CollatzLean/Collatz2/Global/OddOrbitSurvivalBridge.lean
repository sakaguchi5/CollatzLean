import CollatzLean.Collatz2.Global.InfiniteSurvival
import CollatzLean.Collatz2.Orbit.OddOrbit

/-!
# Collatz2: OddOrbit から NestedSurvivalChain への橋

任意の normalized odd-only `OddOrbit` には、その値域の最小値が存在する。
その最小値を `x`、最初の最小値到達位置を `i` とし、

  `word n     = O.segment i (n + 1)`
  `endpoint n = O.value (i + (n + 1))`

と置く。

最小性により future の全 actual boundary は `x` 以上であり、
各 exponent は正なので residue modulus は無限に深くなる。
従ってこの minimum tail は `NestedSurvivalChain x` を自然に与える。

このファイルは `OddOrbit` と `InfiniteSurvival` の abstract chain を結ぶだけで、
新しい trajectory-specific data は導入しない。
-/

namespace Collatz2
namespace OddOrbit

/-- 軌道値の中に少なくとも一つ自然数値が存在する。 -/
private theorem exists_orbit_value (O : OddOrbit) :
    ∃ a : ℕ, ∃ n : ℕ, O.value n = a := by
  exact ⟨O.value 0, 0, rfl⟩

/--
軌道全体の値域の最小値。
`Nat.find` により値そのものを最小化する。
-/
noncomputable def globalMinimumValue (O : OddOrbit) : ℕ := by
  classical
  exact Nat.find (exists_orbit_value O)

/-- global minimum は実際に軌道上で達成される。 -/
theorem exists_value_eq_globalMinimumValue
    (O : OddOrbit) :
    ∃ n : ℕ, O.value n = O.globalMinimumValue := by
  classical
  exact Nat.find_spec (exists_orbit_value O)

/-- global minimum は任意の軌道値以下。 -/
theorem globalMinimumValue_le_value
    (O : OddOrbit)
    (n : ℕ) :
    O.globalMinimumValue ≤ O.value n := by
  classical
  exact Nat.find_min' (exists_orbit_value O) ⟨n, rfl⟩

/-- global minimum が最初に現れる index。 -/
noncomputable def globalMinimumIndex (O : OddOrbit) : ℕ := by
  classical
  exact Nat.find (O.exists_value_eq_globalMinimumValue)

/-- `globalMinimumIndex` では値が exact に global minimum。 -/
theorem value_globalMinimumIndex
    (O : OddOrbit) :
    O.value O.globalMinimumIndex = O.globalMinimumValue := by
  classical
  exact Nat.find_spec (O.exists_value_eq_globalMinimumValue)

/-- global minimum は正。 -/
theorem globalMinimumValue_pos
    (O : OddOrbit) :
    0 < O.globalMinimumValue := by
  rw [← O.value_globalMinimumIndex]
  exact O.value_pos O.globalMinimumIndex

/-- global minimum は odd。 -/
theorem globalMinimumValue_odd
    (O : OddOrbit) :
    Odd O.globalMinimumValue := by
  rw [← O.value_globalMinimumIndex]
  exact O.value_odd O.globalMinimumIndex

/-- valid word では各 exponent が1以上なので、word 長は総2指数以下。 -/
private theorem length_le_twoSteps_of_valid
    {w : Word}
    (hvalid : w.Valid) :
    w.length ≤ w.twoSteps := by
  induction w with
  | nil =>
      simp [Word.twoSteps]
  | cons e w ih =>
      have he : 0 < e := hvalid e (by simp)
      have htail : Word.Valid w := by
        intro a ha
        exact hvalid a (by simp [ha])
      have hih := ih htail
      simp only [List.length_cons, Word.twoSteps_cons]
      omega

/-- elementary growth bound `n+1 ≤ 2^n`。 -/
private theorem succ_le_two_pow
    (n : ℕ) :
    n + 1 ≤ 2 ^ n := by
  induction n with
  | zero =>
      norm_num
  | succ n ih =>
      rw [pow_succ]
      calc
        n + 1 + 1 ≤ 2 * (n + 1) := by omega
        _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
      omega

/--
同じ word と同じ start を持つ二つの affine realization は endpoint が一意。
minimum-tail の arbitrary prefix run を actual orbit boundary と同定する補助定理。
-/
private theorem realizes_endpoint_unique
    {w : Word} {x y z : ℕ}
    (hy : Word.Realizes w x y)
    (hz : Word.Realizes w x z) :
    y = z := by
  have hyEq := (Word.realizes_iff w x y).1 hy
  have hzEq := (Word.realizes_iff w x z).1 hz
  have hmul :
      2 ^ w.twoSteps * y = 2 ^ w.twoSteps * z := by
    calc
      2 ^ w.twoSteps * y
          = 3 ^ w.oddSteps * x + w.affineConst := hyEq
      _ = 2 ^ w.twoSteps * z := hzEq.symm
  exact
    Nat.mul_left_cancel
      (Nat.pow_pos (by omega : 0 < (2 : ℕ)))
      hmul

/--
minimum tail の n 段目 word。
nonempty を正本側で要求するため長さ `n+1` から開始する。
-/
noncomputable def minimumTailWord
    (O : OddOrbit)
    (n : ℕ) : Word :=
  O.segment O.globalMinimumIndex (n + 1)

/-- minimum tail の n 段目 endpoint。 -/
noncomputable def minimumTailEndpoint
    (O : OddOrbit)
    (n : ℕ) : ℕ :=
  O.value (O.globalMinimumIndex + (n + 1))

/-- minimum tail の各 word は actual normalized run。 -/
theorem runs_minimumTail
    (O : OddOrbit)
    (n : ℕ) :
    Runs (O.minimumTailWord n)
      O.globalMinimumValue
      (O.minimumTailEndpoint n) := by
  classical
  unfold minimumTailWord minimumTailEndpoint
  have hrun := O.runsSegment O.globalMinimumIndex (n + 1)
  simpa [O.value_globalMinimumIndex] using hrun

/-- minimum tail の各 word は valid。 -/
theorem minimumTailWord_valid
    (O : OddOrbit)
    (n : ℕ) :
    (O.minimumTailWord n).Valid :=
  (O.runs_minimumTail n).valid

/-- minimum tail の各 word は nonempty。 -/
theorem minimumTailWord_nonempty
    (O : OddOrbit)
    (n : ℕ) :
    O.minimumTailWord n ≠ [] := by
  classical
  intro hnil
  have hlen := congrArg List.length hnil
  unfold minimumTailWord at hlen
  simp only [O.segment_length, List.length_nil] at hlen
  omega

/-- minimum tail の word family は prefix inclusion で nested。 -/
theorem minimumTailWord_nested
    (O : OddOrbit)
    {m n : ℕ}
    (hmn : m ≤ n) :
    ∃ v : Word,
      O.minimumTailWord m ++ v = O.minimumTailWord n := by
  classical
  let i := O.globalMinimumIndex
  let d := n - m
  refine ⟨O.segment (i + (m + 1)) d, ?_⟩
  unfold minimumTailWord
  change
    O.segment i (m + 1) ++ O.segment (i + (m + 1)) d =
      O.segment i (n + 1)
  calc
    O.segment i (m + 1) ++ O.segment (i + (m + 1)) d
        = O.segment i ((m + 1) + d) :=
          (O.segment_add i (m + 1) d).symm
    _ = O.segment i (n + 1) := by
      congr 1
      dsimp [d]
      omega

/--
minimum tail では全 actual prefix endpoint が anchor `globalMinimumValue` 以上。
-/
theorem minimumTail_allPrefixesSurvive
    (O : OddOrbit)
    (n : ℕ) :
    Word.AllPrefixesSurviveAt
      (O.minimumTailWord n)
      O.globalMinimumValue := by
  classical
  have hfull := O.runs_minimumTail n
  apply
    (Word.allPrefixesSurviveAt_iff_allPrefixStartDefectsNonnegative hfull).2
  intro u v huv
  let i := O.globalMinimumIndex
  have hlenEq := congrArg List.length huv
  have hlen : u.length ≤ n + 1 := by
    unfold minimumTailWord at hlenEq
    simp only [List.length_append, O.segment_length] at hlenEq
    omega
  have huSegment : u = O.segment i u.length := by
    calc
      u = (u ++ v).take u.length := by simp
      _ = (O.minimumTailWord n).take u.length := by rw [huv]
      _ = (O.segment i (n + 1)).take u.length := by
        rfl
      _ = O.segment i u.length :=
        O.segment_take_of_le hlen
  have hrunSegment := O.runsSegment i u.length
  have hrunU :
      Runs u O.globalMinimumValue (O.value (i + u.length)) := by
    rw [huSegment]
    simpa [i, O.value_globalMinimumIndex] using hrunSegment
  have hmin :
      O.globalMinimumValue ≤ O.value (i + u.length) :=
    O.globalMinimumValue_le_value (i + u.length)
  exact
    (hrunU.realizes.start_le_end_iff_startDefect_nonneg).1 hmin

/-- minimum tail の residue modulus は任意の整数閾値を eventually 越える。 -/
theorem minimumTail_modulusEscapes
    (O : OddOrbit) :
    ∀ K : ℤ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      K < (Word.residueModulus (O.minimumTailWord n) : ℤ) := by
  classical
  intro K
  cases K with
  | ofNat k =>
      refine ⟨k, ?_⟩
      intro n hn
      have hlen :=
        length_le_twoSteps_of_valid (O.minimumTailWord_valid n)
      have hH :
          n + 1 ≤ (O.minimumTailWord n).twoSteps := by
        have hwlen : (O.minimumTailWord n).length = n + 1 := by
          unfold minimumTailWord
          exact O.segment_length O.globalMinimumIndex (n + 1)
        rw [hwlen] at hlen
        exact hlen
      have hpow :=
        succ_le_two_pow ((O.minimumTailWord n).twoSteps + 1)
      have hkM :
          k < Word.residueModulus (O.minimumTailWord n) := by
        unfold Word.residueModulus
        omega
      have hkMZ :
          (k : ℤ) <
            (Word.residueModulus (O.minimumTailWord n) : ℤ) := by
        exact_mod_cast hkM
      exact hkMZ
  | negSucc k =>
      refine ⟨0, ?_⟩
      intro n hn
      have hpos :
          0 < Word.residueModulus (O.minimumTailWord n) :=
        Word.residueModulus_pos _
      have hposZ :
          (0 : ℤ) < (Word.residueModulus (O.minimumTailWord n) : ℤ) := by
        exact_mod_cast hpos
      omega

/--
## OddOrbit -> NestedSurvivalChain

任意の odd-only orbit の global minimum tail は、その minimum を anchor とする
`NestedSurvivalChain` を canonical に与える。
-/
noncomputable def toNestedSurvivalChain
    (O : OddOrbit) :
    Word.NestedSurvivalChain O.globalMinimumValue := by
  classical
  exact
    { word := O.minimumTailWord
      endpoint := O.minimumTailEndpoint
      valid := O.minimumTailWord_valid
      nonempty := O.minimumTailWord_nonempty
      run := O.runs_minimumTail
      survives := O.minimumTail_allPrefixesSurvive
      nested := fun {_ _} hmn => O.minimumTailWord_nested hmn
      modulusEscapes := O.minimumTail_modulusEscapes }

/--
任意の `OddOrbit` から positive odd anchor と、
その anchor に基づく nested survival chain が存在する。
-/
theorem exists_positive_odd_nestedSurvivalChain
    (O : OddOrbit) :
    ∃ x : ℕ,
      ∃ _C : Word.NestedSurvivalChain x,
        0 < x ∧ Odd x := by
  classical
  exact
    ⟨O.globalMinimumValue,
      O.toNestedSurvivalChain,
      O.globalMinimumValue_pos,
      O.globalMinimumValue_odd⟩

/--
反例用途の薄い corollary。

global minimum が `1` より大きい orbit は、
nontrivial anchor と、その anchor に基づく nested survival chain を与える。
-/
theorem exists_nontrivial_nestedSurvivalChain
    (O : OddOrbit)
    (hmin : 1 < O.globalMinimumValue) :
    ∃ x : ℕ,
      ∃ _C : Word.NestedSurvivalChain x,
        1 < x := by
  classical
  exact
    ⟨O.globalMinimumValue,
      O.toNestedSurvivalChain,
      hmin⟩

end OddOrbit
end Collatz2
