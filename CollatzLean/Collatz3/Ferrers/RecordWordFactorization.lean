import CollatzLean.Collatz3.Ferrers.RecordFerrers
import Mathlib.Data.List.Forall2
import Mathlib.Data.List.Range

/-!
# Collatz3: RecordFerrers の lossless word factorization

canonical record partition の block length 列に沿って local exponent word を切り出し、
それらを連結すると元の critical word に exact に戻ることを証明する。

canonical partition は anchor `1` から始まるので、whole word の正しい形は

`[1] ++ local₁ ++ ... ++ localₛ`

である。先頭 `[1]` は固定 canonical prefix であり、record block の一つではない。
-/

namespace Collatz3
namespace Critical

/-- local depth は区間の連結に対して加法的。 -/
theorem localDepth_add
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    {a r s : ℕ}
    (hEnd : a + r + s ≤ m) :
    localDepth h a (r + s) =
      localDepth h a r + localDepth h (a + r) s := by
  have hAR :=
    profileHeight_add_localDepth A (a := a) (j := r) (by omega)
  have hARS :=
    profileHeight_add_localDepth A (a := a) (j := r + s) (by omega)
  have hTail :=
    profileHeight_add_localDepth A (a := a + r) (j := s) (by omega)
  have hARS' :
      profileHeight h a + localDepth h a (r + s) =
        profileHeight h (a + r + s) := by
    simpa [Nat.add_assoc] using hARS
  omega

/-- local word は隣接する二区間の連結に exact に一致する。 -/
theorem localWord_add
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    {a r s : ℕ}
    (hEnd : a + r + s ≤ m) :
    localWord h a (r + s) =
      localWord h a r ++ localWord h (a + r) s := by
  unfold localWord wordFromHeight
  rw [List.range_add, List.map_append]
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro k hk
  have hkLt : k < s := by
    simpa using hk
  have hK :=
    localDepth_add A (a := a) (r := r) (s := k) (by omega)
  have hKS :=
    localDepth_add A (a := a) (r := r) (s := k + 1) (by omega)
  simp only [Function.comp_apply]
  have hIndex : r + k + 1 = r + (k + 1) := by omega
  rw [hIndex, hK, hKS]
  omega

/-- local word の odd-step 数は区間長そのもの。 -/
@[simp] theorem oddSteps_localWord
    {m : ℕ}
    (h : Profile m)
    (a r : ℕ) :
    Word.oddSteps (localWord h a r) = r :=
  oddSteps_wordFromHeight (fun j => localDepth h a j) r

/-- start `0` の local word は whole `wordOfProfile` と同じ word。 -/
theorem localWord_zero_eq_wordOfProfile
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    (hm : 0 < m) :
    localWord h 0 m = wordOfProfile h := by
  unfold localWord wordOfProfile
  apply congrArg (fun height : ℕ → ℕ => wordFromHeight height m)
  funext j
  simp [localDepth, profileHeight_zero A hm]

/-- 幅 `m>1` では canonical anchor までの最初の local word は exact に `[1]`。 -/
theorem localWord_zero_one_eq_singleton_one
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    (hm : 1 < m) :
    localWord h 0 1 = [1] := by
  have hZero : profileHeight h 0 = 0 :=
    profileHeight_zero A (by omega)
  have hOne : profileHeight h 1 = 1 :=
    profileHeight_one_eq_one A hm
  simp [localWord, wordFromHeight, localDepth, hZero, hOne]

end Critical

namespace Ferrers

open Critical

/--
start `a` から block length 列を順に読み、各区間の `localWord` を並べる。
これは単なる deterministic finite factorization data。
-/
def localWordsFromLengths
    {m : ℕ}
    (h : Profile m) : ℕ → List ℕ → List Word
  | _a, [] => []
  | a, r :: rs =>
      localWord h a r :: localWordsFromLengths h (a + r) rs

/-- local word 列の odd-step 数を読むと元の block length 列に戻る。 -/
theorem map_oddSteps_localWordsFromLengths
    {m : ℕ}
    (h : Profile m) :
    ∀ (a : ℕ) (rs : List ℕ),
      (localWordsFromLengths h a rs).map Word.oddSteps = rs
  | _a, [] => by
      simp [localWordsFromLengths]
  | a, r :: rs => by
      simp [localWordsFromLengths,
        map_oddSteps_localWordsFromLengths h (a + r) rs]

/--
length 列が覆う区間内では、local word 列を flatten するとその全区間の local word に戻る。
-/
theorem flatten_localWordsFromLengths_eq_localWord
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h) :
    ∀ (a : ℕ) (rs : List ℕ),
      a + rs.sum ≤ m →
      (localWordsFromLengths h a rs).flatten =
        localWord h a rs.sum
  | a, [], _hEnd => by
      simp [localWordsFromLengths, localWord, wordFromHeight]
  | a, r :: rs, hEnd => by
      have hTailEnd : (a + r) + rs.sum ≤ m := by
        simpa [List.sum_cons, Nat.add_assoc] using hEnd
      have hIH :=
        flatten_localWordsFromLengths_eq_localWord
          A (a + r) rs hTailEnd
      simp only [localWordsFromLengths, List.flatten_cons]
      rw [hIH]
      have hAll : a + r + rs.sum ≤ m := by
        exact hTailEnd
      rw [← localWord_add A (a := a) (r := r) (s := rs.sum) hAll]
      simp [List.sum_cons]

/--
全 block が local critical なら、各 local word は対応する幅の genuine CriticalWord。
-/
theorem localWordsFromLengths_forall₂_critical
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h) :
    ∀ (a : ℕ) (rs : List ℕ),
      LocalCriticalBlocksFrom h a rs →
      List.Forall₂
        (fun r w => IsCriticalWord r w)
        rs (localWordsFromLengths h a rs)
  | _a, [], _L =>
      List.Forall₂.nil
  | a, r :: rs, L => by
      exact List.Forall₂.cons
        (isCriticalWord_localWord A L.1)
        (localWordsFromLengths_forall₂_critical
          A (a + r) rs L.2)

namespace RecordFerrers

/-- RecordFerrers の deterministic canonical local word 列。 -/
def canonicalLocalWords
    {m : ℕ}
    (R : RecordFerrers m) : List Word :=
  localWordsFromLengths
    R.profile.1 initialRoofAnchor
    (canonicalRecordLengths R.profile.1)

/-- canonical local word 列の odd-step 数は canonical block lengths そのもの。 -/
theorem map_oddSteps_canonicalLocalWords
    {m : ℕ}
    (R : RecordFerrers m) :
    R.canonicalLocalWords.map Word.oddSteps =
      canonicalRecordLengths R.profile.1 := by
  exact map_oddSteps_localWordsFromLengths
    R.profile.1 initialRoofAnchor
    (canonicalRecordLengths R.profile.1)

/-- 各 canonical local word は対応 block width の genuine CriticalWord。 -/
theorem canonicalLocalWords_forall₂_critical
    {m : ℕ}
    (R : RecordFerrers m) :
    List.Forall₂
      (fun r w => IsCriticalWord r w)
      (canonicalRecordLengths R.profile.1)
      R.canonicalLocalWords := by
  exact localWordsFromLengths_forall₂_critical
    R.profile.2 initialRoofAnchor
    (canonicalRecordLengths R.profile.1)
    R.localCriticalBlocks

/-- canonical local word 列を flatten すると anchor `1` 以後の suffix word に戻る。 -/
theorem flatten_canonicalLocalWords_eq_localWord
    {m : ℕ}
    (R : RecordFerrers m) :
    R.canonicalLocalWords.flatten =
      localWord R.profile.1 initialRoofAnchor (m - 1) := by
  have hSum := canonicalRecordLengths_sum
    (h := R.profile.1) R.one_lt_width
  have hm : 1 ≤ m := Nat.le_of_lt R.one_lt_width
  have hEnd :
      initialRoofAnchor +
          (canonicalRecordLengths R.profile.1).sum ≤ m := by
    rw [hSum]
    simp only [initialRoofAnchor]
    omega
  have h :=
    flatten_localWordsFromLengths_eq_localWord
      R.profile.2 initialRoofAnchor
      (canonicalRecordLengths R.profile.1) hEnd
  simpa [canonicalLocalWords, hSum] using h

/--
RecordFerrers の whole critical word は、固定 prefix `[1]` と canonical local CriticalWords の
連結へ lossless に分解される。
-/
theorem wordOfProfile_eq_one_append_flatten_canonicalLocalWords
    {m : ℕ}
    (R : RecordFerrers m) :
    wordOfProfile R.profile.1 =
      [1] ++ R.canonicalLocalWords.flatten := by
  have hmPos : 0 < m := by
    exact lt_trans (by omega : 0 < 1) R.one_lt_width
  have hWhole :=
    localWord_zero_eq_wordOfProfile R.profile.2 hmPos
  have hHead :=
    localWord_zero_one_eq_singleton_one
      R.profile.2 R.one_lt_width
  have hTail := R.flatten_canonicalLocalWords_eq_localWord
  have hAdd :
      localWord R.profile.1 0 (1 + (m - 1)) =
        localWord R.profile.1 0 1 ++
          localWord R.profile.1 1 (m - 1) := by
    apply localWord_add R.profile.2
    omega
  have hmEq : 1 + (m - 1) = m := by omega
  rw [hmEq, hWhole, hHead] at hAdd
  rw [hTail]
  exact hAdd

end RecordFerrers
end Ferrers
end Collatz3
