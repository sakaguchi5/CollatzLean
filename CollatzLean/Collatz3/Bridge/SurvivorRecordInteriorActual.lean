import CollatzLean.Collatz3.Bridge.InfiniteSurvivorEscape
import CollatzLean.Collatz3.Bridge.SurvivorRecordWindows
import CollatzLean.Collatz3.Ferrers.RecordWordFactorization
import CollatzLean.Collatz3.Semantics.FirstPassage



/-!
# Collatz3 Bridge: survivor completion の内部 Record block を actual orbit へ戻す

`survivorCriticalCompletion` は最後の exponent だけを critical terminal まで仮想的に延長する。
従って completion 全体を同じ natural start の actual run と同一視してはいけない。

一方 terminal より strict に手前の区間では completion は元 survivor prefix を全く変更しない。
このファイルでは、その安全な内部部分だけを actual `OddOrbit` へ戻す。

中心となる事実は次の通り。

* completion profile の proper height は元 survivor composition の `sizeUpTo` と一致する。
* actual endpoint survivor code ではその値は infinite prefix depth `D_k`。
* 従って `a+r < m` の内部 local word は actual `segmentWord a r` と exact に同じ。
* その local geometry が `IsLocalCriticalBlock` なら、同じ actual segment は
  genuine `ActualFirstPassage` になる。
* completion の roof cut は survivor defect `δ_a = 0` を意味する。

これにより pure RecordFerrers geometry と actual orbit semantics を、terminal completion を
誤って actual 化せずに接続する。
-/

namespace Collatz3
namespace Bridge

/-- completion admissible profile の proper height は元 survivor prefix size。 -/
theorem survivorCompletion_profileHeight_eq_sizeUpTo
    {n : ℕ}
    (hn : 0 < n)
    (S : SurvivorParityCode n)
    {k : ℕ}
    (hk : k < S.1.length) :
    Critical.profileHeight
        (survivorCriticalCompletionAdmissibleProfile hn S).1 k =
      S.1.sizeUpTo k := by
  rw [Critical.profileHeight_of_lt _ hk]
  unfold Critical.checkpoint
  have hProfile :=
    survivorCriticalCompletion_profile_eq_defect hn S ⟨k, hk⟩
  change
    Critical.beattyIndex k -
        RestrictedCriticalPartition.profile
          (survivorCriticalCompletionPartition hn S) ⟨k, hk⟩ =
      S.1.sizeUpTo k
  rw [hProfile]
  unfold survivorPrefixDefect
  have hPow := S.2.proper_safe hk
  have hLe : S.1.sizeUpTo k ≤ Critical.beattyIndex k := by
    have h :=
      Critical.prefixDepth_le_beatty_of_powerCoefficient
        (w := S.1.blocks) (k := k) (by simpa using hPow)
    simpa using h
  change
    Critical.beattyIndex k -
        (Critical.beattyIndex k - S.1.sizeUpTo k) =
      S.1.sizeUpTo k
  omega

/-- completion local depth は元 survivor composition の二つの prefix size の差。 -/
theorem survivorCompletion_localDepth_eq_sizeUpTo_sub
    {n : ℕ}
    (hn : 0 < n)
    (S : SurvivorParityCode n)
    {a j : ℕ}
    (haj : a + j < S.1.length) :
    Critical.localDepth
        (survivorCriticalCompletionAdmissibleProfile hn S).1 a j =
      S.1.sizeUpTo (a + j) - S.1.sizeUpTo a := by
  unfold Critical.localDepth
  have ha : a < S.1.length := by omega
  rw [
    survivorCompletion_profileHeight_eq_sizeUpTo hn S haj,
    survivorCompletion_profileHeight_eq_sizeUpTo hn S ha
  ]

/-- survivorRecordWindow の underlying profile は completion profile そのもの。 -/
@[simp] theorem survivorRecordWindow_profile
    {n : ℕ}
    (hn : 0 < n)
    (S : SurvivorParityCode n)
    (hm : 2 < S.1.length)
    (P : Critical.IsPrimitiveWidth S.1.length)
    (B : Critical.IsBestUpperWidth S.1.length) :
    (survivorRecordWindow hn S hm P B).profile =
      survivorCriticalCompletionAdmissibleProfile hn S :=
  rfl

end Bridge

namespace OddOrbit

open Bridge

/--
actual endpoint survivor completion の internal local depth は actual segment two-depth そのもの。
-/
theorem endpointCompletion_localDepth_eq_segmentTwoSteps
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m a j : ℕ}
    (hm : 0 < m)
    (haj : a + j < m) :
    Critical.localDepth
        (survivorCriticalCompletionAdmissibleProfile
          (infinitePrefixDepth_pos SInf hm)
          (O.endpointSurvivorCode SInf m)).1
        a j =
      Word.twoSteps (O.segmentWord a j) := by
  let C := O.endpointSurvivorCode SInf m
  let hD := infinitePrefixDepth_pos SInf hm
  have hLen : C.1.length = m := by
    simp only [endpointSurvivorCode_length, C]
  have hLocal :=
    survivorCompletion_localDepth_eq_sizeUpTo_sub hD C
      (by simpa [hLen] using haj)
  have hSizeEnd :
      C.1.sizeUpTo (a + j) = infinitePrefixDepth O.exponent (a + j) := by
    exact O.endpointSurvivorCode_sizeUpTo SInf m (a + j) (by omega)
  have hSizeStart :
      C.1.sizeUpTo a = infinitePrefixDepth O.exponent a := by
    exact O.endpointSurvivorCode_sizeUpTo SInf m a (by omega)
  rw [hSizeEnd, hSizeStart] at hLocal
  have hAdd := O.infinitePrefixDepth_add_eq a j
  change
    Critical.localDepth
        (survivorCriticalCompletionAdmissibleProfile hD C).1
        a j =
      Word.twoSteps (O.segmentWord a j)
  rw [hLocal, hAdd]
  simp

/--
terminal を避ける local word は仮想 completion と actual orbit で exact に同じ。
-/
theorem endpointCompletion_localWord_eq_segmentWord
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m a r : ℕ}
    (hm : 0 < m)
    (hInternal : a + r < m) :
    Critical.localWord
        (survivorCriticalCompletionAdmissibleProfile
          (infinitePrefixDepth_pos SInf hm)
          (O.endpointSurvivorCode SInf m)).1
        a r =
      O.segmentWord a r := by
  let C := O.endpointSurvivorCode SInf m
  let hD := infinitePrefixDepth_pos SInf hm
  let H := survivorCriticalCompletionAdmissibleProfile hD C
  apply Word.eq_of_oddSteps_eq_of_prefixTwoDepth_eq
  · simp [Critical.localWord]
  · intro k hk
    have hkr : k ≤ r := by
      simpa [Critical.localWord, Critical.oddSteps_wordFromHeight] using hk
    have hEnd : a + r ≤ C.1.length := by
      have hLen : C.1.length = m := by
        simp only [endpointSurvivorCode_length, C]
      omega
    have hLocalPrefix :
        Word.prefixTwoDepth (Critical.localWord H.1 a r) k =
          Critical.localDepth H.1 a k := by
      unfold Critical.localWord
      apply Critical.prefixTwoDepth_wordFromHeight
      · exact Critical.localDepth_zero H.1 a
      · intro t ht
        exact Critical.localDepth_lt_succ H.2 hEnd ht
      · exact hkr
    have hActualPrefix :
        Word.prefixTwoDepth (O.segmentWord a r) k =
          Word.twoSteps (O.segmentWord a k) :=
      O.prefixTwoDepth_segmentWord a r k hkr
    rw [hLocalPrefix, hActualPrefix]
    apply O.endpointCompletion_localDepth_eq_segmentTwoSteps SInf hm
    omega

/--
completion geometry の internal local critical block は、同じ actual orbit segment の
`ActualFirstPassage` になる。
-/
theorem endpointCompletion_internal_actualFirstPassage
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m a r : ℕ}
    (hm : 0 < m)
    (hInternal : a + r < m)
    (B : Critical.IsLocalCriticalBlock
      (survivorCriticalCompletionAdmissibleProfile
        (infinitePrefixDepth_pos SInf hm)
        (O.endpointSurvivorCode SInf m)).1
      a r) :
    ActualFirstPassage
      (Critical.localWord
        (survivorCriticalCompletionAdmissibleProfile
          (infinitePrefixDepth_pos SInf hm)
          (O.endpointSurvivorCode SInf m)).1
        a r)
      (O.value a)
      (O.value (a + r)) := by
  let C := O.endpointSurvivorCode SInf m
  let hD := infinitePrefixDepth_pos SInf hm
  let H := survivorCriticalCompletionAdmissibleProfile hD C
  have hWord :
      Critical.localWord H.1 a r = O.segmentWord a r := by
    simpa [C, hD, H] using
      O.endpointCompletion_localWord_eq_segmentWord SInf hm hInternal
  have hRun :
      Runs (Critical.localWord H.1 a r)
        (O.value a) (O.value (a + r)) := by
    rw [hWord]
    exact O.runsSegment a r
  have hCritical :
      Critical.IsCriticalWord r (Critical.localWord H.1 a r) :=
    Critical.isCriticalWord_localWord H.2 (by simpa [C, hD, H] using B)
  have hFirst :
      Word.CriticalFirstPassage (Critical.localWord H.1 a r) := by
    constructor
    · rw [hCritical.oddSteps_eq]
      exact hCritical.twoSteps_eq
    · intro k hk
      rw [hCritical.oddSteps_eq] at hk
      exact hCritical.prefixTwoDepth_le_beatty hk
  exact ⟨hRun, hFirst⟩

/--
primitive best-upper endpoint window から作った真の `RecordFerrers` でも、terminal より手前の
local critical block は同じ actual first-passage である。

`RecordFerrers.localCriticalBlocks` から個々の canonical block の `Blocal` を取り出した後に
直接使うための wrapper。
-/
theorem endpointRecord_internal_actualFirstPassage
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m a r : ℕ}
    (hm : 0 < m)
    (hWidth : 2 < (O.endpointSurvivorCode SInf m).1.length)
    (P : Critical.IsPrimitiveWidth (O.endpointSurvivorCode SInf m).1.length)
    (Best : Critical.IsBestUpperWidth (O.endpointSurvivorCode SInf m).1.length)
    (hInternal : a + r < m)
    (Blocal : Critical.IsLocalCriticalBlock
      (survivorRecordWindow
        (infinitePrefixDepth_pos SInf hm)
        (O.endpointSurvivorCode SInf m)
        hWidth P Best).profile.1
      a r) :
    ActualFirstPassage
      (Critical.localWord
        (survivorRecordWindow
          (infinitePrefixDepth_pos SInf hm)
          (O.endpointSurvivorCode SInf m)
          hWidth P Best).profile.1
        a r)
      (O.value a)
      (O.value (a + r)) := by
  let C := O.endpointSurvivorCode SInf m
  let hD := infinitePrefixDepth_pos SInf hm
  let R := survivorRecordWindow hD C hWidth P Best
  have B' :
      Critical.IsLocalCriticalBlock
        (survivorCriticalCompletionAdmissibleProfile hD C).1 a r := by
    simpa [R, C, hD] using Blocal
  have h :=
    O.endpointCompletion_internal_actualFirstPassage SInf hm hInternal
      (by simpa [C, hD] using B')
  simpa [R, C, hD] using h

/-- completion roof cut は finite survivor defect zero と exact に対応する。 -/
theorem endpointCompletion_roofCut_defect_zero
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m a : ℕ}
    (hm : 0 < m)
    (R : Critical.IsRoofCut
      (survivorCriticalCompletionAdmissibleProfile
        (infinitePrefixDepth_pos SInf hm)
        (O.endpointSurvivorCode SInf m)).1
      a) :
    infiniteSurvivorDefect O.exponent a = 0 := by
  let C := O.endpointSurvivorCode SInf m
  let hD := infinitePrefixDepth_pos SInf hm
  let H := survivorCriticalCompletionAdmissibleProfile hD C
  have hLen : C.1.length = m := by
    simp only [endpointSurvivorCode_length, C]
  have ha : a < m := by
    have := R.lt_width
    simpa [C, hD, H, hLen] using this
  have hHeight :
      Critical.profileHeight H.1 a = C.1.sizeUpTo a := by
    apply survivorCompletion_profileHeight_eq_sizeUpTo hD C
    simpa [hLen] using ha
  have hSize :
      C.1.sizeUpTo a = infinitePrefixDepth O.exponent a :=
    O.endpointSurvivorCode_sizeUpTo SInf m a (Nat.le_of_lt ha)
  have hRoof : Critical.profileHeight H.1 a = Critical.beattyIndex a := by
    simpa [C, hD, H] using R.height_eq
  unfold infiniteSurvivorDefect
  rw [← hSize, ← hHeight, hRoof]
  simp


/--
actual endpoint completion から作った RecordFerrers の proper record cut は
actual survivor defect zero を強制する。
-/
theorem endpointRecordCut_defect_zero
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m a : ℕ}
    (hm : 0 < m)
    (hWidth : 2 < (O.endpointSurvivorCode SInf m).1.length)
    (P : Critical.IsPrimitiveWidth (O.endpointSurvivorCode SInf m).1.length)
    (Best : Critical.IsBestUpperWidth (O.endpointSurvivorCode SInf m).1.length)
    (Rcut : Ferrers.IsRecordCutAfter
      (survivorRecordWindow
        (infinitePrefixDepth_pos SInf hm)
        (O.endpointSurvivorCode SInf m)
        hWidth P Best).profile.1
      Critical.initialRoofAnchor a) :
    infiniteSurvivorDefect O.exponent a = 0 := by
  let C := O.endpointSurvivorCode SInf m
  let hD := infinitePrefixDepth_pos SInf hm
  let R := survivorRecordWindow hD C hWidth P Best
  have hRoof : Critical.IsRoofCut R.profile.1 a :=
    Ferrers.isRoofCut_of_isRecordCutAfter R.profile.2 (by simpa [R, C, hD] using Rcut)
  have hRoof' :
      Critical.IsRoofCut
        (survivorCriticalCompletionAdmissibleProfile hD C).1 a := by
    simpa [R, C, hD] using hRoof
  exact O.endpointCompletion_roofCut_defect_zero SInf hm (by simpa [C, hD] using hRoof')

end OddOrbit
end Collatz3
