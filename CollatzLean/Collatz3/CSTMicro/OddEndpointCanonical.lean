import CollatzLean.Collatz3.CSTMicro.ProfileReindex
import CollatzLean.Collatz3.CSTMicro.CriticalGapBridge
import CollatzLean.Collatz3.CSTMicro.Realization
import CollatzLean.Collatz3.CSTMicro.LiftClassification
import CollatzLean.Collatz3.Bridge.FirstPassageProfile

/-!
# Collatz3 CSTMicro Stage 6: odd endpoint と canonical `R,Y,Q`

Stage 5 までで standard first-passage path は canonical に

  standard parity path
    -> compressed critical exponent word
    -> admissible critical profile

へ移された。

Stage 6 では endpoint が奇数である場合に、standard parity trace を actual odd-only run へ戻し、
既存 Collatz3 の odd-endpoint canonical coordinates `R,Y,Q` へ接続する。

ここで重要なのは modulus の違いである。

* standard parity cylinder: `2^H`
* odd-endpoint canonical cylinder: `2^(H+1)`

したがって odd-endpoint canonical start は standard least representative `R₀` の
二つの lifts

  R₀,
  R₀ + 2^H

のどちらかにしかならない。

single-lift 条件のもとで非下降 odd-endpoint realization が存在すれば、
その realization 自身が canonical `R,Y` に一致し、canonical drift `Q` は非負になる。
-/

namespace Collatz3
namespace CSTMicro

/-- standard parity trace は append の中間点で exact に分解できる。 -/
theorem traceRealizes_append_iff
    (u v : ParityWord)
    (x z : ℕ) :
    TraceRealizes (u ++ v) x z ↔
      ∃ y : ℕ,
        TraceRealizes u x y ∧
          TraceRealizes v y z := by
  induction u generalizing x with
  | nil =>
      simp [TraceRealizes]
  | cons b u ih =>
      cases b with
      | false =>
          simp only [List.cons_append, TraceRealizes]
          constructor
          · rintro ⟨m, hxm, htail⟩
            rcases (ih m).1 htail with ⟨y, huy, hyv⟩
            exact ⟨y, ⟨m, hxm, huy⟩, hyv⟩
          · rintro ⟨y, ⟨m, hxm, huy⟩, hyv⟩
            exact ⟨m, hxm, (ih m).2 ⟨y, huy, hyv⟩⟩
      | true =>
          simp only [List.cons_append, TraceRealizes]
          constructor
          · rintro ⟨m, hxm, htail⟩
            rcases (ih m).1 htail with ⟨y, huy, hyv⟩
            exact ⟨y, ⟨m, hxm, huy⟩, hyv⟩
          · rintro ⟨y, ⟨m, hxm, huy⟩, hyv⟩
            exact ⟨m, hxm, (ih m).2 ⟨y, huy, hyv⟩⟩

namespace TraceRealizes

/-- parity word が `true` から始まる exact trace の start は奇数。 -/
theorem start_odd_of_true_cons
    {v : ParityWord}
    {x y : ℕ}
    (h : TraceRealizes (true :: v) x y) :
    Odd x := by
  rcases h with ⟨z, hxz, htail⟩
  obtain ⟨k, hEven | hOdd⟩ := x.even_or_odd'
  · rw [hEven] at hxz
    omega
  · exact ⟨k, hOdd⟩

/--
start が standard least representative なら、その realization の endpoint は
standard canonical endpoint に一意に一致する。
-/
theorem end_eq_canonicalEndpoint_of_start_eq_leastRepresentative
    {v : ParityWord}
    {x y : ℕ}
    (h : TraceRealizes v x y)
    (hx : x = leastRepresentative v) :
    y = canonicalEndpoint v := by
  rcases h.exists_lift with ⟨k, hxLift, hyLift⟩
  rw [hx] at hxLift
  have hMk : parityModulus v * k = 0 := by
    omega
  have hMpos : 0 < parityModulus v := by
    unfold parityModulus
    positivity
  have hk : k = 0 := by
    rcases Nat.mul_eq_zero.mp hMk with hM | hk
    · exact False.elim ((Nat.ne_of_gt hMpos) hM)
    · exact hk
  subst k
  simpa using hyLift

end TraceRealizes

/--
valid exponent word の parity expansion が odd endpoint を持つ exact trace なら、
その trace は exact odd-only `Runs` に圧縮できる。
-/
theorem runs_of_trace_expandWord
    {w : Word}
    (hValid : Word.Valid w)
    {x y : ℕ}
    (hTrace : TraceRealizes (expandWord w) x y)
    (hy : Odd y) :
    Runs w x y := by
  induction w generalizing x with
  | nil =>
      simp only [expandWord_nil, TraceRealizes] at hTrace
      subst y
      exact Runs.nil x
  | cons e tail ih =>
      have he : 0 < e := hValid e (by simp)
      have hTailValid : Word.Valid tail := by
        intro a ha
        exact hValid a (by simp [ha])
      rw [expandWord_cons] at hTrace
      rcases
          (traceRealizes_append_iff
            (parityBlock e) (expandWord tail) x y).1 hTrace
        with ⟨z, hBlock, hTail⟩
      have hzOdd : Odd z := by
        cases tail with
        | nil =>
            simp only [expandWord_nil, TraceRealizes] at hTail
            rw [hTail]
            exact hy
        | cons f fs =>
            have hStart :
                TraceRealizes
                  (true ::
                    (List.replicate (f - 1) false ++ expandWord fs))
                  z y := by
              simpa [expandWord, parityBlock] using hTail
            exact hStart.start_odd_of_true_cons
      have hStep : OddStep e x z := by
        refine ⟨he, ?_, hzOdd⟩
        have hAff := hBlock.affine
        unfold AffineRealizes at hAff
        rw [length_parityBlock_of_pos he] at hAff
        simpa using hAff
      exact Runs.cons hStep (ih hTailValid hTail)

namespace FirstPassagePath

/-- standard trace を canonical compressed word の endpoint equation へ移す。 -/
theorem compressedEndpointEquation_of_trace
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount)
    {x y : ℕ}
    (h : TraceRealizes P.word x y) :
    Word.EndpointEquation P.compressedExponentWord x y := by
  have hExp :
      TraceRealizes (expandWord P.compressedExponentWord) x y := by
    rw [P.expandWord_compressedExponentWord hp]
    exact h
  exact
    (affineRealizes_expandWord_iff_wordEndpointEquation
      (P.compressedExponentWord_valid hp) x y).1 hExp.affine

/--
standard trace の endpoint が奇数なら、canonical compressed word は actual first-passage run になる。
-/
theorem actualFirstPassage_of_trace_oddEndpoint
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount)
    {x y : ℕ}
    (h : TraceRealizes P.word x y)
    (hy : Odd y) :
    ActualFirstPassage P.compressedExponentWord x y := by
  constructor
  · have hExp :
        TraceRealizes (expandWord P.compressedExponentWord) x y := by
      rw [P.expandWord_compressedExponentWord hp]
      exact h
    exact
      runs_of_trace_expandWord
        (P.compressedExponentWord_valid hp) hExp hy
  · exact P.compressedExponentWord_critical hp

/--
Stage 5 の extracted profile と compressed word は既存 canonical bridge の意味でも
同じ affine data `(p,H,B)` を持つ。
-/
theorem extractedCriticalProfile_sameAffineData
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount) :
    Critical.SameAffineData
      P.extractedCriticalProfile
      P.compressedExponentWord := by
  constructor
  · rfl
  · constructor
    · exact (P.compressedExponentWord_critical hp).totalTwoDepth_eq
    · rw [P.compressedExponentWord_affineConst_eq hp]
      rw [P.extractedCriticalProfile_affineNumerator_eq hp]

/--
standard path の `endpointOddCount` を型添字にした profile view も compressed word と
同じ affine data を持つ。
-/
theorem endpointIndexedCriticalProfile_sameAffineData
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount) :
    Critical.SameAffineData
      (P.endpointIndexedCriticalProfile hp)
      P.compressedExponentWord := by
  constructor
  · exact P.compressedExponentWord_oddSteps_eq hp
  · constructor
    · have h := (P.compressedExponentWord_critical hp).totalTwoDepth_eq
      rw [P.compressedExponentWord_oddSteps_eq hp] at h
      exact h
    · rw [P.compressedExponentWord_affineConst_eq hp]
      rw [P.endpointIndexedCriticalProfile_affineNumerator_eq hp]

/-- compressed word の canonical `R` は endpoint-indexed profile の canonical `R` と一致。 -/
theorem compressedCanonicalStart_eq_endpointIndexedProfile
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount) :
    Word.canonicalStart P.compressedExponentWord =
      Critical.profileCanonicalStart (P.endpointIndexedCriticalProfile hp) :=
  (P.endpointIndexedCriticalProfile_sameAffineData hp).canonicalStart_eq

/-- compressed word の canonical `Y` は endpoint-indexed profile の canonical `Y` と一致。 -/
theorem compressedCanonicalEnd_eq_endpointIndexedProfile
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount) :
    Word.canonicalEnd P.compressedExponentWord =
      Critical.profileCanonicalEnd (P.endpointIndexedCriticalProfile hp) :=
  (P.endpointIndexedCriticalProfile_sameAffineData hp).canonicalEnd_eq

/-- compressed word の canonical `Q` は endpoint-indexed profile の canonical `Q` と一致。 -/
theorem compressedCanonicalGap_eq_endpointIndexedProfile
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount) :
    Word.canonicalGap P.compressedExponentWord =
      Critical.profileCanonicalGap (P.endpointIndexedCriticalProfile hp) :=
  (P.endpointIndexedCriticalProfile_sameAffineData hp).canonicalGap_eq

/--
endpoint-indexed profile の REQ equation を standard path の `(p,H,B)` で書いた形。
-/
theorem endpointIndexedProfile_req_equation_standard
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount) :
    2 ^ P.length *
        Critical.profileCanonicalEnd (P.endpointIndexedCriticalProfile hp) =
      3 ^ P.endpointOddCount *
          Critical.profileCanonicalStart (P.endpointIndexedCriticalProfile hp) +
        affineConst P.word := by
  have h :=
    Critical.profile_req_equation (P.endpointIndexedCriticalProfile hp)
  rw [P.endpointIndexedCriticalProfile_affineNumerator_eq hp] at h
  rw [← P.length_eq_criticalTwoDepth] at h
  exact h

/--
Stage 6 の exact `B = D*R + 2^H*Q` identity。
ここでは `D` を符号付きの `2^H - 3^p` として書き、standard path の座標だけを使う。
-/
theorem endpointIndexedProfile_affineConst_eq_gap_start_add_twoPow_gap
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount) :
    (affineConst P.word : ℤ) =
      ((2 : ℤ) ^ P.length - (3 : ℤ) ^ P.endpointOddCount) *
          (Critical.profileCanonicalStart
            (P.endpointIndexedCriticalProfile hp) : ℤ) +
        (2 : ℤ) ^ P.length *
          Critical.profileCanonicalGap (P.endpointIndexedCriticalProfile hp) := by
  have h :=
    Critical.profileAffineNumerator_eq_gap_start_add_twoPow_gap
      (P.endpointIndexedCriticalProfile hp)
  rw [P.endpointIndexedCriticalProfile_affineNumerator_eq hp] at h
  rw [← P.length_eq_criticalTwoDepth] at h
  exact h

/--
compressed word の odd-endpoint canonical pair 自身も、元 standard parity path を exact に実現する。
-/
theorem compressedCanonicalPair_trace
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount) :
    TraceRealizes P.word
      (Word.canonicalStart P.compressedExponentWord)
      (Word.canonicalEnd P.compressedExponentWord) := by
  have hAff :
      AffineRealizes
        (expandWord P.compressedExponentWord)
        (Word.canonicalStart P.compressedExponentWord)
        (Word.canonicalEnd P.compressedExponentWord) :=
    (affineRealizes_expandWord_iff_wordEndpointEquation
      (P.compressedExponentWord_valid hp)
      (Word.canonicalStart P.compressedExponentWord)
      (Word.canonicalEnd P.compressedExponentWord)).2
      (Word.canonical_endpointEquation P.compressedExponentWord)
  have hTrace := hAff.trace
  rw [P.expandWord_compressedExponentWord hp] at hTrace
  exact hTrace

/--
compressed canonical `R,Y` は actual odd-only first-passage 自身も実現する。
-/
theorem compressedCanonicalPair_actualFirstPassage
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount) :
    ActualFirstPassage P.compressedExponentWord
      (Word.canonicalStart P.compressedExponentWord)
      (Word.canonicalEnd P.compressedExponentWord) := by
  exact
    P.actualFirstPassage_of_trace_oddEndpoint
      hp
      (P.compressedCanonicalPair_trace hp)
      (Word.canonicalEnd_odd P.compressedExponentWord)

/--
odd-endpoint canonical modulus `2^(H+1)` は standard parity modulus `2^H` の exactly 2 倍。
-/
theorem compressedOddEndpointModulus_eq_two_mul_parityModulus
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount) :
    Word.oddEndpointModulus P.compressedExponentWord =
      2 * parityModulus P.word := by
  calc
    Word.oddEndpointModulus P.compressedExponentWord
        = 2 ^ (Word.twoSteps P.compressedExponentWord + 1) :=
          Word.oddEndpointModulus_eq P.compressedExponentWord
    _ = 2 ^ (P.length + 1) := by
          rw [P.compressedExponentWord_twoSteps_eq hp]
    _ = 2 * 2 ^ P.length := by
          rw [pow_succ]
          ring
    _ = 2 * parityModulus P.word := by
          rfl

/--
modulus が 2 倍になるため、compressed word の canonical pair は standard canonical pair の
0-th lift または 1st lift のどちらかに入る。
-/
theorem compressedCanonicalPair_eq_standardLift_zero_or_one
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount) :
    (Word.canonicalStart P.compressedExponentWord =
        leastRepresentative P.word ∧
      Word.canonicalEnd P.compressedExponentWord =
        canonicalEndpoint P.word) ∨
    (Word.canonicalStart P.compressedExponentWord =
        leastRepresentative P.word + parityModulus P.word ∧
      Word.canonicalEnd P.compressedExponentWord =
        canonicalEndpoint P.word + 3 ^ P.endpointOddCount) := by
  have hTrace := P.compressedCanonicalPair_trace hp
  rcases hTrace.exists_lift with ⟨k, hStart, hEnd⟩
  have hUpper :
      Word.canonicalStart P.compressedExponentWord <
        2 * parityModulus P.word := by
    have h := Word.canonicalStart_lt_modulus P.compressedExponentWord
    rw [P.compressedOddEndpointModulus_eq_two_mul_parityModulus hp] at h
    exact h
  have hklt : k < 2 := by
    by_contra hNot
    have hk2 : 2 ≤ k := by omega
    have hMul :
        parityModulus P.word * 2 ≤ parityModulus P.word * k :=
      Nat.mul_le_mul_left (parityModulus P.word) hk2
    have hLower :
        2 * parityModulus P.word ≤
          Word.canonicalStart P.compressedExponentWord := by
      rw [hStart]
      omega
    omega
  have hk01 : k = 0 ∨ k = 1 := by omega
  rcases hk01 with rfl | rfl
  · exact Or.inl ⟨by simpa using hStart, by simpa using hEnd⟩
  · exact Or.inr ⟨
      by simpa using hStart,
      by
        change
          P.compressedExponentWord.canonicalEnd =
            canonicalEndpoint P.word + 3 ^ oddCount P.word
        simpa using hEnd
    ⟩

/--
path-wise single-lift 条件のもとで非下降かつ odd endpoint の standard realization は、
compressed word の canonical `R,Y` そのもの。
-/
theorem nondecreasing_oddEndpoint_eq_compressedCanonicalPair
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount)
    (hSingle : P.SingleLiftGapCondition)
    {x y : ℕ}
    (h : TraceRealizes P.word x y)
    (hxy : x ≤ y)
    (hy : Odd y) :
    x = Word.canonicalStart P.compressedExponentWord ∧
      y = Word.canonicalEnd P.compressedExponentWord := by
  have hx0 : x = leastRepresentative P.word :=
    P.nondecreasing_trace_start_eq_leastRepresentative hSingle h hxy
  have hEq := P.compressedEndpointEquation_of_trace hp h
  have hRle : Word.canonicalStart P.compressedExponentWord ≤ x :=
    hEq.canonicalStart_le_start hy
  rcases P.compressedCanonicalPair_eq_standardLift_zero_or_one hp with
      hZero | hOne
  · rcases hZero with ⟨hR, hY⟩
    have hy0 : y = canonicalEndpoint P.word :=
      h.end_eq_canonicalEndpoint_of_start_eq_leastRepresentative hx0
    constructor
    · exact hx0.trans hR.symm
    · exact hy0.trans hY.symm
  · rcases hOne with ⟨hR, hY⟩
    have hMpos : 0 < parityModulus P.word := by
      unfold parityModulus
      positivity
    rw [hR, hx0] at hRle
    omega

/-- 非下降 odd-endpoint survivor の canonical drift `Q` は非負。 -/
theorem compressedCanonicalGap_nonneg_of_nondecreasing_oddEndpoint
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount)
    (hSingle : P.SingleLiftGapCondition)
    {x y : ℕ}
    (h : TraceRealizes P.word x y)
    (hxy : x ≤ y)
    (hy : Odd y) :
    0 ≤ Word.canonicalGap P.compressedExponentWord := by
  rcases
      P.nondecreasing_oddEndpoint_eq_compressedCanonicalPair
        hp hSingle h hxy hy
    with ⟨hx, hyEq⟩
  have hRY :
      Word.canonicalStart P.compressedExponentWord ≤
        Word.canonicalEnd P.compressedExponentWord := by
    rw [← hx, ← hyEq]
    exact hxy
  change
    (0 : ℤ) ≤
      (Word.canonicalEnd P.compressedExponentWord : ℤ) -
        (Word.canonicalStart P.compressedExponentWord : ℤ)
  exact sub_nonneg.mpr (by exact_mod_cast hRY)

/--
Stage 6 の endpoint-indexed profile 最終形。
非下降 odd-endpoint survivor は profile canonical `R,Y` に一致し、`Q ≥ 0`。
-/
theorem nondecreasing_oddEndpoint_eq_endpointIndexedProfileCanonical
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount)
    (hSingle : P.SingleLiftGapCondition)
    {x y : ℕ}
    (h : TraceRealizes P.word x y)
    (hxy : x ≤ y)
    (hy : Odd y) :
    x = Critical.profileCanonicalStart (P.endpointIndexedCriticalProfile hp) ∧
      y = Critical.profileCanonicalEnd (P.endpointIndexedCriticalProfile hp) ∧
      0 ≤ Critical.profileCanonicalGap (P.endpointIndexedCriticalProfile hp) := by
  have hPair :=
    P.nondecreasing_oddEndpoint_eq_compressedCanonicalPair
      hp hSingle h hxy hy
  have hR := P.compressedCanonicalStart_eq_endpointIndexedProfile hp
  have hY := P.compressedCanonicalEnd_eq_endpointIndexedProfile hp
  have hQ :=
    P.compressedCanonicalGap_nonneg_of_nondecreasing_oddEndpoint
      hp hSingle h hxy hy
  rw [P.compressedCanonicalGap_eq_endpointIndexedProfile hp] at hQ
  exact ⟨hPair.1.trans hR, hPair.2.trans hY, hQ⟩

/--
Stage 4 の universal critical-gap interface を仮定した wrapper。
この場合、個別 path の single-lift 条件を別途渡す必要はない。
-/
theorem nondecreasing_oddEndpoint_eq_endpointIndexedProfileCanonical_of_criticalGapLinearBound
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount)
    (hGap : Arithmetic.CriticalGapLinearBound)
    {x y : ℕ}
    (h : TraceRealizes P.word x y)
    (hxy : x ≤ y)
    (hy : Odd y) :
    x = Critical.profileCanonicalStart (P.endpointIndexedCriticalProfile hp) ∧
      y = Critical.profileCanonicalEnd (P.endpointIndexedCriticalProfile hp) ∧
      0 ≤ Critical.profileCanonicalGap (P.endpointIndexedCriticalProfile hp) := by
  exact
    P.nondecreasing_oddEndpoint_eq_endpointIndexedProfileCanonical
      hp
      (P.singleLiftGapCondition_of_criticalGapLinearBound hGap)
      h hxy hy

end FirstPassagePath
end CSTMicro
end Collatz3
