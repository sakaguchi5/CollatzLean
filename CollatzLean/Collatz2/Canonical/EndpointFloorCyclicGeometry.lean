import CollatzLean.Collatz2.Global.CanonicalEndpointFloorContractingReturn
import CollatzLean.Collatz2.Geometry.RankPath
import CollatzLean.Collatz2.Geometry.CyclicCenter
import Mathlib.Tactic.Positivity

/-!
# Collatz2 Canonical: endpoint-floor cyclic geometry

current A `CanonicalEndpointFloorContractingReturn` に対して

1. canonical positive return の center-shadow exact form
2. 任意 proper cut の actual prefix/suffix realization
3. 全 cut cyclic translation identity
4. endpoint floor による original translation の strict cyclic minimality

をまとめる。

FutureMinimum endpoint は一切使わない。
-/

namespace Collatz2
namespace OddOrbit
namespace CanonicalEndpointFloorContractingReturn

/-- cut prefix。 -/
def cutPrefix
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O)
    (k : ℕ) : Word :=
  D.word.take k

/-- cut suffix。 -/
def cutSuffix
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O)
    (k : ℕ) : Word :=
  D.word.drop k

/-- cut cyclic rotation。 -/
def cutRotation
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O)
    (k : ℕ) : Word :=
  D.cutSuffix k ++ D.cutPrefix k

/-- generic `Word.cyclicRotate` との一致。 -/
theorem cutRotation_eq_cyclicRotate
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O)
    (k : ℕ) :
    D.cutRotation k = Word.cyclicRotate D.word k := by
  rfl

/-- cut prefix は actual orbit segment。 -/
theorem cutPrefix_eq_segment
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O)
    {k : ℕ}
    (hk : k ≤ D.length) :
    D.cutPrefix k = O.segment D.startIndex k := by
  unfold cutPrefix word
  exact O.segment_take_of_le hk

/-- cut suffix も actual orbit segment。 -/
theorem cutSuffix_eq_segment
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O)
    {k : ℕ}
    (hk : k ≤ D.length) :
    D.cutSuffix k =
      O.segment (D.startIndex + k) (D.length - k) := by
  have hsum : k + (D.length - k) = D.length := by
    omega
  have hTakeDrop :
      D.word = D.cutPrefix k ++ D.cutSuffix k := by
    simp only [cutPrefix, cutSuffix, List.take_append_drop]
  have hSegment :=
    O.segment_add D.startIndex k (D.length - k)
  rw [hsum] at hSegment
  have hSegment' :
      D.word =
        D.cutPrefix k ++
          O.segment (D.startIndex + k) (D.length - k) := by
    rw [D.cutPrefix_eq_segment hk]
    simpa [word] using hSegment
  have hEq :
      D.cutPrefix k ++ D.cutSuffix k =
        D.cutPrefix k ++
          O.segment (D.startIndex + k) (D.length - k) :=
    hTakeDrop.symm.trans hSegment'
  have hDrop :=
    congrArg (List.drop (D.cutPrefix k).length) hEq
  simpa using hDrop

/-- cut prefix の actual realization。 -/
theorem cutPrefixRealizes
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O)
    {k : ℕ}
    (hk : k ≤ D.length) :
    Word.Realizes
      (D.cutPrefix k)
      (O.value D.startIndex)
      (O.value (D.startIndex + k)) := by
  rw [D.cutPrefix_eq_segment hk]
  exact O.realizesSegment D.startIndex k

/-- current A proper cut の rational chord rank は strict positive。 -/
theorem cutChordRank_pos
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O)
    {k : ℕ}
    (hkPos : 0 < k)
    (hkLt : k < D.length) :
    0 < Word.chordRank D.word k := by
  have hkLt' : k < Word.oddSteps D.word := by
    simpa [Word.oddSteps, D.word_length] using hkLt
  have hF : Word.FirstCrossing D.word := by
    simpa [word] using D.firstCrossing
  exact hF.chordRank_pos hkPos hkLt'

/-- cut prefix の odd-step 数は cut index そのもの。 -/
theorem cutPrefix_oddSteps_eq
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O)
    {k : ℕ}
    (hk : k ≤ D.length) :
    Word.oddSteps (D.cutPrefix k) = k := by
  rw [D.cutPrefix_eq_segment hk]
  simp [Word.oddSteps]

/-- cut suffix の actual realization。 -/
theorem cutSuffixRealizes
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O)
    {k : ℕ}
    (hk : k ≤ D.length) :
    Word.Realizes
      (D.cutSuffix k)
      (O.value (D.startIndex + k))
      (O.value D.endIndex) := by
  rw [D.cutSuffix_eq_segment hk]
  have h :=
    O.realizesSegment (D.startIndex + k) (D.length - k)
  have hIndex :
      D.startIndex + k + (D.length - k) = D.endIndex := by
    dsimp [endIndex]
    omega
  rw [hIndex] at h
  exact h

/-! ## 3. canonical start = center の 2-adic shadow -/

/--
canonical positive return の center-shadow packet。

  T = S + 2*n
  B = G*S + 2^(H+1)*n.

したがって projective center `B/G` は canonical start `S` の右側にあり、
その差の numerator は canonical residue modulus の正倍である。
-/
structure CenterShadowData
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O) where
  n : ℕ
  n_pos : 0 < n
  endpoint_eq :
    Word.canonicalEnd D.word =
      Word.canonicalStart D.word + 2 * n
  translate_eq :
    Word.affineConst D.word =
      (AffineTransfer.ofWord D.word).centerGap *
          Word.canonicalStart D.word +
        Word.residueModulus D.word * n

/-- current A から center-shadow packet を無条件に構成する。 -/
noncomputable def toCenterShadowData
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O) :
    CenterShadowData D := by
  classical
  have hExists :=
    D.allSuffixesContracting.exists_canonicalHalfGap_and_exactBalance
      D.word_valid D.word_nonempty D.canonicalPositive
  let n : ℕ := Classical.choose hExists
  have hSpec := Classical.choose_spec hExists
  rcases hSpec with ⟨hn, hEnd, hB⟩
  exact {
    n := n
    n_pos := hn
    endpoint_eq := hEnd
    translate_eq := by
      simpa [Word.residueModulus] using hB
  }

namespace CenterShadowData

/-- actual endpoint も同じ half-gap coordinate。 -/
theorem actualEnd_eq_start_add_two_mul_n
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (L : CenterShadowData D) :
    O.value D.endIndex = O.value D.startIndex + 2 * L.n := by
  calc
    O.value D.endIndex
        = Word.canonicalEnd D.word := by
            simpa [endIndex, word] using D.endCanonical
    _ = Word.canonicalStart D.word + 2 * L.n := L.endpoint_eq
    _ = O.value D.startIndex + 2 * L.n := by
          simpa [word] using
            congrArg (fun z => z + 2 * L.n) D.startCanonical.symm

/-- center gap modulus 上では translation は residue-modulus shift だけを残す。 -/
theorem translate_cast_eq_residueModulus_mul_n
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (L : CenterShadowData D) :
    ((Word.affineConst D.word : ℕ) :
        ZMod (AffineTransfer.ofWord D.word).centerGap) =
      ((Word.residueModulus D.word * L.n : ℕ) :
        ZMod (AffineTransfer.ofWord D.word).centerGap) := by
  have hCast :=
    congrArg
      (fun z : ℕ =>
        (z : ZMod (AffineTransfer.ofWord D.word).centerGap))
      L.translate_eq
  simpa using hCast

/--
whole gap modulus 上で canonical residue modulus は `2*3^p` と同じ。
-/
theorem residueModulus_cast_eq_two_mul_threePow
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O} :
    ((Word.residueModulus D.word : ℕ) :
        ZMod (AffineTransfer.ofWord D.word).centerGap) =
      ((2 * 3 ^ Word.oddSteps D.word : ℕ) :
        ZMod (AffineTransfer.ofWord D.word).centerGap) := by
  let G := (AffineTransfer.ofWord D.word).centerGap
  have hPow :
      3 ^ Word.oddSteps D.word < 2 ^ Word.twoSteps D.word :=
    (Word.contracting_iff_threePow_lt_twoPow).1 D.contracting
  have hGapNat :
      G + 3 ^ Word.oddSteps D.word =
        2 ^ Word.twoSteps D.word := by
    dsimp [G]
    unfold AffineTransfer.centerGap
    simp only [AffineTransfer.ofWord_twoCoeff, AffineTransfer.ofWord_oddCoeff]
    exact Nat.sub_add_cancel (Nat.le_of_lt hPow)
  have hCast :=
    congrArg (fun z : ℕ => (z : ZMod G)) hGapNat
  have hTwoPow :
      ((2 ^ Word.twoSteps D.word : ℕ) : ZMod G) =
        ((3 ^ Word.oddSteps D.word : ℕ) : ZMod G) := by
    simpa using hCast.symm
  change
    ((2 ^ (Word.twoSteps D.word + 1) : ℕ) : ZMod G) =
      ((2 * 3 ^ Word.oddSteps D.word : ℕ) : ZMod G)
  rw [pow_succ]
  push_cast at hTwoPow ⊢
  rw [hTwoPow]
  ring

/--
Small-residue equation の current A 版。

  B ≡ 2*3^p*n (mod G).
-/
theorem translate_cast_eq_smallResidue
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (L : CenterShadowData D) :
    ((Word.affineConst D.word : ℕ) :
        ZMod (AffineTransfer.ofWord D.word).centerGap) =
      ((2 * 3 ^ Word.oddSteps D.word * L.n : ℕ) :
        ZMod (AffineTransfer.ofWord D.word).centerGap) := by
  rw [L.translate_cast_eq_residueModulus_mul_n]
  push_cast
  rw [residueModulus_cast_eq_two_mul_threePow]
  push_cast
  ring

/-- center numerator は canonical start を strict に越える。 -/
theorem gap_mul_start_lt_translate
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (L : CenterShadowData D) :
    (AffineTransfer.ofWord D.word).centerGap *
        Word.canonicalStart D.word <
      Word.affineConst D.word := by
  rw [L.translate_eq]
  have hM : 0 < Word.residueModulus D.word := Word.residueModulus_pos D.word
  have hExtra : 0 < Word.residueModulus D.word * L.n :=
    Nat.mul_pos hM L.n_pos
  omega

end CenterShadowData

/-! ## 4. 全 cut exact identity -/

/--
current A の任意 proper cut に generic cyclic identity を適用した版。

`X_k` を cut boundary、`T` を terminal とすると

  B(rot_k)-B
    = 2*n*3^k*(2^H_suffix-3^p_suffix)
      +(2^H-3^p)*(X_k-T).
-/
theorem cutRotation_translate_sub_exact
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (L : CenterShadowData D)
    {k : ℕ}
    (hkLt : k < D.length) :
    ((Word.affineConst (D.cutRotation k) : ℕ) : ℤ) -
        ((Word.affineConst D.word : ℕ) : ℤ) =
      (2 * L.n : ℤ) *
          ((3 : ℤ) ^ Word.oddSteps (D.cutPrefix k)) *
          (((2 : ℤ) ^ Word.twoSteps (D.cutSuffix k)) -
            ((3 : ℤ) ^ Word.oddSteps (D.cutSuffix k))) +
        (((2 : ℤ) ^ Word.twoSteps D.word) -
            ((3 : ℤ) ^ Word.oddSteps D.word)) *
          ((O.value (D.startIndex + k) : ℤ) -
            (O.value D.endIndex : ℤ)) := by
  have hkLe : k ≤ D.length := Nat.le_of_lt hkLt
  have hGeneric :=
    Word.cyclicTranslate_sub_exact
      (D.cutPrefixRealizes hkLe)
      (D.cutSuffixRealizes hkLe)
      L.actualEnd_eq_start_add_two_mul_n
  have hWord :
      D.cutPrefix k ++ D.cutSuffix k = D.word := by
    simp [cutPrefix, cutSuffix]
  rw [hWord] at hGeneric
  simpa [cutRotation] using hGeneric

/-! ## 1. FirstCrossing + endpointFloor -> cyclic translation strict minimum -/

/-- proper cut suffix は contracting。 -/
theorem cutSuffix_contracting
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O)
    {k : ℕ}
    (hkLt : k < D.length) :
    Word.Contracting (D.cutSuffix k) := by
  have hkLtWord : k < D.word.length := by
    simpa [D.word_length] using hkLt
  have hneg := D.allSuffixesContracting k hkLtWord
  have hC := (Word.suffixDeterminant_neg_iff_contracting).1 hneg
  simpa [cutSuffix] using hC

/--
全 proper cyclic rotation の translation は original translation より strict に大きい。
これは endpointFloor を cyclic center geometry に変換する主要定理。
-/
theorem affineConst_lt_cutRotation
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O)
    {k : ℕ}
    (hkPos : 0 < k)
    (hkLt : k < D.length) :
    Word.affineConst D.word < Word.affineConst (D.cutRotation k) := by
  let L := D.toCenterShadowData
  have hEq :=
    cutRotation_translate_sub_exact L hkLt
  have hSuffixC : Word.Contracting (D.cutSuffix k) :=
    D.cutSuffix_contracting hkLt
  have hSuffixPow :
      3 ^ Word.oddSteps (D.cutSuffix k) <
        2 ^ Word.twoSteps (D.cutSuffix k) :=
    (Word.contracting_iff_threePow_lt_twoPow).1 hSuffixC
  have hSuffixPowZ :
      ((3 : ℤ) ^ Word.oddSteps (D.cutSuffix k)) <
        ((2 : ℤ) ^ Word.twoSteps (D.cutSuffix k)) := by
    exact_mod_cast hSuffixPow
  have hSuffixGapZ :
      (0 : ℤ) <
        ((2 : ℤ) ^ Word.twoSteps (D.cutSuffix k)) -
          ((3 : ℤ) ^ Word.oddSteps (D.cutSuffix k)) := by
    exact sub_pos.mpr hSuffixPowZ
  have hWholePow :
      3 ^ Word.oddSteps D.word <
        2 ^ Word.twoSteps D.word :=
    (Word.contracting_iff_threePow_lt_twoPow).1 D.contracting
  have hWholePowZ :
      ((3 : ℤ) ^ Word.oddSteps D.word) <
        ((2 : ℤ) ^ Word.twoSteps D.word) := by
    exact_mod_cast hWholePow
  have hWholeGapZ :
      (0 : ℤ) <
        ((2 : ℤ) ^ Word.twoSteps D.word) -
          ((3 : ℤ) ^ Word.oddSteps D.word) := by
    exact sub_pos.mpr hWholePowZ
  have hFloor :
      O.value D.endIndex < O.value (D.startIndex + k) := by
    simpa [endIndex] using D.endpointFloor k hkPos hkLt
  have hFloorZ :
      (O.value D.endIndex : ℤ) <
        (O.value (D.startIndex + k) : ℤ) := by
    exact_mod_cast hFloor
  have hBoundaryZ :
      (0 : ℤ) <
        (O.value (D.startIndex + k) : ℤ) -
          (O.value D.endIndex : ℤ) := by
    exact sub_pos.mpr hFloorZ
  have hnPosZ : (0 : ℤ) < (L.n : ℤ) := by
    exact_mod_cast L.n_pos
  have hnZ : (0 : ℤ) < 2 * (L.n : ℤ) := by
    exact mul_pos (by norm_num) hnPosZ
  have hThreeZ :
      (0 : ℤ) < (3 : ℤ) ^ Word.oddSteps (D.cutPrefix k) := by
    positivity
  have hFirstTerm :
      (0 : ℤ) <
        (2 * L.n : ℤ) *
          ((3 : ℤ) ^ Word.oddSteps (D.cutPrefix k)) *
          (((2 : ℤ) ^ Word.twoSteps (D.cutSuffix k)) -
            ((3 : ℤ) ^ Word.oddSteps (D.cutSuffix k))) := by
    exact mul_pos (mul_pos hnZ hThreeZ) hSuffixGapZ
  have hSecondTerm :
      (0 : ℤ) <
        (((2 : ℤ) ^ Word.twoSteps D.word) -
          ((3 : ℤ) ^ Word.oddSteps D.word)) *
          ((O.value (D.startIndex + k) : ℤ) -
            (O.value D.endIndex : ℤ)) := by
    exact mul_pos hWholeGapZ hBoundaryZ
  have hDiff :
      (0 : ℤ) <
        ((Word.affineConst (D.cutRotation k) : ℕ) : ℤ) -
          ((Word.affineConst D.word : ℕ) : ℤ) := by
    rw [hEq]
    exact add_pos hFirstTerm hSecondTerm
  have hCast :
      ((Word.affineConst D.word : ℕ) : ℤ) <
        ((Word.affineConst (D.cutRotation k) : ℕ) : ℤ) := by
    exact sub_pos.mp hDiff
  exact_mod_cast hCast

/--
center gap は rotation で保存されるため、translation strict minimum は
negative projective center の strict minimum でもある。
-/
theorem centerRises_to_cutRotation
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O)
    {k : ℕ}
    (hkPos : 0 < k)
    (hkLt : k < D.length) :
    (AffineTransfer.ofWord D.word).CenterRises
      (AffineTransfer.ofWord (D.cutRotation k)) := by
  have hB := D.affineConst_lt_cutRotation hkPos hkLt
  have hDet :
      (AffineTransfer.ofWord (D.cutRotation k)).determinant =
        (AffineTransfer.ofWord D.word).determinant := by
    rw [D.cutRotation_eq_cyclicRotate]
    exact Word.determinant_cyclicRotate D.word k
  have hNeg :
      (AffineTransfer.ofWord D.word).determinant < 0 := D.contracting
  have hGapPos :
      (0 : ℤ) < -((AffineTransfer.ofWord D.word).determinant) := by
    omega
  unfold AffineTransfer.CenterRises
  rw [hDet]
  change
    (Word.affineConst D.word : ℤ) *
        (-((AffineTransfer.ofWord D.word).determinant)) <
      (Word.affineConst (D.cutRotation k) : ℤ) *
        (-((AffineTransfer.ofWord D.word).determinant))
  have hBZ :
      (Word.affineConst D.word : ℤ) <
        (Word.affineConst (D.cutRotation k) : ℤ) := by
    exact_mod_cast hB
  exact (Int.mul_lt_mul_right hGapPos).2 hBZ

end CanonicalEndpointFloorContractingReturn
end OddOrbit
end Collatz2
