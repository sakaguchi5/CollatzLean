import CollatzLean.Collatz2.Global.CanonicalEndpointFloorContractingReturn

/-!
# Collatz2 Global: endpoint-floor return の natural coordinates

`CanonicalEndpointFloorContractingReturn` から、旧 branch packet を介さず

* whole word は `1 :: v`
* canonical return half-gap `n > 0`
* first boundary と endpoint の half-gap `d > 0`

を直接抽出する。

座標は exact に

  S + 1 = 4 * (n + d)
  s + 1 = 6 * (n + d)
  T + 1 = 6 * n + 4 * d

となる。

ここで

* `S = canonicalStart(1::v)`
* `s` = actual first boundary
* `T = canonicalEnd(1::v)`

である。
-/

namespace Collatz2
namespace OddOrbit
namespace CanonicalEndpointFloorContractingReturn

/-- endpoint-floor return の natural coordinate packet。 -/
structure NaturalCoordinates
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O) where
  tail : Word
  word_eq : D.word = 1 :: tail
  tail_nonempty : tail ≠ []

  n : ℕ
  d : ℕ
  n_pos : 0 < n
  d_pos : 0 < d

  boundary : ℕ
  boundary_eq :
    boundary = O.value (D.startIndex + 1)

  fullEnd_eq :
    Word.canonicalEnd D.word =
      Word.canonicalStart D.word + 2 * n

  boundary_eq_fullEnd_add :
    boundary =
      Word.canonicalEnd D.word + 2 * d

  fullStart_add_one :
    Word.canonicalStart D.word + 1 =
      4 * (n + d)

  boundary_add_one :
    boundary + 1 =
      6 * (n + d)

  fullEnd_add_one :
    Word.canonicalEnd D.word + 1 =
      6 * n + 4 * d

namespace NaturalCoordinates

/-- tail の odd-step 数は whole より1小さい。 -/
theorem tail_length_add_one
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (N : NaturalCoordinates D) :
    N.tail.length + 1 = D.word.length := by
  rw [N.word_eq]
  simp

/-- actual first boundary は terminal endpoint より上。 -/
theorem fullEnd_lt_boundary
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (N : NaturalCoordinates D) :
    Word.canonicalEnd D.word < N.boundary := by
  rw [N.boundary_eq_fullEnd_add]
  have hd := N.d_pos
  omega

end NaturalCoordinates

/--
canonical-positive all-suffix budget から、whole length は少なくとも2。
実際には `p = 6*n + sigma` なので `p >= 7`。
-/
theorem word_length_gt_one
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O) :
    1 < D.word.length := by
  obtain ⟨n, sigma, hn, hsigma, _hreturn, hp, _hbudget⟩ :=
    D.exists_halfGap_sigma_budgetIdentity
  have hp' :
      D.word.length = 6 * n + sigma := by
    simpa [Word.oddSteps] using hp
  omega

/-- endpoint-floor return の先頭 exponent は1。 -/
theorem firstExponent_eq_one
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O) :
    O.exponent D.startIndex = 1 := by
  have hlen : 1 < D.word.length :=
    D.word_length_gt_one
  have hF : Word.FirstCrossing D.word := by
    simpa [word] using D.firstCrossing
  have hOnePos : 0 < (1 : ℕ) := by
    omega
  have hExp :
      Word.Expanding (D.word.take 1) :=
    hF.properExpanding
      hOnePos
      hlen
  have htake :
      D.word.take 1 =
        [O.exponent D.startIndex] := by
    have hlenD : 1 ≤ D.length := by
      have h := D.length_pos
      omega
    calc
      D.word.take 1
          = (O.segment D.startIndex D.length).take 1 := by
              rfl
      _ = O.segment D.startIndex 1 :=
        O.segment_take_of_le hlenD
      _ = [O.exponent D.startIndex] := by
        simp
  have hpow :
      2 ^ O.exponent D.startIndex < 3 := by
    rw [Word.expanding_iff_twoPow_lt_threePow] at hExp
    rw [htake] at hExp
    simpa [Word.twoSteps, Word.oddSteps] using hExp
  have hePos := O.exponent_pos D.startIndex
  by_contra hne
  have heTwo : 2 ≤ O.exponent D.startIndex := by
    omega
  have hmono :
      2 ^ 2 ≤ 2 ^ O.exponent D.startIndex :=
    Nat.pow_le_pow_right
      (by omega : 0 < (2 : ℕ)) heTwo
  norm_num at hmono
  omega

/-- whole word を actual tail と `1 :: tail` に分解する。 -/
theorem exists_prependOne_tail
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O) :
    ∃ v : Word,
      D.word = 1 :: v ∧
      v ≠ [] := by
  let v :=
    O.segment (D.startIndex + 1) (D.length - 1)
  have hlen : 1 < D.length := by
    have h := D.word_length_gt_one
    simpa [D.word_length] using h
  have hlenEq :
      D.length = (D.length - 1) + 1 := by
    omega
  have hword :
      D.word =
        O.exponent D.startIndex :: v := by
    unfold word v
    rw [hlenEq]
    simp
  have he := D.firstExponent_eq_one
  have hwordOne :
      D.word = 1 :: v := by
    rw [hword, he]
  have hvne : v ≠ [] := by
    apply List.ne_nil_of_length_pos
    simp [v]
    omega
  exact ⟨v, hwordOne, hvne⟩

/--
endpoint-floor return から natural coordinates を構成する。
-/
noncomputable def toNaturalCoordinates
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O) :
    NaturalCoordinates D := by
  classical
  let H :=
    D.exists_halfGap_sigma_budgetIdentity
  let n : ℕ :=
    Classical.choose H
  let Hsigma :=
    Classical.choose_spec H
  let sigma :=
    Classical.choose Hsigma
  have hPack :=
    Classical.choose_spec Hsigma
  have hn :=
    hPack.1
  have hreturn :=
    hPack.2.2.1
  let Hv :=
    D.exists_prependOne_tail
  let v : Word :=
    Classical.choose Hv
  have hvPack :=
    Classical.choose_spec Hv
  have hword :=
    hvPack.1
  have hvne :=
    hvPack.2
  let boundary := O.value (D.startIndex + 1)
  have hlen : 1 < D.length := by
    have h := D.word_length_gt_one
    simpa [D.word_length] using h
  have hfloorActual :
      O.value (D.startIndex + D.length) <
        boundary := by
    dsimp [boundary]
    exact D.endpointFloor 1 (by omega) hlen
  have hEndActual :
      O.value (D.startIndex + D.length) =
        Word.canonicalEnd D.word := by
    simpa [word] using D.endCanonical
  have hfloor :
      Word.canonicalEnd D.word < boundary := by
    rw [← hEndActual]
    exact hfloorActual
  let Ha :=
    O.value_odd (D.startIndex + 1)
  let a : ℕ :=
    Classical.choose Ha
  have ha :=
    Classical.choose_spec Ha
  let Hb :=
    Word.canonicalEnd_odd D.word
  let b : ℕ :=
    Classical.choose Hb
  have hb :=
    Classical.choose_spec Hb
  have hba : b < a := by
    omega
  let d := a - b
  have hd : 0 < d := by
    dsimp [d]
    omega
  have hboundary :
      boundary =
        Word.canonicalEnd D.word + 2 * d := by
    dsimp [boundary, d] at *
    omega
  have he := D.firstExponent_eq_one
  have hstepOrbit := O.step D.startIndex
  have hStartActual :
      O.value D.startIndex =
        Word.canonicalStart D.word := by
    simpa [word] using D.startCanonical
  have hstep :
      2 * boundary =
        3 * Word.canonicalStart D.word + 1 := by
    dsimp [boundary]
    rw [he] at hstepOrbit
    norm_num at hstepOrbit
    rw [hStartActual] at hstepOrbit
    exact hstepOrbit
  have hStartCoord :
      Word.canonicalStart D.word + 1 =
        4 * (n + d) := by
    omega
  have hBoundaryCoord :
      boundary + 1 =
        6 * (n + d) := by
    omega
  have hEndCoord :
      Word.canonicalEnd D.word + 1 =
        6 * n + 4 * d := by
    omega
  exact {
    tail := v
    word_eq := hword
    tail_nonempty := hvne
    n := n
    d := d
    n_pos := hn
    d_pos := hd
    boundary := boundary
    boundary_eq := rfl
    fullEnd_eq := hreturn
    boundary_eq_fullEnd_add := hboundary
    fullStart_add_one := hStartCoord
    boundary_add_one := hBoundaryCoord
    fullEnd_add_one := hEndCoord
  }

end CanonicalEndpointFloorContractingReturn
end OddOrbit
end Collatz2
