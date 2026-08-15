import CollatzLean.Collatz2.Geometry.BestUpperSlope
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Collatz2 Geometry: primitive best-upper normalization

Stage 2。

contracting exponent pair `P=(p,H)` の content

  g = gcd(p,H)

を除いた pair

  P₀ = (p/g, H/g)

を exponent-slope の primitive form とする。

* contracting を保存
* slope を exact に保存
* `StripReduced` / best-upper 性を保存
* `gcd(H₀,p₀)=1`

を証明する。

primitive + StripReduced pair では proper strip rank は

  1 <= stripRank(r) < p

かつ residue が pairwise distinct であり、実際に `1,...,p-1` を一度ずつ取る。
-/

namespace Collatz2
namespace Word
namespace ContractingExponentPair

/-- exponent pair の content。 -/
def exponentContent (P : ContractingExponentPair) : ℕ :=
  Nat.gcd P.oddCount P.twoDepth

/-- content を除いた odd denominator。 -/
def primitiveOddCount (P : ContractingExponentPair) : ℕ :=
  P.oddCount / P.exponentContent

/-- content を除いた two-depth。 -/
def primitiveTwoDepth (P : ContractingExponentPair) : ℕ :=
  P.twoDepth / P.exponentContent

/-- exponent pair の primitive 性。 -/
def IsPrimitive (P : ContractingExponentPair) : Prop :=
  Nat.Coprime P.twoDepth P.oddCount

/-- contracting pair では two-depth も正。 -/
theorem twoDepth_pos (P : ContractingExponentPair) :
    0 < P.twoDepth := by
  by_contra hnot
  have hzero : P.twoDepth = 0 := by omega
  have hThreePos : 0 < 3 ^ P.oddCount :=
    Nat.pow_pos (by omega)
  have hCon := P.contracting
  rw [hzero, pow_zero] at hCon
  omega

/-- exponent content は正。 -/
theorem exponentContent_pos (P : ContractingExponentPair) :
    0 < P.exponentContent := by
  unfold exponentContent
  exact Nat.gcd_pos_of_pos_right P.oddCount P.twoDepth_pos

/-- `g * (p/g) = p`。 -/
theorem exponentContent_mul_primitiveOddCount
    (P : ContractingExponentPair) :
    P.exponentContent * P.primitiveOddCount = P.oddCount := by
  unfold exponentContent primitiveOddCount
  exact Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)

/-- `g * (H/g) = H`。 -/
theorem exponentContent_mul_primitiveTwoDepth
    (P : ContractingExponentPair) :
    P.exponentContent * P.primitiveTwoDepth = P.twoDepth := by
  unfold exponentContent primitiveTwoDepth
  exact Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)

/-- primitive denominator は正。 -/
theorem primitiveOddCount_pos (P : ContractingExponentPair) :
    0 < P.primitiveOddCount := by
  have hOddPos : 0 < P.oddCount :=
    P.oddCount_pos
  have hEq := P.exponentContent_mul_primitiveOddCount
  by_contra hnot
  have hzero : P.primitiveOddCount = 0 := by
    omega
  rw [hzero, mul_zero] at hEq
  omega
/--
content を除いた pair も strict contracting。
-/
def primitivePair (P : ContractingExponentPair) : ContractingExponentPair := by
  let g := P.exponentContent
  let p0 := P.primitiveOddCount
  let H0 := P.primitiveTwoDepth
  have hgPos : 0 < g := by
    simpa [g] using P.exponentContent_pos
  have hpEq : g * p0 = P.oddCount := by
    simpa [g, p0] using P.exponentContent_mul_primitiveOddCount
  have hHEq : g * H0 = P.twoDepth := by
    simpa [g, H0] using P.exponentContent_mul_primitiveTwoDepth
  have hp0Pos : 0 < p0 := by
    simpa [p0] using P.primitiveOddCount_pos
  have hContract : 3 ^ p0 < 2 ^ H0 := by
    by_contra hnot
    have hle : 2 ^ H0 ≤ 3 ^ p0 := by omega
    have hPow : (2 ^ H0) ^ g ≤ (3 ^ p0) ^ g :=
      Nat.pow_le_pow_left hle g
    have hWholeRev : 2 ^ P.twoDepth ≤ 3 ^ P.oddCount := by
      calc
        2 ^ P.twoDepth
            = 2 ^ (g * H0) := by rw [hHEq]
        _ = 2 ^ (H0 * g) := by rw [Nat.mul_comm]
        _ = (2 ^ H0) ^ g := by rw [pow_mul]
        _ ≤ (3 ^ p0) ^ g := hPow
        _ = 3 ^ (p0 * g) := by rw [pow_mul]
        _ = 3 ^ (g * p0) := by rw [Nat.mul_comm]
        _ = 3 ^ P.oddCount := by rw [hpEq]
    exact (not_le_of_gt P.contracting) hWholeRev
  exact {
    oddCount := p0
    twoDepth := H0
    oddCount_pos := hp0Pos
    contracting := hContract
  }

@[simp] theorem primitivePair_oddCount
    (P : ContractingExponentPair) :
    P.primitivePair.oddCount = P.primitiveOddCount := rfl

@[simp] theorem primitivePair_twoDepth
    (P : ContractingExponentPair) :
    P.primitivePair.twoDepth = P.primitiveTwoDepth := rfl

/-- primitive pair は本当に coprime。 -/
theorem primitivePair_isPrimitive
    (P : ContractingExponentPair) :
    P.primitivePair.IsPrimitive := by
  have h :=
    Nat.gcd_div_gcd_div_gcd_of_pos_right
      (n := P.oddCount)
      (m := P.twoDepth)
      P.twoDepth_pos
  have h' :
      Nat.Coprime P.primitiveOddCount P.primitiveTwoDepth := by
    simpa [primitiveOddCount, primitiveTwoDepth, exponentContent,
      Nat.Coprime] using h
  change Nat.Coprime P.primitiveTwoDepth P.primitiveOddCount
  exact h'.symm

/-- primitive 化は rational slope を exact に保存する。 -/
theorem primitivePair_slope_eq
    (P : ContractingExponentPair) :
    P.primitivePair.twoDepth * P.oddCount =
      P.twoDepth * P.primitivePair.oddCount := by
  have hp := P.exponentContent_mul_primitiveOddCount
  have hH := P.exponentContent_mul_primitiveTwoDepth
  calc
    P.primitivePair.twoDepth * P.oddCount
        = P.primitiveTwoDepth *
            (P.exponentContent * P.primitiveOddCount) := by
              rw [primitivePair_twoDepth, ← hp]
    _ = (P.exponentContent * P.primitiveTwoDepth) *
          P.primitiveOddCount := by ring
    _ = P.twoDepth * P.primitivePair.oddCount := by
          rw [hH, primitivePair_oddCount]

/-- primitive 化した pair は元 pair 以下の slope。実際には equality。 -/
theorem primitivePair_slopeBelow
    (P : ContractingExponentPair) :
    SlopeBelow P.primitivePair P := by
  unfold SlopeBelow
  exact Nat.le_of_eq P.primitivePair_slope_eq

/-- 逆向きも同様。 -/
theorem slopeBelow_primitivePair
    (P : ContractingExponentPair) :
    SlopeBelow P P.primitivePair := by
  unfold SlopeBelow
  exact Nat.le_of_eq P.primitivePair_slope_eq.symm

/-- primitive 化は denominator を増やさない。 -/
theorem primitivePair_denominator_le
    (P : ContractingExponentPair) :
    P.primitivePair.oddCount ≤ P.oddCount := by
  simp only [primitivePair_oddCount, primitiveOddCount]
  exact Nat.div_le_self _ _

/-- `StripReduced` / best-upper 性は primitive 化で保存される。 -/
theorem primitivePair_stripReduced
    {P : ContractingExponentPair}
    (hReduced : P.StripReduced) :
    P.primitivePair.StripReduced := by
  apply stripReduced_of_bestUpper
  intro r hrPos hrLt
  have hBestP := bestUpper_of_stripReduced hReduced
  have hrLtP : r < P.oddCount :=
    lt_of_lt_of_le hrLt P.primitivePair_denominator_le
  have hP := hBestP r hrPos hrLtP
  let g := P.exponentContent
  have hgPos : 0 < g := by
    simpa [g] using P.exponentContent_pos
  have hp := P.exponentContent_mul_primitiveOddCount
  have hH := P.exponentContent_mul_primitiveTwoDepth
  have hScaled :
      g * (P.primitivePair.twoDepth * r) ≤
        g * (P.primitivePair.oddCount * (criticalHeight r + 1)) := by
    calc
      g * (P.primitivePair.twoDepth * r)
          = P.twoDepth * r := by
              simp only [primitivePair_twoDepth]
              rw [← hH]
              ring
      _ ≤ P.oddCount * (criticalHeight r + 1) := hP
      _ = g * (P.primitivePair.oddCount * (criticalHeight r + 1)) := by
              simp only [primitivePair_oddCount]
              rw [← hp]
              ring
  exact Nat.le_of_mul_le_mul_left hScaled hgPos

/-- nonprimitive pair は primitive 化で denominator が strict に減る。 -/
theorem primitivePair_denominator_lt_of_not_primitive
    {P : ContractingExponentPair}
    (hnot : ¬ P.IsPrimitive) :
    P.primitivePair.oddCount < P.oddCount := by
  let g := P.exponentContent
  have hgPos : 0 < g := by
    simpa [g] using P.exponentContent_pos
  have hgNe : g ≠ 1 := by
    intro hgOne
    apply hnot
    unfold IsPrimitive Nat.Coprime
    have hGcd : Nat.gcd P.twoDepth P.oddCount = 1 := by
      rw [Nat.gcd_comm]
      simpa [g, exponentContent] using hgOne
    exact hGcd
  have hgGt : 1 < g := by omega
  have hp0Pos : 0 < P.primitivePair.oddCount := by
    simpa using P.primitiveOddCount_pos
  have hmul :
      1 * P.primitivePair.oddCount <
        g * P.primitivePair.oddCount :=
    Nat.mul_lt_mul_of_pos_right hgGt hp0Pos
  have hp := P.exponentContent_mul_primitiveOddCount
  calc
    P.primitivePair.oddCount
        = 1 * P.primitivePair.oddCount := by simp
    _ < g * P.primitivePair.oddCount := hmul
    _ = P.oddCount := by
          simpa [g] using hp

/-! ## primitive reduced pair の strip permutation -/

/-- pair strip rank の residue。 -/
def stripRankResidue
    (P : ContractingExponentPair)
    (r : ℕ) : ZMod P.oddCount :=
  (P.stripRank r : ZMod P.oddCount)

/-- strip rank は modulo `p` で `H*r` と同じ。 -/
theorem stripRankResidue_eq
    (P : ContractingExponentPair)
    {r : ℕ}
    (hrPos : 0 < r) :
    P.stripRankResidue r =
      ((P.twoDepth * r : ℕ) : ZMod P.oddCount) := by
  have hlt := P.criticalHeight_below_chord hrPos
  have hle :
      P.oddCount * criticalHeight r ≤ P.twoDepth * r :=
    Nat.le_of_lt hlt
  unfold stripRankResidue stripRank
  rw [Nat.cast_sub hle]
  simp

/-- primitive pair では proper strip residues は pairwise distinct。 -/
theorem stripRankResidue_injective_of_primitive
    {P : ContractingExponentPair}
    (hPrimitive : P.IsPrimitive)
    {r s : ℕ}
    (hrPos : 0 < r)
    (hrLt : r < P.oddCount)
    (hsPos : 0 < s)
    (hsLt : s < P.oddCount)
    (hEq : P.stripRankResidue r = P.stripRankResidue s) :
    r = s := by
  let p := P.oddCount
  let H := P.twoDepth
  haveI : NeZero p := ⟨Nat.ne_of_gt (by simpa [p] using P.oddCount_pos)⟩
  have hMul :
      (((H * r : ℕ) : ZMod p)) =
        (((H * s : ℕ) : ZMod p)) := by
    have hr := P.stripRankResidue_eq hrPos
    have hs := P.stripRankResidue_eq hsPos
    simpa [p, H] using hr.symm.trans (hEq.trans hs)
  let U : (ZMod p)ˣ :=
    ZMod.unitOfCoprime H (by simpa [p, H, IsPrimitive] using hPrimitive)
  have hHU :
      ((H : ℕ) : ZMod p) = (↑U : ZMod p) := by
    simp [U]
  have hMul' :
      (↑U : ZMod p) * ((r : ℕ) : ZMod p) =
        (↑U : ZMod p) * ((s : ℕ) : ZMod p) := by
    simpa [Nat.cast_mul, hHU] using hMul
  have hCancel :=
    congrArg
      (fun z : ZMod p => (↑(U⁻¹) : ZMod p) * z)
      hMul'
  have hCast :
      ((r : ℕ) : ZMod p) = ((s : ℕ) : ZMod p) := by
    simpa [← mul_assoc] using hCancel
  have hVal := congrArg ZMod.val hCast
  simpa [ZMod.val_natCast, Nat.mod_eq_of_lt hrLt,
    Nat.mod_eq_of_lt hsLt, p] using hVal

/-- primitive proper denominator では strip rank は `p` 自身を取らない。 -/
theorem stripRank_ne_oddCount_of_primitive
    {P : ContractingExponentPair}
    (hPrimitive : P.IsPrimitive)
    {r : ℕ}
    (hrPos : 0 < r)
    (hrLt : r < P.oddCount) :
    P.stripRank r ≠ P.oddCount := by
  intro hEq
  let p := P.oddCount
  let H := P.twoDepth
  haveI : NeZero p := ⟨Nat.ne_of_gt (by simpa [p] using P.oddCount_pos)⟩
  have hResid := P.stripRankResidue_eq hrPos
  have hZero : (((H * r : ℕ) : ZMod p)) = 0 := by
    have hRankZero : P.stripRankResidue r = 0 := by
      unfold stripRankResidue
      rw [hEq]
      simp only [CharP.cast_eq_zero]
    simpa [p, H] using hResid.symm.trans hRankZero
  let U : (ZMod p)ˣ :=
    ZMod.unitOfCoprime H (by simpa [p, H, IsPrimitive] using hPrimitive)
  have hHU :
      ((H : ℕ) : ZMod p) = (↑U : ZMod p) := by simp [U]
  have hUr :
      (↑U : ZMod p) * ((r : ℕ) : ZMod p) = 0 := by
    simpa [Nat.cast_mul, hHU] using hZero
  have hCancel :=
    congrArg
      (fun z : ZMod p => (↑(U⁻¹) : ZMod p) * z)
      hUr
  have hrZero : ((r : ℕ) : ZMod p) = 0 := by
    simpa [← mul_assoc] using hCancel
  have hVal := congrArg ZMod.val hrZero
  have hrEqZero : r = 0 := by
    simpa [ZMod.val_natCast, Nat.mod_eq_of_lt hrLt, p] using hVal
  omega

/-- primitive + reduced では proper strip rank は exact に `1,...,p-1` 内。 -/
theorem stripRank_pos_lt_of_primitive_reduced
    {P : ContractingExponentPair}
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    {r : ℕ}
    (hrPos : 0 < r)
    (hrLt : r < P.oddCount) :
    0 < P.stripRank r ∧ P.stripRank r < P.oddCount := by
  have hPos := P.stripRank_pos hrPos
  have hLe := hReduced r hrPos hrLt
  have hNe := P.stripRank_ne_oddCount_of_primitive hPrimitive hrPos hrLt
  exact ⟨hPos, lt_of_le_of_ne hLe hNe⟩

/--
primitive + reduced では proper strip rank は `1,...,p-1` を一度ずつ取る。
constructive な surjectivity 版。
-/
theorem exists_unique_proper_denominator_of_stripRank
    {P : ContractingExponentPair}
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    {q : ℕ}
    (hqPos : 0 < q)
    (hqLt : q < P.oddCount) :
    ∃! r : ℕ,
      0 < r ∧ r < P.oddCount ∧ P.stripRank r = q := by
  let p := P.oddCount
  let H := P.twoDepth
  haveI : NeZero p := ⟨Nat.ne_of_gt (by simpa [p] using P.oddCount_pos)⟩
  let U : (ZMod p)ˣ :=
    ZMod.unitOfCoprime H (by simpa [p, H, IsPrimitive] using hPrimitive)
  let z : ZMod p :=
    (↑(U⁻¹) : ZMod p) * ((q : ℕ) : ZMod p)
  let r : ℕ := z.val
  have hrLt : r < p := by
    simpa [r] using ZMod.val_lt z
  have hqCastNe : (((q : ℕ) : ZMod p)) ≠ 0 := by
    intro hq0
    have hVal := congrArg ZMod.val hq0
    have hqEq : q = 0 := by
      simpa [ZMod.val_natCast, Nat.mod_eq_of_lt (by simpa [p] using hqLt), p] using hVal
    omega
  have hzNe : z ≠ 0 := by
    intro hz
    have hMul :=
      congrArg
        (fun t : ZMod p => (↑U : ZMod p) * t)
        hz
    have hq0 : (((q : ℕ) : ZMod p)) = 0 := by
      simpa [z, ← mul_assoc] using hMul
    exact hqCastNe hq0
  have hrPos : 0 < r := by
    have hrNe : r ≠ 0 := by
      intro hr0
      apply hzNe
      apply (ZMod.val_eq_zero z).mp
      simpa [r] using hr0
    exact Nat.pos_of_ne_zero hrNe
  have hrCast : ((r : ℕ) : ZMod p) = z := by
    simp only [ZMod.natCast_val, ZMod.cast_id', id_eq, r]
  have hHU :
      ((H : ℕ) : ZMod p) = (↑U : ZMod p) := by simp [U]
  have hHr :
      (((H * r : ℕ) : ZMod p)) = ((q : ℕ) : ZMod p) := by
    rw [Nat.cast_mul, hHU, hrCast]
    simp [z, ← mul_assoc]
  have hResid := P.stripRankResidue_eq hrPos
  have hRankCast :
      ((P.stripRank r : ℕ) : ZMod p) = ((q : ℕ) : ZMod p) := by
    simpa [p, H, stripRankResidue] using hResid.trans hHr
  have hRange :=
    P.stripRank_pos_lt_of_primitive_reduced
      hPrimitive hReduced hrPos (by simpa [p] using hrLt)
  have hVal := congrArg ZMod.val hRankCast
  have hRankEq : P.stripRank r = q := by
    simpa [ZMod.val_natCast,
      Nat.mod_eq_of_lt (by simpa [p] using hRange.2),
      Nat.mod_eq_of_lt (by simpa [p] using hqLt), p] using hVal
  refine ⟨r, ?_, ?_⟩
  · exact ⟨hrPos, by simpa [p] using hrLt, hRankEq⟩
  · intro s hs
    rcases hs with ⟨hsPos, hsLt, hsEq⟩
    symm
    apply P.stripRankResidue_injective_of_primitive
      hPrimitive hrPos (by simpa [p] using hrLt) hsPos hsLt
    unfold stripRankResidue
    rw [hRankEq, hsEq]

/-! ## primitive reduced normal form -/

/-- primitive + reduced pair packet。 -/
structure PrimitiveReducedData (P : ContractingExponentPair) : Prop where
  primitive : P.IsPrimitive
  reduced : P.StripReduced

/--
任意 contracting pair は、すでに primitive+reduced であるか、
より小さい denominator の primitive+reduced pair へ slope を上げずに正規化できる。
-/
theorem primitiveReduced_or_exists_strict_normalization
    (P : ContractingExponentPair) :
    P.PrimitiveReducedData ∨
      ∃ Q : ContractingExponentPair,
        Q.PrimitiveReducedData ∧
        Q.oddCount < P.oddCount ∧
        SlopeBelow Q P := by
  by_cases hReduced : P.StripReduced
  · by_cases hPrimitive : P.IsPrimitive
    · exact Or.inl ⟨hPrimitive, hReduced⟩
    · let Q := P.primitivePair
      have hQReduced : Q.StripReduced := by
        simpa [Q] using P.primitivePair_stripReduced hReduced
      have hQPrimitive : Q.IsPrimitive := by
        simpa [Q] using P.primitivePair_isPrimitive
      have hQLt : Q.oddCount < P.oddCount := by
        simpa [Q] using P.primitivePair_denominator_lt_of_not_primitive hPrimitive
      have hSlope : SlopeBelow Q P := by
        simpa [Q] using P.primitivePair_slopeBelow
      exact Or.inr ⟨Q, ⟨hQPrimitive, hQReduced⟩, hQLt, hSlope⟩
  · have hWide : P.HasWideStrip := by
      by_contra hnotWide
      exact hReduced (stripReduced_of_not_hasWideStrip hnotWide)
    obtain ⟨C, hCLt⟩ :=
      exists_bestUpperCertificate_strict_of_wide hWide
    let Q := C.pair.primitivePair
    have hQReduced : Q.StripReduced := by
      simpa [Q] using C.pair.primitivePair_stripReduced C.reduced
    have hQPrimitive : Q.IsPrimitive := by
      simpa [Q] using C.pair.primitivePair_isPrimitive
    have hQLeC : Q.oddCount ≤ C.pair.oddCount := by
      simpa [Q] using C.pair.primitivePair_denominator_le
    have hQLt : Q.oddCount < P.oddCount :=
      lt_of_le_of_lt hQLeC hCLt
    have hQC : SlopeBelow Q C.pair := by
      simpa [Q] using C.pair.primitivePair_slopeBelow
    have hQP : SlopeBelow Q P :=
      slopeBelow_trans hQC C.slope_below
    exact Or.inr ⟨Q, ⟨hQPrimitive, hQReduced⟩, hQLt, hQP⟩

end ContractingExponentPair
end Word
end Collatz2
