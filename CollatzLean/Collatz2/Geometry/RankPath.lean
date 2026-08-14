import CollatzLean.Collatz2.Core.TranslationPath
import CollatzLean.Collatz2.Local.FirstCrossing
import Mathlib.Data.ZMod.Basic

/-!
# Collatz2 Geometry: FirstCrossing rank path

有限 exponent word `w` の prefix cut `k` に対し

  p = oddSteps w
  H = twoSteps w
  h_k = twoSteps (w.take k)

として rational chord rank

  d_k = H*k - p*h_k

を自然数で定義する。

FirstCrossing では proper prefix が coefficient-expanding、whole が
coefficient-contracting なので

  p*h_k < H*k

が成り立ち、したがって proper rank は strict positive になる。

primitive pair `gcd(H,p)=1` では rank residue は

  d_k ≡ H*k (mod p)

なので proper cuts の rank residue は pairwise distinct。
これは rational Dyck / Christoffel rank の純整数版である。
-/

namespace Collatz2
namespace Word

/-- cut `k` までの累積2進 depth。 -/
def prefixTwoDepth (w : Word) (k : ℕ) : ℕ :=
  twoSteps (w.take k)

/-- rational chord に対する natural rank。 -/
def chordRank (w : Word) (k : ℕ) : ℕ :=
  twoSteps w * k - oddSteps w * prefixTwoDepth w k

/-- subtraction を使わない signed rank。 -/
def chordRankInt (w : Word) (k : ℕ) : ℤ :=
  (twoSteps w : ℤ) * (k : ℤ) -
    (oddSteps w : ℤ) * (prefixTwoDepth w k : ℤ)

/-- FirstCrossing proper cut は rational chord の strict 下側にある。 -/
theorem FirstCrossing.prefixSlope_cross
    {w : Word}
    (hF : FirstCrossing w)
    {k : ℕ}
    (hkPos : 0 < k)
    (hkLt : k < oddSteps w) :
    oddSteps w * prefixTwoDepth w k <
      twoSteps w * k := by
  have hkLtLen : k < w.length := by
    simpa [oddSteps] using hkLt
  have hkLeLen : k ≤ w.length := Nat.le_of_lt hkLtLen
  have hTakeLen : (w.take k).length = k :=
    List.length_take_of_le hkLeLen
  have hPrefixRaw :=
    (expanding_iff_twoPow_lt_threePow).1
      (hF.properExpanding hkPos hkLtLen)
  have hPrefix :
      2 ^ prefixTwoDepth w k < 3 ^ k := by
    simpa [prefixTwoDepth, oddSteps, hTakeLen] using hPrefixRaw
  have hWhole :=
    (contracting_iff_threePow_lt_twoPow).1
      hF.terminalContracting
  have hpPos : 0 < oddSteps w := by
    simpa [oddSteps] using List.length_pos_iff.mpr hF.nonempty
  have hPrefixPowRaw :=
    Nat.pow_lt_pow_left hPrefix (Nat.ne_of_gt hpPos)
  have hPrefixPow :
      2 ^ (prefixTwoDepth w k * oddSteps w) <
        3 ^ (k * oddSteps w) := by
    calc
      2 ^ (prefixTwoDepth w k * oddSteps w)
          = (2 ^ prefixTwoDepth w k) ^ oddSteps w := by
              rw [pow_mul]
      _ < (3 ^ k) ^ oddSteps w := hPrefixPowRaw
      _ = 3 ^ (k * oddSteps w) := by
              rw [pow_mul]
  have hWholePowRaw :=
    Nat.pow_lt_pow_left hWhole (Nat.ne_of_gt hkPos)
  have hWholePow :
      3 ^ (oddSteps w * k) <
        2 ^ (twoSteps w * k) := by
    calc
      3 ^ (oddSteps w * k)
          = (3 ^ oddSteps w) ^ k := by
              rw [pow_mul]
      _ < (2 ^ twoSteps w) ^ k := hWholePowRaw
      _ = 2 ^ (twoSteps w * k) := by
              rw [pow_mul]
  by_contra hnot
  have hle : twoSteps w * k ≤ oddSteps w * prefixTwoDepth w k := by
    omega
  have htwo :
      2 ^ (twoSteps w * k) ≤
        2 ^ (oddSteps w * prefixTwoDepth w k) :=
    Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hle
  have hleft :
      2 ^ (oddSteps w * prefixTwoDepth w k) <
        3 ^ (oddSteps w * k) := by
    simpa [Nat.mul_comm] using hPrefixPow
  have hcontra :
      2 ^ (twoSteps w * k) < 2 ^ (twoSteps w * k) :=
    lt_of_le_of_lt htwo (lt_trans hleft hWholePow)
  exact (Nat.lt_irrefl _ hcontra)

/-- FirstCrossing proper cut の natural rank は strict positive。 -/
theorem FirstCrossing.chordRank_pos
    {w : Word}
    (hF : FirstCrossing w)
    {k : ℕ}
    (hkPos : 0 < k)
    (hkLt : k < oddSteps w) :
    0 < chordRank w k := by
  unfold chordRank
  exact Nat.sub_pos_of_lt (hF.prefixSlope_cross hkPos hkLt)

/-- proper cut では signed rank は natural rank の整数 cast。 -/
theorem FirstCrossing.chordRankInt_eq_natCast
    {w : Word}
    (hF : FirstCrossing w)
    {k : ℕ}
    (hkPos : 0 < k)
    (hkLt : k < oddSteps w) :
    chordRankInt w k = (chordRank w k : ℤ) := by
  have hlt := hF.prefixSlope_cross hkPos hkLt
  have hle :
      oddSteps w * prefixTwoDepth w k ≤ twoSteps w * k :=
    Nat.le_of_lt hlt
  unfold chordRankInt chordRank
  rw [Nat.cast_sub hle]
  push_cast
  ring

/-- rank residue。primitive case では cuts を permutation として読む。 -/
def chordRankResidue (w : Word) (k : ℕ) : ZMod (oddSteps w) :=
  (chordRank w k : ZMod (oddSteps w))

/-- proper rank は modulo `p` で `H*k` と同じ。 -/
theorem FirstCrossing.chordRankResidue_eq
    {w : Word}
    (hF : FirstCrossing w)
    {k : ℕ}
    (hkPos : 0 < k)
    (hkLt : k < oddSteps w) :
    chordRankResidue w k =
      ((twoSteps w * k : ℕ) : ZMod (oddSteps w)) := by
  have hlt := hF.prefixSlope_cross hkPos hkLt
  have hle :
      oddSteps w * prefixTwoDepth w k ≤ twoSteps w * k :=
    Nat.le_of_lt hlt
  unfold chordRankResidue chordRank
  rw [Nat.cast_sub hle]
  simp

/--
primitive slope `gcd(H,p)=1` では proper rank residue は pairwise distinct。
したがって `k=1,...,p-1` の residues は `1,...,p-1` の並べ替えになる。
-/
theorem FirstCrossing.chordRankResidue_injective
    {w : Word}
    (hF : FirstCrossing w)
    (hcop : Nat.Coprime (twoSteps w) (oddSteps w))
    {k l : ℕ}
    (hkPos : 0 < k)
    (hkLt : k < oddSteps w)
    (hlPos : 0 < l)
    (hlLt : l < oddSteps w)
    (hEq : chordRankResidue w k = chordRankResidue w l) :
    k = l := by
  have hpPos : 0 < oddSteps w := by
    simpa [oddSteps] using List.length_pos_iff.mpr hF.nonempty
  let p := oddSteps w
  let H := twoSteps w
  haveI : NeZero p := ⟨Nat.ne_of_gt (by simpa [p] using hpPos)⟩
  have hMul :
      (((H * k : ℕ) : ZMod p)) =
        (((H * l : ℕ) : ZMod p)) := by
    have hk := hF.chordRankResidue_eq hkPos hkLt
    have hl := hF.chordRankResidue_eq hlPos hlLt
    simpa [p, H] using hk.symm.trans (hEq.trans hl)
  let U : (ZMod p)ˣ :=
    ZMod.unitOfCoprime H (by simpa [p, H] using hcop)
  have hHU :
      ((H : ℕ) : ZMod p) = (↑U : ZMod p) := by
    simp [U]
  have hMul' :
      (↑U : ZMod p) * ((k : ℕ) : ZMod p) =
        (↑U : ZMod p) * ((l : ℕ) : ZMod p) := by
    simpa [Nat.cast_mul, hHU] using hMul
  have hCancel :=
    congrArg
      (fun z : ZMod p => (↑(U⁻¹) : ZMod p) * z)
      hMul'
  have hCast :
      ((k : ℕ) : ZMod p) = ((l : ℕ) : ZMod p) := by
    simpa [← mul_assoc] using hCancel
  have hVal := congrArg ZMod.val hCast
  simpa [ZMod.val_natCast, Nat.mod_eq_of_lt hkLt,
    Nat.mod_eq_of_lt hlLt, p] using hVal

/-! ## translation path の rank normalization -/

/-- translation path を一様に3倍した normalized path。 -/
def normalizedTranslationPathTerms (w : Word) : List ℕ :=
  scaleTranslationTerms 3 (translationPathTerms w)

/-- normalized path の総和は exact に `3*B`。 -/
theorem normalizedTranslationPathTerms_sum
    (w : Word) :
    (normalizedTranslationPathTerms w).sum = 3 * affineConst w := by
  unfold normalizedTranslationPathTerms
  rw [sum_scaleTranslationTerms, translationPathTerms_sum_eq_affineConst]

/-- cut `k` に対応する normalized translation monomial。 -/
def normalizedCutTerm (w : Word) (k : ℕ) : ℕ :=
  2 ^ prefixTwoDepth w k * 3 ^ (oddSteps w - k)

/--
proper FirstCrossing cut の rank は monomial の2進 exponent を whole chord に持ち上げる。
modular rank-unit 化の前段として使う exact equality。
-/
theorem FirstCrossing.rankPowerLift
    {w : Word}
    (hF : FirstCrossing w)
    {k : ℕ}
    (hkPos : 0 < k)
    (hkLt : k < oddSteps w) :
    2 ^ chordRank w k *
        (normalizedCutTerm w k) ^ oddSteps w =
      2 ^ (twoSteps w * k) *
        3 ^ ((oddSteps w - k) * oddSteps w) := by
  have hlt := hF.prefixSlope_cross hkPos hkLt
  have hle :
      oddSteps w * prefixTwoDepth w k ≤ twoSteps w * k :=
    Nat.le_of_lt hlt
  have hrank :
      chordRank w k + oddSteps w * prefixTwoDepth w k =
        twoSteps w * k := by
    unfold chordRank
    exact Nat.sub_add_cancel hle
  unfold normalizedCutTerm
  calc
    2 ^ chordRank w k *
          (2 ^ prefixTwoDepth w k *
            3 ^ (oddSteps w - k)) ^ oddSteps w
        =
      2 ^ (chordRank w k +
          prefixTwoDepth w k * oddSteps w) *
        3 ^ ((oddSteps w - k) * oddSteps w) := by
          rw [mul_pow, ← pow_mul, ← pow_mul, pow_add]
          ring
    _ =
      2 ^ (twoSteps w * k) *
        3 ^ ((oddSteps w - k) * oddSteps w) := by
          have hExp :
              chordRank w k + prefixTwoDepth w k * oddSteps w =
                twoSteps w * k := by
            rw [Nat.mul_comm (prefixTwoDepth w k) (oddSteps w)]
            exact hrank
          rw [hExp]

end Word
end Collatz2
