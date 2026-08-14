import CollatzLean.Collatz2.Geometry.Center
import CollatzLean.Collatz2.Geometry.RankPath
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Group.Basic

/-!
# Collatz2 Geometry: rank-unit shadow

primitive exponent pair `(p,H)` に対して modular root `u` を選び

  u^p = 2
  u^H = 3

と読める場合、proper cut rank `d_k` と normalized translation monomial

  M_k = 2^h_k * 3^(p-k)

は exact に

  u^d_k * M_k = 3^p

を満たす。

primitive pair `gcd(H,p)=1` では Bézout 係数からこの unit 自身も内部構成できる。
-/

namespace Collatz2
namespace Word

/-- terminal negative gap。FirstCrossing では正。 -/
def terminalGap (w : Word) : ℕ :=
  2 ^ twoSteps w - 3 ^ oddSteps w

/-- `terminalGap` は transfer の natural center gap そのもの。 -/
@[simp] theorem terminalGap_eq_centerGap (w : Word) :
    terminalGap w = (AffineTransfer.ofWord w).centerGap := by
  rfl

/-- FirstCrossing terminal gap は正。 -/
theorem FirstCrossing.terminalGap_pos
    {w : Word}
    (hF : FirstCrossing w) :
    0 < terminalGap w := by
  unfold terminalGap
  exact Nat.sub_pos_of_lt
    ((contracting_iff_threePow_lt_twoPow).1 hF.terminalContracting)

/--
rank unit packet。
`u^p=2`, `u^H=3` を terminal gap modulus 上で保持する。
-/
structure RankUnitData (w : Word) where
  gap_pos : 0 < terminalGap w
  unit : (ZMod (terminalGap w))ˣ
  unit_pow_oddSteps :
    ((↑unit : ZMod (terminalGap w)) ^ oddSteps w) =
      ((2 : ℕ) : ZMod (terminalGap w))
  unit_pow_twoSteps :
    ((↑unit : ZMod (terminalGap w)) ^ twoSteps w) =
      ((3 : ℕ) : ZMod (terminalGap w))

/--
primitive exponent pair `gcd(H,p)=1` では `RankUnitData` は追加仮定ではない。

`G = 2^H - 3^p` とする。mod `G` では `2^H = 3^p`。
2,3 はともに `G` と coprime なので units `u₂,u₃` を持つ。
Bézout

  H*a + p*b = 1

に対して

  u = u₃^a * u₂^b

と置けば、units 上で `u^p=u₂`, `u^H=u₃` が従う。
-/
theorem FirstCrossing.exists_rankUnitData_of_coprime
    {w : Word}
    (hF : FirstCrossing w)
    (hcop : Nat.Coprime (twoSteps w) (oddSteps w)) :
    Nonempty (RankUnitData w) := by
  let H := twoSteps w
  let p := oddSteps w
  let G := terminalGap w
  have hpPos : 0 < p := by
    dsimp [p, oddSteps]
    exact List.length_pos_iff.mpr hF.nonempty
  have hPow : 3 ^ p < 2 ^ H := by
    dsimp [p, H]
    exact
      (contracting_iff_threePow_lt_twoPow).1
        hF.terminalContracting
  have hHPos : 0 < H := by
    by_contra hnot
    have hHzero : H = 0 := by omega
    rw [hHzero] at hPow
    simp at hPow
  have hGapPos : 0 < G := by
    dsimp [G]
    exact hF.terminalGap_pos
  have hGapAdd : G + 3 ^ p = 2 ^ H := by
    dsimp [G, terminalGap]
    exact Nat.sub_add_cancel (Nat.le_of_lt hPow)
  have hEvenTwo : Even (2 ^ H) :=
    (show Even (2 : ℕ) by decide).pow_of_ne_zero
      (Nat.ne_of_gt hHPos)
  have hOddThree : Odd (3 ^ p) :=
    (show Odd (3 : ℕ) by decide).pow
  have hOddGap : Odd G :=
    Nat.Even.sub_odd (Nat.le_of_lt hPow) hEvenTwo hOddThree
  have hTwoCop : Nat.Coprime 2 G :=
    hOddGap.coprime_two_left
  have hThreeCop : Nat.Coprime 3 G := by
    apply (show Nat.Prime 3 by decide).coprime_iff_not_dvd.mpr
    intro hThreeDvdGap
    have hThreeDvdPow : 3 ∣ 3 ^ p :=
      dvd_pow_self 3 (Nat.ne_of_gt hpPos)
    have hThreeDvdSum : 3 ∣ G + 3 ^ p :=
      Nat.dvd_add hThreeDvdGap hThreeDvdPow
    have hThreeDvdTwoPow : 3 ∣ 2 ^ H := by
      rw [hGapAdd] at hThreeDvdSum
      exact hThreeDvdSum
    have hThreeDvdTwo : 3 ∣ 2 :=
      (show Nat.Prime 3 by decide).dvd_of_dvd_pow hThreeDvdTwoPow
    norm_num at hThreeDvdTwo
  let u2 : (ZMod G)ˣ :=
    ZMod.unitOfCoprime 2 hTwoCop
  let u3 : (ZMod G)ˣ :=
    ZMod.unitOfCoprime 3 hThreeCop
  have hPowCast :
      (((2 ^ H : ℕ) : ZMod G)) =
        (((3 ^ p : ℕ) : ZMod G)) := by
    have hCast :=
      congrArg (fun z : ℕ => (z : ZMod G)) hGapAdd
    simpa using hCast.symm
  have hUnitRel : u2 ^ H = u3 ^ p := by
    apply Units.ext
    simpa [u2, u3] using hPowCast
  have hRel :
      u3 ^ (p : ℤ) = u2 ^ (H : ℤ) := by
    simpa only [zpow_natCast] using hUnitRel.symm
  let a : ℤ := H.gcdA p
  let b : ℤ := H.gcdB p
  have hGcd : Nat.gcd H p = 1 :=
    Nat.coprime_iff_gcd_eq_one.mp hcop
  have hBez0 := Nat.gcd_eq_gcd_ab H p
  rw [hGcd] at hBez0
  have hBez :
      a * (H : ℤ) + b * (p : ℤ) = 1 := by
    calc
      a * (H : ℤ) + b * (p : ℤ)
          = (H : ℤ) * a + (p : ℤ) * b := by ring
      _ = 1 := by
        simpa [a, b] using hBez0.symm
  let u : (ZMod G)ˣ :=
    u3 ^ a * u2 ^ b
  have hRelA :
      u3 ^ (a * (p : ℤ)) =
        u2 ^ (a * (H : ℤ)) := by
    calc
      u3 ^ (a * (p : ℤ))
          = (u3 ^ (p : ℤ)) ^ a :=
            zpow_mul' u3 a (p : ℤ)
      _ = (u2 ^ (H : ℤ)) ^ a := by rw [hRel]
      _ = u2 ^ (a * (H : ℤ)) :=
        (zpow_mul' u2 a (H : ℤ)).symm
  have hRelB :
      u2 ^ (b * (H : ℤ)) =
        u3 ^ (b * (p : ℤ)) := by
    calc
      u2 ^ (b * (H : ℤ))
          = (u2 ^ (H : ℤ)) ^ b :=
            zpow_mul' u2 b (H : ℤ)
      _ = (u3 ^ (p : ℤ)) ^ b := by rw [← hRel]
      _ = u3 ^ (b * (p : ℤ)) :=
        (zpow_mul' u3 b (p : ℤ)).symm
  have huPowPZ : u ^ (p : ℤ) = u2 := by
    dsimp [u]
    calc
      (u3 ^ a * u2 ^ b) ^ (p : ℤ)
          = (u3 ^ a) ^ (p : ℤ) *
              (u2 ^ b) ^ (p : ℤ) := by
                rw [mul_zpow]
      _ = u3 ^ (a * (p : ℤ)) *
            u2 ^ (b * (p : ℤ)) := by
              rw [← zpow_mul, ← zpow_mul]
      _ = u2 ^ (a * (H : ℤ)) *
            u2 ^ (b * (p : ℤ)) := by
              rw [hRelA]
      _ = u2 ^ (a * (H : ℤ) + b * (p : ℤ)) := by
              rw [← zpow_add]
      _ = u2 := by
              rw [hBez]
              simp
  have huPowHZ : u ^ (H : ℤ) = u3 := by
    dsimp [u]
    calc
      (u3 ^ a * u2 ^ b) ^ (H : ℤ)
          = (u3 ^ a) ^ (H : ℤ) *
              (u2 ^ b) ^ (H : ℤ) := by
                rw [mul_zpow]
      _ = u3 ^ (a * (H : ℤ)) *
            u2 ^ (b * (H : ℤ)) := by
              rw [← zpow_mul, ← zpow_mul]
      _ = u3 ^ (a * (H : ℤ)) *
            u3 ^ (b * (p : ℤ)) := by
              rw [hRelB]
      _ = u3 ^ (a * (H : ℤ) + b * (p : ℤ)) := by
              rw [← zpow_add]
      _ = u3 := by
              rw [hBez]
              simp
  have huPowP : u ^ p = u2 := by
    simpa only [zpow_natCast] using huPowPZ
  have huPowH : u ^ H = u3 := by
    simpa only [zpow_natCast] using huPowHZ
  let R : RankUnitData w := {
    gap_pos := by simpa [G] using hGapPos
    unit := by simpa [G] using u
    unit_pow_oddSteps := by
      have hCoe :=
        congrArg
          (fun z : (ZMod G)ˣ => (↑z : ZMod G))
          huPowP
      simpa [u2, p, G] using hCoe
    unit_pow_twoSteps := by
      have hCoe :=
        congrArg
          (fun z : (ZMod G)ˣ => (↑z : ZMod G))
          huPowH
      simpa [u3, H, G] using hCoe
  }
  exact ⟨R⟩

namespace RankUnitData

/--
proper FirstCrossing cut の normalized monomial は rank だけで unit-direction が決まる。

  u^d_k * M_k = 3^p.
-/
theorem cut_certificate
    {w : Word}
    (R : RankUnitData w)
    (hF : FirstCrossing w)
    {k : ℕ}
    (hkPos : 0 < k)
    (hkLt : k < oddSteps w) :
    ((↑R.unit : ZMod (terminalGap w)) ^ chordRank w k) *
        ((normalizedCutTerm w k : ℕ) : ZMod (terminalGap w)) =
      ((3 ^ oddSteps w : ℕ) : ZMod (terminalGap w)) := by
  have hlt := hF.prefixSlope_cross hkPos hkLt
  have hle :
      oddSteps w * prefixTwoDepth w k ≤ twoSteps w * k :=
    Nat.le_of_lt hlt
  have hrank :
      chordRank w k + oddSteps w * prefixTwoDepth w k =
        twoSteps w * k := by
    unfold chordRank
    exact Nat.sub_add_cancel hle
  have hExp :
      chordRank w k +
          oddSteps w * prefixTwoDepth w k +
          twoSteps w * (oddSteps w - k) =
        twoSteps w * oddSteps w := by
    rw [hrank]
    rw [← Nat.mul_add]
    have hkSum :
        k + (oddSteps w - k) = oddSteps w := by
      omega
    rw [hkSum]
  unfold normalizedCutTerm
  push_cast
  let u : ZMod (terminalGap w) := ↑R.unit
  have huP :
      u ^ oddSteps w = ((2 : ℕ) : ZMod (terminalGap w)) := by
    simpa [u] using R.unit_pow_oddSteps
  have huH :
      u ^ twoSteps w = ((3 : ℕ) : ZMod (terminalGap w)) := by
    simpa [u] using R.unit_pow_twoSteps
  change
    u ^ chordRank w k *
        (((2 : ℕ) : ZMod (terminalGap w)) ^ prefixTwoDepth w k *
          (((3 : ℕ) : ZMod (terminalGap w)) ^ (oddSteps w - k))) =
      (((3 : ℕ) : ZMod (terminalGap w)) ^ oddSteps w)
  calc
    u ^ chordRank w k *
          (((2 : ℕ) : ZMod (terminalGap w)) ^ prefixTwoDepth w k *
            (((3 : ℕ) : ZMod (terminalGap w)) ^ (oddSteps w - k)))
        =
      u ^ chordRank w k *
          ((u ^ oddSteps w) ^ prefixTwoDepth w k *
            (u ^ twoSteps w) ^ (oddSteps w - k)) := by
              rw [huP, huH]
    _ =
      u ^ (chordRank w k +
          oddSteps w * prefixTwoDepth w k +
          twoSteps w * (oddSteps w - k)) := by
            rw [← pow_mul, ← pow_mul]
            rw [← pow_add, ← pow_add]
            rw [Nat.add_assoc]
    _ = u ^ (twoSteps w * oddSteps w) := by
          rw [hExp]
    _ = (u ^ twoSteps w) ^ oddSteps w := by
          rw [pow_mul]
    _ = (((3 : ℕ) : ZMod (terminalGap w)) ^ oddSteps w) := by
          rw [huH]


end RankUnitData
end Word
end Collatz2
