import CollatzLean.Collatz2.Geometry.RankPath
import Mathlib.Data.Nat.Log

/-!
# Collatz2 Geometry: irrational critical line と rational chord の strip

Stage 6。

`k > 0` に対し

  criticalHeight(k) = max { h | 2^h < 3^k }

を純整数 `Nat.log` で定義する。
FirstCrossing word では prefix depth `h_k` はこの critical height 以下である。
一方 whole が contracting なので rational chord `H*k/p` は critical line より上にある。

そこで chord rank

  d_k = H*k - p*h_k

を

  stripRank(k) + p*extraDepth(k)

へ exact に分解する。

* `stripRank` は `(p,H,k)` だけで決まる deterministic geometry
* `extraDepth` は word prefix が critical line からさらに下へ沈んだ量

である。
-/

namespace Collatz2
namespace Word

/-- `2^h < 3^k` を満たす最大整数 height。 -/
def criticalHeight (k : ℕ) : ℕ :=
  Nat.log 2 (3 ^ k - 1)

/-- positive `k` では critical height は本当に expanding 側にある。 -/
theorem criticalHeight_pow_lt_threePow
    {k : ℕ}
    (hkPos : 0 < k) :
    2 ^ criticalHeight k < 3 ^ k := by
  have hkOne : 1 ≤ k := by omega
  have hThreeGe : 3 ≤ 3 ^ k := by
    calc
      3 = 3 ^ (1 : ℕ) := by norm_num
      _ ≤ 3 ^ k :=
        Nat.pow_le_pow_right (by omega : 0 < (3 : ℕ)) hkOne
  have hSubPos : 0 < 3 ^ k - 1 := by omega
  have hLog :=
    Nat.pow_log_le_self 2 (Nat.ne_of_gt hSubPos)
  unfold criticalHeight
  omega

/-- `2^h < 3^k` なら `h` は critical height 以下。 -/
theorem le_criticalHeight_of_twoPow_lt_threePow
    {k h : ℕ}
    (hlt : 2 ^ h < 3 ^ k) :
    h ≤ criticalHeight k := by
  have hle : 2 ^ h ≤ 3 ^ k - 1 := by omega
  unfold criticalHeight
  exact Nat.le_log_of_pow_le (by omega : 1 < (2 : ℕ)) hle

/-- contracting depth は critical height を strict に越える。 -/
theorem criticalHeight_lt_of_threePow_lt_twoPow
    {k h : ℕ}
    (hkPos : 0 < k)
    (hcontract : 3 ^ k < 2 ^ h) :
    criticalHeight k < h := by
  by_contra hnot
  have hle : h ≤ criticalHeight k := by omega
  have hpowLe :
      2 ^ h ≤ 2 ^ criticalHeight k :=
    Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hle
  have hcrit := criticalHeight_pow_lt_threePow hkPos
  have hcontra : 2 ^ h < 2 ^ h :=
    lt_of_le_of_lt hpowLe (lt_trans hcrit hcontract)
  exact (Nat.lt_irrefl _ hcontra)

/-- rational chord と critical height の間の deterministic rank-width。 -/
def stripRank (w : Word) (k : ℕ) : ℕ :=
  twoSteps w * k - oddSteps w * criticalHeight k

/-- prefix が critical line からさらに下へ沈んだ depth。 -/
def extraDepth (w : Word) (k : ℕ) : ℕ :=
  criticalHeight k - prefixTwoDepth w k

/-- FirstCrossing prefix depth は critical height 以下。 -/
theorem FirstCrossing.prefixTwoDepth_le_criticalHeight
    {w : Word}
    (hF : FirstCrossing w)
    {k : ℕ}
    (hkPos : 0 < k)
    (hkLt : k < oddSteps w) :
    prefixTwoDepth w k ≤ criticalHeight k := by
  have hkLtLen : k < w.length := by
    simpa [oddSteps] using hkLt
  have hkLeLen : k ≤ w.length := Nat.le_of_lt hkLtLen
  have hTakeLen : (w.take k).length = k :=
    List.length_take_of_le hkLeLen
  have hPowRaw :=
    (expanding_iff_twoPow_lt_threePow).1
      (hF.properExpanding hkPos hkLtLen)
  have hPow :
      2 ^ prefixTwoDepth w k < 3 ^ k := by
    simpa [prefixTwoDepth, oddSteps, hTakeLen] using hPowRaw
  exact le_criticalHeight_of_twoPow_lt_threePow hPow

/--
FirstCrossing terminal slope に対し critical height 自身も rational chord より strict に下。
-/
theorem FirstCrossing.criticalHeight_below_chord
    {w : Word}
    (hF : FirstCrossing w)
    {k : ℕ}
    (hkPos : 0 < k) :
    oddSteps w * criticalHeight k < twoSteps w * k := by
  have hCrit := criticalHeight_pow_lt_threePow hkPos
  have hWhole :=
    (contracting_iff_threePow_lt_twoPow).1 hF.terminalContracting
  have hpPos : 0 < oddSteps w := by
    simpa [oddSteps] using List.length_pos_iff.mpr hF.nonempty
  have hCritRaisedRaw :=
    Nat.pow_lt_pow_left hCrit (Nat.ne_of_gt hpPos)
  have hCritRaised :
      2 ^ (criticalHeight k * oddSteps w) <
        3 ^ (k * oddSteps w) := by
    calc
      2 ^ (criticalHeight k * oddSteps w)
          = (2 ^ criticalHeight k) ^ oddSteps w := by
              rw [pow_mul]
      _ < (3 ^ k) ^ oddSteps w := hCritRaisedRaw
      _ = 3 ^ (k * oddSteps w) := by
              rw [pow_mul]
  have hWholeRaisedRaw :=
    Nat.pow_lt_pow_left hWhole (Nat.ne_of_gt hkPos)
  have hWholeRaised :
      3 ^ (oddSteps w * k) <
        2 ^ (twoSteps w * k) := by
    calc
      3 ^ (oddSteps w * k)
          = (3 ^ oddSteps w) ^ k := by
              rw [pow_mul]
      _ < (2 ^ twoSteps w) ^ k := hWholeRaisedRaw
      _ = 2 ^ (twoSteps w * k) := by
              rw [pow_mul]
  by_contra hnot
  have hle :
      twoSteps w * k ≤ oddSteps w * criticalHeight k := by
    omega
  have htwo :
      2 ^ (twoSteps w * k) ≤
        2 ^ (oddSteps w * criticalHeight k) :=
    Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hle
  have hleft :
      2 ^ (oddSteps w * criticalHeight k) <
        3 ^ (oddSteps w * k) := by
    simpa [Nat.mul_comm] using hCritRaised
  have hcontra :
      2 ^ (twoSteps w * k) < 2 ^ (twoSteps w * k) :=
    lt_of_le_of_lt htwo (lt_trans hleft hWholeRaised)
  exact (Nat.lt_irrefl _ hcontra)

/-- deterministic strip rank は proper cut で正。 -/
theorem FirstCrossing.stripRank_pos
    {w : Word}
    (hF : FirstCrossing w)
    {k : ℕ}
    (hkPos : 0 < k) :
    0 < stripRank w k := by
  unfold stripRank
  exact Nat.sub_pos_of_lt (hF.criticalHeight_below_chord hkPos)

/--
rank の exact strip decomposition。

  d_k = stripRank(k) + p*extraDepth(k).
-/
theorem FirstCrossing.chordRank_eq_stripRank_add_extraDepth
    {w : Word}
    (hF : FirstCrossing w)
    {k : ℕ}
    (hkPos : 0 < k)
    (hkLt : k < oddSteps w) :
    chordRank w k =
      stripRank w k + oddSteps w * extraDepth w k := by
  let p := oddSteps w
  let H := twoSteps w
  let c := criticalHeight k
  let h := prefixTwoDepth w k
  have hPrefixLe : h ≤ c := by
    simpa [h, c] using hF.prefixTwoDepth_le_criticalHeight hkPos hkLt
  have hCritLt : p * c < H * k := by
    simpa [p, H, c] using hF.criticalHeight_below_chord hkPos
  have hPrefixLt : p * h < H * k := by
    simpa [p, H, h] using hF.prefixSlope_cross hkPos hkLt
  have hStripAdd :
      stripRank w k + p * c = H * k := by
    unfold stripRank
    simpa [p, H, c, Nat.add_comm] using
      Nat.sub_add_cancel (Nat.le_of_lt hCritLt)
  have hExtraAdd :
      extraDepth w k + h = c := by
    unfold extraDepth
    simpa [h, c] using Nat.sub_add_cancel hPrefixLe
  have hRankAdd :
      chordRank w k + p * h = H * k := by
    unfold chordRank
    simpa [p, H, h, Nat.add_comm] using
      Nat.sub_add_cancel (Nat.le_of_lt hPrefixLt)
  have hSame :
      (stripRank w k + p * extraDepth w k) + p * h =
        chordRank w k + p * h := by
    calc
      (stripRank w k + p * extraDepth w k) + p * h
          = stripRank w k + p * (extraDepth w k + h) := by ring
      _ = stripRank w k + p * c := by rw [hExtraAdd]
      _ = H * k := hStripAdd
      _ = chordRank w k + p * h := hRankAdd.symm
  exact (Nat.add_right_cancel hSame).symm

/--
長さ `k` の prefix 自身が contracting なら、その depth は critical height より上。
-/
theorem criticalHeight_lt_prefixTwoDepth_of_contracting_take
    {w : Word}
    {k : ℕ}
    (hkPos : 0 < k)
    (hkLe : k ≤ w.length)
    (hC : Contracting (w.take k)) :
    criticalHeight k < prefixTwoDepth w k := by
  have hTakeLen : (w.take k).length = k :=
    List.length_take_of_le hkLe
  have hPowRaw :=
    (contracting_iff_threePow_lt_twoPow).1 hC
  have hPow :
      3 ^ k < 2 ^ prefixTwoDepth w k := by
    simpa [prefixTwoDepth, oddSteps, hTakeLen] using hPowRaw
  exact criticalHeight_lt_of_threePow_lt_twoPow hkPos hPow

/--
contracting prefix が full rational chord の下側にも残るなら、critical/rational strip は
少なくとも一層を持つ。rank 単位では `p < stripRank`。
-/
theorem stripRank_gt_oddSteps_of_contracting_take_of_rankInt_pos
    {w : Word}
    {k : ℕ}
    (hpPos : 0 < oddSteps w)
    (hkPos : 0 < k)
    (hkLe : k ≤ w.length)
    (hC : Contracting (w.take k))
    (hRank : 0 < chordRankInt w k) :
    oddSteps w < stripRank w k := by
  let p := oddSteps w
  let H := twoSteps w
  let c := criticalHeight k
  let h := prefixTwoDepth w k
  have hCrit : c < h := by
    simpa [c, h] using
      criticalHeight_lt_prefixTwoDepth_of_contracting_take
        hkPos hkLe hC
  have hSlopeZ :
      (p : ℤ) * (h : ℤ) < (H : ℤ) * (k : ℤ) := by
    have hRank' := hRank
    unfold chordRankInt at hRank'
    simpa [p, H, h] using sub_pos.mp hRank'
  have hSlope : p * h < H * k := by
    exact_mod_cast hSlopeZ
  have hCritSucc : c + 1 ≤ h := by omega
  have hMul : p * (c + 1) ≤ p * h :=
    Nat.mul_le_mul_left p hCritSucc
  let A := p * c
  let B := H * k
  have hAB : A + p < B := by
    calc
      A + p = p * (c + 1) := by
        dsimp [A]
        ring
      _ ≤ p * h := hMul
      _ < H * k := hSlope
      _ = B := by rfl
  have hSub : p < B - A := by omega
  simpa [stripRank, p, H, c, A, B] using hSub

end Word
end Collatz2
