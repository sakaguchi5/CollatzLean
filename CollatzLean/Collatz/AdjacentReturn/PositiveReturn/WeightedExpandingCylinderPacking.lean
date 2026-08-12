import CollatzLean.Collatz.AdjacentReturn.PositiveReturn.CommonCorridorSeparation
import Mathlib.Data.Finset.Basic

/-!
# expanding cylinder の weighted finite packing

長さ `L` の expanding prefix `w` は odd starts の一つの canonical cylinder
(modulus `2^(twoSteps w + 1)`) を決める。

このファイルでは reciprocal weight を直接扱わず、共通 dyadic denominator `2^H`
を用いて

  `scaledWeight(K) = 2^(H-K)`

とする。有限 bucket family の count を `c_a` とすると、weighted pigeonhole は

  `T * scaledWeight(K_a) <= c_a * totalScaledMass`

を満たす bucket を一つ与える。

さらに expanding-cylinder mass estimate

  `20^L * totalScaledMass < 19^L * 2^H`

が与えられれば、共通因子を exact に消去して

  `T * 20^L < c_a * 2^K_a * 19^L`

を得る。これは

  `(c_a / T) * 2^K_a > (20/19)^L`

の自然数版であり、frequency × separation modulus の exponential pressure を
除算なしで保持する。

mass estimate 自体と finite chain window の bucket 構成をこの integer kernel から
分離しておくことで、後続の packing / anchored-cancellation の双方から再利用できる。
-/

namespace Collatz

namespace Word

/--
長さ `5*m` の expanding word は total exponent が `8*m` 未満。
`3^5 = 243 < 256 = 2^8` だけを使う粗い rational slope bound。
-/
theorem Expanding.twoSteps_lt_eight_mul_of_length_eq_five_mul
    {w : Collatz.Word} (hE : w.Expanding)
    {m : ℕ}
    (hm : 0 < m)
    (hlen : w.length = 5 * m) :
    w.twoSteps < 8 * m := by
  have hpow :
      2 ^ w.twoSteps < 3 ^ (5 * m) := by
    change 2 ^ w.twoSteps < 3 ^ w.oddSteps at hE
    simpa [Word.oddSteps, hlen] using hE
  have hbase : (3 : ℕ) ^ 5 < 2 ^ 8 := by
    norm_num
  have h35lt28 :
      3 ^ (5 * m) < 2 ^ (8 * m) := by
    calc
      3 ^ (5 * m) = (3 ^ 5) ^ m := by rw [pow_mul]
      _ < (2 ^ 8) ^ m := Nat.pow_lt_pow_left hbase (Nat.ne_of_gt hm)
      _ = 2 ^ (8 * m) := by rw [pow_mul]
  by_contra hnot
  have hle : 8 * m ≤ w.twoSteps := by omega
  have hmono : 2 ^ (8 * m) ≤ 2 ^ w.twoSteps :=
    Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hle
  omega

end Word

namespace AdjacentReturn
namespace PositiveReturn

/-- 共通 dyadic denominator `2^H` に持ち上げた cylinder weight。 -/
def scaledCylinderWeight (H K : ℕ) : ℕ :=
  2 ^ (H - K)

/-- finite bucket family の総 scaled cylinder mass。 -/
def scaledCylinderMass
    {α : Type*}
    (S : Finset α) (exponent : α → ℕ) (H : ℕ) : ℕ :=
  Finset.sum S (fun a => scaledCylinderWeight H (exponent a))

/--
有限 family に対する weighted pigeonhole の除算なし整数形。

`T = sum c_a` とすると、ある bucket `a` で

  `T*w_a <= c_a*sum(w)`

が成立する。
-/
theorem weightedCylinderPigeonhole
    {α : Type*}
    (S : Finset α)
    (count exponent : α → ℕ)
    (H T : ℕ)
    (hTotal : Finset.sum S count = T)
    (hTPos : 0 < T) :
    ∃ a ∈ S,
      T * scaledCylinderWeight H (exponent a) ≤
        count a * scaledCylinderMass S exponent H := by
  let W := scaledCylinderMass S exponent H
  have hSne : S.Nonempty := by
    by_contra hEmpty
    have hSempty : S = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hEmpty
    rw [hSempty] at hTotal
    simp at hTotal
    omega
  by_contra hNo
  push Not at hNo
  have hEach :
      ∀ a ∈ S,
        count a * W <
          T * scaledCylinderWeight H (exponent a) := by
    intro a ha
    exact hNo a ha
  have hSumLt :
      Finset.sum S (fun a => count a * W) <
        Finset.sum S
          (fun a => T * scaledCylinderWeight H (exponent a)) := by
    apply Finset.sum_lt_sum
    · intro a ha
      exact Nat.le_of_lt (hEach a ha)
    · obtain ⟨a, ha⟩ := hSne
      exact ⟨a, ha, hEach a ha⟩
  have hLeft :
      Finset.sum S (fun a => count a * W) = T * W := by
    calc
      Finset.sum S (fun a => count a * W)
          = Finset.sum S count * W := by
              rw [Finset.sum_mul]
      _ = T * W := by
        rw [hTotal]
  have hRight :
      Finset.sum S
          (fun a => T * scaledCylinderWeight H (exponent a))
        = T * W := by
    calc
      Finset.sum S
          (fun a => T * scaledCylinderWeight H (exponent a))
          = T * Finset.sum S
              (fun a => scaledCylinderWeight H (exponent a)) := by
              rw [Finset.mul_sum]
      _ = T * W := by
        rfl
  rw [hLeft, hRight] at hSumLt
  exact (Nat.lt_irrefl _ hSumLt)

/--
expanding-cylinder mass が `(19/20)^L` より小さいことを common denominator で
与えたときの weighted finite packing。

結論

  `T * 20^L < c_a * 2^K_a * 19^L`

は `frequency * 2^K > (20/19)^L` の exact integer form。
-/
theorem weightedExpandingCylinderPacking
    {α : Type*}
    (S : Finset α)
    (count exponent : α → ℕ)
    (H L T : ℕ)
    (hExponent : ∀ a ∈ S, exponent a ≤ H)
    (hTotal : Finset.sum S count = T)
    (hTPos : 0 < T)
    (hMass :
      20 ^ L * scaledCylinderMass S exponent H <
        19 ^ L * 2 ^ H) :
    ∃ a ∈ S,
      T * 20 ^ L <
        count a * 2 ^ exponent a * 19 ^ L := by
  obtain ⟨a, ha, hPack⟩ :=
    weightedCylinderPigeonhole S count exponent H T hTotal hTPos
  let d := H - exponent a
  have hKle : exponent a ≤ H :=
    hExponent a ha
  have hHsplit : H = d + exponent a := by
    dsimp [d]
    exact (Nat.sub_add_cancel hKle).symm
  have hPowSplit : 2 ^ H = 2 ^ d * 2 ^ exponent a := by
    rw [hHsplit, pow_add]
  have hWeight :
      scaledCylinderWeight H (exponent a) = 2 ^ d := by
    rfl
  rw [hWeight] at hPack
  have hPowDPos : 0 < 2 ^ d :=
    Nat.pow_pos (by omega)
  have hCountPos : 0 < count a := by
    by_contra hnot
    have hzero : count a = 0 := by
      omega
    rw [hzero] at hPack
    simp only [zero_mul, nonpos_iff_eq_zero, mul_eq_zero, Nat.pow_eq_zero,
      OfNat.ofNat_ne_zero, ne_eq, false_and,
    or_false] at hPack
    have hleftPos : 0 < T * 2 ^ d :=
      Nat.mul_pos hTPos hPowDPos
    omega
  have hPackScaled :
      (T * 20 ^ L) * 2 ^ d ≤
        count a * (20 ^ L * scaledCylinderMass S exponent H) := by
    have h := Nat.mul_le_mul_left (20 ^ L) hPack
    calc
      (T * 20 ^ L) * 2 ^ d
          = 20 ^ L * (T * 2 ^ d) := by
              ring
      _ ≤ 20 ^ L *
          (count a * scaledCylinderMass S exponent H) := h
      _ = count a *
          (20 ^ L * scaledCylinderMass S exponent H) := by
              ring
  have hMassScaled :
      count a * (20 ^ L * scaledCylinderMass S exponent H) <
        count a * (19 ^ L * 2 ^ H) :=
    (Nat.mul_lt_mul_left hCountPos).2 hMass
  have hCombined :
      (T * 20 ^ L) * 2 ^ d <
        (count a * 2 ^ exponent a * 19 ^ L) * 2 ^ d := by
    calc
      (T * 20 ^ L) * 2 ^ d
          ≤ count a *
              (20 ^ L * scaledCylinderMass S exponent H) :=
        hPackScaled
      _ < count a * (19 ^ L * 2 ^ H) :=
        hMassScaled
      _ = (count a * 2 ^ exponent a * 19 ^ L) * 2 ^ d := by
        rw [hPowSplit]
        ring
  have hPressure :
      T * 20 ^ L <
        count a * 2 ^ exponent a * 19 ^ L :=
    (Nat.mul_lt_mul_right hPowDPos).1 hCombined
  exact ⟨a, ha, hPressure⟩

end PositiveReturn
end AdjacentReturn
end Collatz
