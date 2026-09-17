import CollatzLean.Collatz3.Binary.AlternatingWeight
import CollatzLean.Collatz3.Arithmetic.Pow23
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.ModEq
import Mathlib.NumberTheory.PowModTotient
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring


/-!
# Collatz3 Binary: 3進 residue channel weights

mod `3^(K+1)` で `2^i` が繰り返す基本周期

`2 * 3^K`

に従って binary positions を channel に分ける。

`K=0,1,2,...` で channel 数は `2,6,18,...`。
ここでは channel count と周期算術だけを置き、actual Collatz semantics は導入しない。
-/

namespace Collatz3
namespace Binary

/-- depth `K` の 3進 modulus。`K=0` が mod `3`。 -/
def residueDepthModulus (K : ℕ) : ℕ :=
  3 ^ (K + 1)

/-- depth `K` の binary position period。 -/
def residueChannelPeriod (K : ℕ) : ℕ :=
  2 * 3 ^ K

@[simp] theorem residueDepthModulus_pos (K : ℕ) :
    0 < residueDepthModulus K := by
  simp [residueDepthModulus]

@[simp] theorem residueChannelPeriod_pos (K : ℕ) :
    0 < residueChannelPeriod K := by
  simp [residueChannelPeriod]

@[simp] theorem residueDepthModulus_zero :
    residueDepthModulus 0 = 3 := by
  norm_num [residueDepthModulus]

@[simp] theorem residueChannelPeriod_zero :
    residueChannelPeriod 0 = 2 := by
  norm_num [residueChannelPeriod]

/-- channel 数は depth を一つ上げるごとに 3 倍。 -/
theorem residueChannelPeriod_succ (K : ℕ) :
    residueChannelPeriod (K + 1) = 3 * residueChannelPeriod K := by
  simp [residueChannelPeriod, pow_succ]
  ring

/-- modulus も depth を一つ上げるごとに 3 倍。 -/
theorem residueDepthModulus_succ (K : ℕ) :
    residueDepthModulus (K + 1) = 3 * residueDepthModulus K := by
  simp [residueDepthModulus, pow_succ]
  ring

/-- `φ(3^(K+1)) = 2*3^K`。 -/
theorem totient_residueDepthModulus (K : ℕ) :
    (residueDepthModulus K).totient = residueChannelPeriod K := by
  have h := Nat.totient_prime_pow_succ (by decide : Nat.Prime 3) K
  simpa [residueDepthModulus, residueChannelPeriod, Nat.mul_comm] using h

/--
channel period だけ exponent を進めると `2^i` は mod `3^(K+1)` で元へ戻る。
-/
theorem twoPow_residueChannelPeriod_mod_eq_one (K : ℕ) :
    2 ^ residueChannelPeriod K % residueDepthModulus K = 1 := by
  have hMod : 1 < residueDepthModulus K := by
    unfold residueDepthModulus
    exact Nat.one_lt_pow (by omega) (by norm_num)
  have hCop : Nat.Coprime 2 (residueDepthModulus K) := by
    simpa [residueDepthModulus] using
      (Arithmetic.coprime_threePow_twoPow (K + 1) 1).symm
  have hEuler := Nat.pow_totient_mod_eq_one hMod hCop
  rw [totient_residueDepthModulus K] at hEuler
  exact hEuler

/--
絶対 position `index` から読み始めたとき、指定 residue channel に属する `1` の個数。
channel label 自体も period で正規化する。
-/
def residueWeightFrom
    (period residue index : ℕ) : List Bool → ℕ
  | [] => 0
  | b :: bs =>
      (if index % period = residue % period then bitValue b else 0) +
        residueWeightFrom period residue (index + 1) bs

/-- depth `K` の residue channel weight。 -/
def residueWeight
    (K residue : ℕ)
    (bits : List Bool) : ℕ :=
  residueWeightFrom (residueChannelPeriod K) residue 0 bits

@[simp] theorem residueWeightFrom_nil
    (period residue index : ℕ) :
    residueWeightFrom period residue index [] = 0 := rfl

@[simp] theorem residueWeightFrom_cons
    (period residue index : ℕ)
    (b : Bool) (bs : List Bool) :
    residueWeightFrom period residue index (b :: bs) =
      (if index % period = residue % period then bitValue b else 0) +
        residueWeightFrom period residue (index + 1) bs := rfl

/-- channel label は period による residue class だけに依存する。 -/
theorem residueWeightFrom_eq_of_residue_mod_eq
    {period r s index : ℕ}
    (h : r % period = s % period)
    (bits : List Bool) :
    residueWeightFrom period r index bits =
      residueWeightFrom period s index bits := by
  induction bits generalizing index with
  | nil => rfl
  | cons b bs ih =>
      simp [residueWeightFrom, h, ih]

/-- depth 固定後も channel label は period class だけに依存する。 -/
theorem residueWeight_eq_of_residue_mod_eq
    {K r s : ℕ}
    (h : r % residueChannelPeriod K = s % residueChannelPeriod K)
    (bits : List Bool) :
    residueWeight K r bits = residueWeight K s bits := by
  unfold residueWeight
  exact residueWeightFrom_eq_of_residue_mod_eq h bits

/-- `2` はすべての residue-depth modulus と互いに素。 -/
theorem two_coprime_residueDepthModulus (K : ℕ) :
    Nat.Coprime 2 (residueDepthModulus K) := by
  simpa [residueDepthModulus] using
    (Arithmetic.coprime_threePow_twoPow (K + 1) 1).symm

/--
任意 exponent は channel period で還元できる。
これは channel weight が mod `3^(K+1)` の情報を保持する算術的根拠。
-/
theorem twoPow_modeq_periodic
    (K index : ℕ) :
    2 ^ index ≡
      2 ^ (index % residueChannelPeriod K)
        [MOD residueDepthModulus K] := by
  unfold Nat.ModEq
  have hMod : 1 < residueDepthModulus K := by
    unfold residueDepthModulus
    exact Nat.one_lt_pow (by omega) (by norm_num)
  have hReduce :=
    Nat.pow_totient_mod
      (x := 2)
      (k := index)
      (n := residueDepthModulus K)
      hMod
      (two_coprime_residueDepthModulus K)
  rw [totient_residueDepthModulus K] at hReduce
  exact hReduce

/--
各 position の `2^i` を channel representative `2^(i mod period)` に置き換えた有限和。
-/
def periodicResidueValueFrom
    (K index : ℕ) : List Bool → ℕ
  | [] => 0
  | b :: bs =>
      bitValue b * 2 ^ (index % residueChannelPeriod K) +
        periodicResidueValueFrom K (index + 1) bs

/-- LSB position `0` から始める periodic residue value。 -/
def periodicResidueValue
    (K : ℕ)
    (bits : List Bool) : ℕ :=
  periodicResidueValueFrom K 0 bits

/--
通常の binary value を absolute position `index` だけ左 shift した値と、
periodic residue value は mod `3^(K+1)` で一致する。
-/
theorem shiftedValue_modeq_periodicResidueValueFrom
    (K index : ℕ)
    (bits : List Bool) :
    2 ^ index * valueLSB bits ≡
      periodicResidueValueFrom K index bits
        [MOD residueDepthModulus K] := by
  induction bits generalizing index with
  | nil =>
      simp [periodicResidueValueFrom]
      rfl
  | cons b bs ih =>
      have hHead :
          bitValue b * 2 ^ index ≡
            bitValue b *
              2 ^ (index % residueChannelPeriod K)
              [MOD residueDepthModulus K] :=
        (twoPow_modeq_periodic K index).mul_left (bitValue b)
      have hTail := ih (index + 1)
      have hAdd := hHead.add hTail
      calc
        2 ^ index * valueLSB (b :: bs)
            = bitValue b * 2 ^ index +
                2 ^ (index + 1) * valueLSB bs := by
                  simp only [valueLSB_cons, pow_succ]
                  ring
        _ ≡
            bitValue b *
                2 ^ (index % residueChannelPeriod K) +
              periodicResidueValueFrom K (index + 1) bs
              [MOD residueDepthModulus K] := hAdd
        _ = periodicResidueValueFrom K index (b :: bs) := rfl

/-- binary value 自身と periodic residue value は同じ 3進 residue を持つ。 -/
theorem valueLSB_modeq_periodicResidueValue
    (K : ℕ)
    (bits : List Bool) :
    valueLSB bits ≡ periodicResidueValue K bits
      [MOD residueDepthModulus K] := by
  simpa [periodicResidueValue] using
    shiftedValue_modeq_periodicResidueValueFrom K 0 bits

/--
深さ `K=0`、すなわち mod `3` では alternating weight が residue を決める。
減算を避けて `value + oddWeight ≡ evenWeight` と書く。
-/
theorem valueLSB_add_oddOneCount_mod_three
    (bits : List Bool) :
    valueLSB bits + oddOneCount bits ≡
      evenOneCount bits [MOD 3] := by
  induction bits with
  | nil =>
      simp
      rfl
  | cons b bs ih =>
      have hCore₁ :
          2 * valueLSB bs + evenOneCount bs ≡
            2 * valueLSB bs +
              (valueLSB bs + oddOneCount bs) [MOD 3] :=
        ih.symm.add_left (2 * valueLSB bs)
      have hCore₂ :
          2 * valueLSB bs +
              (valueLSB bs + oddOneCount bs) ≡
            oddOneCount bs [MOD 3] := by
        have hMod :
            3 * valueLSB bs + oddOneCount bs ≡
              oddOneCount bs [MOD 3] :=
          Nat.ModEq.modulus_mul_add
        convert hMod using 1
        ring
      have hCore := hCore₁.trans hCore₂
      have hBit := hCore.add_left (bitValue b)
      simpa [valueLSB, evenOneCount, oddOneCount,
        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hBit

namespace HasAlternatingWeight

/-- alternating weight realization の mod `3` residue law。 -/
theorem mod_three
    {x evenWeight oddWeight length : ℕ}
    (h : HasAlternatingWeight x evenWeight oddWeight length) :
    x + oddWeight ≡ evenWeight [MOD 3] := by
  rcases h with ⟨bits, hRep, hEven, hOdd⟩
  have hMod := valueLSB_add_oddOneCount_mod_three bits
  rw [hRep.value, hEven, hOdd] at hMod
  exact hMod

end HasAlternatingWeight

end Binary
end Collatz3
