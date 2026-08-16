import CollatzLean.Collatz2.CSTMicro.PolynomialCapacity

/-!
# General CST: inverse parity path sums

standard parity cylinder の canonical class を、
parity word 上の二つの 2-adic weighted sums として読む。

odd positions 版:

  R(P) ≡ - Σ_{s_i = 1} 2^i 3^{-σ_{i+1}}  (mod 2^k)

zero positions 版:

  R(P) ≡ -1 - Σ_{s_i = 0} 2^i 3^{-σ_i}  (mod 2^k)

ここで `σ_i` は時刻 `i` より前の odd step 数。
分数は使わず、`ZMod (2^k)` 内の 3 の unit inverse で表す。
-/

namespace Collatz2
namespace CSTMicro

/-- `ZMod (2^k)` における 3 の unit。 -/
def threeUnitAtLength (k : ℕ) : (ZMod (2 ^ k))ˣ :=
  ZMod.unitOfCoprime
    3
    ((by decide : Nat.Coprime 3 2).pow_right k)

/-- `3^{-a}` in `ZMod (2^k)`。 -/
def invThreePow (k a : ℕ) : ZMod (2 ^ k) :=
  (↑((threeUnitAtLength k)⁻¹) : ZMod (2 ^ k)) ^ a

@[simp] theorem threeUnitAtLength_coe (k : ℕ) :
    (↑(threeUnitAtLength k) : ZMod (2 ^ k)) = 3 := by
  simp [threeUnitAtLength]

@[simp] theorem invThreePow_zero (k : ℕ) :
    invThreePow k 0 = 1 := by
  simp [invThreePow]

@[simp] theorem invThreePow_succ (k a : ℕ) :
    invThreePow k (a + 1) =
      invThreePow k a * invThreePow k 1 := by
  simp [invThreePow, pow_succ]

/-- `3^a * 3^{-a} = 1` in `ZMod (2^k)`。 -/
theorem threePow_mul_invThreePow (k a : ℕ) :
    (3 : ZMod (2 ^ k)) ^ a * invThreePow k a = 1 := by
  rw [invThreePow]
  rw [← threeUnitAtLength_coe]
  rw [← mul_pow]
  have hu :
      (↑(threeUnitAtLength k) : ZMod (2 ^ k)) *
          (↑((threeUnitAtLength k)⁻¹) : ZMod (2 ^ k)) = 1 := by
    simp
  rw [hu]
  simp

/-- `3 * 3^{-(a+1)} = 3^{-a}`。 -/
theorem three_mul_invThreePow_succ (k a : ℕ) :
    (3 : ZMod (2 ^ k)) * invThreePow k (a + 1) =
      invThreePow k a := by
  have h1 := threePow_mul_invThreePow k 1
  have hthree :
      (3 : ZMod (2 ^ k)) * invThreePow k 1 = 1 := by
    simpa only [pow_one] using h1
  rw [invThreePow_succ]
  calc
    (3 : ZMod (2 ^ k)) *
          (invThreePow k a * invThreePow k 1)
        = invThreePow k a *
            ((3 : ZMod (2 ^ k)) * invThreePow k 1) := by
              ac_rfl
    _ = invThreePow k a := by
      rw [hthree]
      simp

/-- odd positions の正の weighted contribution scan。 -/
def oddInverseContributionScan
    (K : ℕ) : ParityWord → ℕ → ℕ → ZMod (2 ^ K)
  | [], _i, _a => 0
  | false :: v, i, a =>
      oddInverseContributionScan K v (i + 1) a
  | true :: v, i, a =>
      (2 : ZMod (2 ^ K)) ^ i * invThreePow K (a + 1) +
        oddInverseContributionScan K v (i + 1) (a + 1)

/-- zero positions の正の weighted contribution scan。 -/
def zeroInverseContributionScan
    (K : ℕ) : ParityWord → ℕ → ℕ → ZMod (2 ^ K)
  | [], _i, _a => 0
  | false :: v, i, a =>
      (2 : ZMod (2 ^ K)) ^ i * invThreePow K a +
        zeroInverseContributionScan K v (i + 1) a
  | true :: v, i, a =>
      zeroInverseContributionScan K v (i + 1) (a + 1)

/-- telescoping boundary term `2^i 3^{-a}`。 -/
def inverseBoundaryTerm
    (K i a : ℕ) : ZMod (2 ^ K) :=
  (2 : ZMod (2 ^ K)) ^ i * invThreePow K a

/--
odd contribution を `3^(a+ones)` で戻すと、
exact に affine numerator の shifted copy になる。
-/
theorem oddInverseContributionScan_scaled
    (K : ℕ) (v : ParityWord) (i a : ℕ) :
    (3 : ZMod (2 ^ K)) ^ (a + oddCount v) *
        oddInverseContributionScan K v i a
      =
    (2 : ZMod (2 ^ K)) ^ i *
      ((affineConst v : ℕ) : ZMod (2 ^ K)) := by
  induction v generalizing i a with
  | nil =>
      simp [oddInverseContributionScan, oddCount, affineConst]
  | cons b v ih =>
      cases b
      · have hih := ih (i := i + 1) (a := a)
        simp only [oddInverseContributionScan, oddCount_false_cons,
          affineConst_false_cons] at hih ⊢
        rw [hih, pow_succ]
        push_cast
        ring
      · have hih := ih (i := i + 1) (a := a + 1)
        have hInv := threePow_mul_invThreePow K (a + 1)
        simp only [oddInverseContributionScan, oddCount_true_cons,
          affineConst_true_cons]
        have hexp :
            a + (oddCount v + 1) = (a + 1) + oddCount v := by
          omega
        rw [hexp, mul_add]
        have hfirst :
            (3 : ZMod (2 ^ K)) ^ ((a + 1) + oddCount v) *
                ((2 : ZMod (2 ^ K)) ^ i * invThreePow K (a + 1))
              =
            (2 : ZMod (2 ^ K)) ^ i *
              (3 : ZMod (2 ^ K)) ^ oddCount v := by
          rw [pow_add]
          calc
            ((3 : ZMod (2 ^ K)) ^ (a + 1) *
                  (3 : ZMod (2 ^ K)) ^ oddCount v) *
                ((2 : ZMod (2 ^ K)) ^ i * invThreePow K (a + 1))
                =
                (2 : ZMod (2 ^ K)) ^ i *
                  ((3 : ZMod (2 ^ K)) ^ (a + 1) *
                    invThreePow K (a + 1)) *
                  (3 : ZMod (2 ^ K)) ^ oddCount v := by ring
            _ =
                (2 : ZMod (2 ^ K)) ^ i *
                  (3 : ZMod (2 ^ K)) ^ oddCount v := by
                    rw [hInv]
                    ring
        rw [hfirst, hih, pow_succ]
        push_cast
        ring

/--
odd contribution と zero contribution の差は boundary term の telescoping。
-/
theorem odd_sub_zero_inverseContributionScan
    (K : ℕ) (v : ParityWord) (i a : ℕ) :
    oddInverseContributionScan K v i a -
        zeroInverseContributionScan K v i a
      =
    inverseBoundaryTerm K i a -
      inverseBoundaryTerm K (i + v.length) (a + oddCount v) := by
  induction v generalizing i a with
  | nil =>
      simp [oddInverseContributionScan, zeroInverseContributionScan,
        inverseBoundaryTerm, oddCount]
  | cons b v ih =>
      cases b
      · have hih := ih (i := i + 1) (a := a)
        have hstep :
            inverseBoundaryTerm K (i + 1) a =
              2 * inverseBoundaryTerm K i a := by
          simp [inverseBoundaryTerm, pow_succ]
          ring
        have hidx : i + (v.length + 1) = (i + 1) + v.length := by
          omega
        simp only [oddInverseContributionScan, zeroInverseContributionScan,
          oddCount_false_cons, List.length_cons]
        calc
          oddInverseContributionScan K v (i + 1) a -
              ((2 : ZMod (2 ^ K)) ^ i * invThreePow K a +
                zeroInverseContributionScan K v (i + 1) a)
              =
              (oddInverseContributionScan K v (i + 1) a -
                zeroInverseContributionScan K v (i + 1) a) -
                inverseBoundaryTerm K i a := by
                  simp [inverseBoundaryTerm]
                  ring
          _ =
              (inverseBoundaryTerm K (i + 1) a -
                inverseBoundaryTerm K ((i + 1) + v.length)
                  (a + oddCount v)) -
                inverseBoundaryTerm K i a := by
                  rw [hih]
          _ =
              inverseBoundaryTerm K i a -
                inverseBoundaryTerm K (i + (v.length + 1))
                  (a + oddCount v) := by
                    rw [hstep, hidx]
                    ring
      · have hih := ih (i := i + 1) (a := a + 1)
        have hstep :
            (2 : ZMod (2 ^ K)) ^ i * invThreePow K (a + 1) +
                inverseBoundaryTerm K (i + 1) (a + 1)
              =
            inverseBoundaryTerm K i a := by
          unfold inverseBoundaryTerm
          rw [pow_succ]
          have hthree := three_mul_invThreePow_succ K a
          calc
            (2 : ZMod (2 ^ K)) ^ i * invThreePow K (a + 1) +
                ((2 : ZMod (2 ^ K)) ^ i * 2) *
                  invThreePow K (a + 1)
                =
                (2 : ZMod (2 ^ K)) ^ i *
                  (3 * invThreePow K (a + 1)) := by ring
            _ =
                (2 : ZMod (2 ^ K)) ^ i * invThreePow K a := by
                  rw [hthree]
        have hidx : i + (v.length + 1) = (i + 1) + v.length := by
          omega
        have hodd :
            a + (oddCount v + 1) = (a + 1) + oddCount v := by
          omega
        simp only [oddInverseContributionScan, zeroInverseContributionScan,
          oddCount_true_cons, List.length_cons]
        calc
          ((2 : ZMod (2 ^ K)) ^ i * invThreePow K (a + 1) +
              oddInverseContributionScan K v (i + 1) (a + 1)) -
              zeroInverseContributionScan K v (i + 1) (a + 1)
              =
              (2 : ZMod (2 ^ K)) ^ i * invThreePow K (a + 1) +
                (oddInverseContributionScan K v (i + 1) (a + 1) -
                  zeroInverseContributionScan K v (i + 1) (a + 1)) := by
                    ring
          _ =
              (2 : ZMod (2 ^ K)) ^ i * invThreePow K (a + 1) +
                (inverseBoundaryTerm K (i + 1) (a + 1) -
                  inverseBoundaryTerm K ((i + 1) + v.length)
                    ((a + 1) + oddCount v)) := by
                      rw [hih]
          _ =
              inverseBoundaryTerm K i a -
                inverseBoundaryTerm K (i + (v.length + 1))
                  (a + (oddCount v + 1)) := by
                    rw [hidx, hodd]
                    rw [← hstep]
                    ring

/-- Rozier odd-position inverse path sum。 -/
def inverseOddPathSum (v : ParityWord) : ZMod (parityModulus v) := by
  unfold parityModulus
  exact
    -oddInverseContributionScan v.length v 0 0

/-- complementary zero-position inverse path sum。 -/
def inverseZeroPathSum (v : ParityWord) : ZMod (parityModulus v) := by
  unfold parityModulus
  exact
    (-1 : ZMod (2 ^ v.length)) -
      zeroInverseContributionScan v.length v 0 0

/-- odd-position inverse formula は defining congruence を満たす。 -/
theorem inverseOddPathSum_spec (v : ParityWord) :
    (((3 ^ oddCount v : ℕ) : ZMod (parityModulus v)) *
        inverseOddPathSum v) +
      ((affineConst v : ℕ) : ZMod (parityModulus v)) = 0 := by
  have h := oddInverseContributionScan_scaled v.length v 0 0
  change
    (((3 ^ oddCount v : ℕ) : ZMod (2 ^ v.length)) *
        (-oddInverseContributionScan v.length v 0 0)) +
      ((affineConst v : ℕ) : ZMod (2 ^ v.length)) = 0
  push_cast
  have h' :
      (3 : ZMod (2 ^ v.length)) ^ oddCount v *
          oddInverseContributionScan v.length v 0 0 =
        ((affineConst v : ℕ) : ZMod (2 ^ v.length)) := by
    simpa using h
  calc
    (3 : ZMod (2 ^ v.length)) ^ oddCount v *
          (-oddInverseContributionScan v.length v 0 0) +
        ((affineConst v : ℕ) : ZMod (2 ^ v.length))
        =
        -((3 : ZMod (2 ^ v.length)) ^ oddCount v *
          oddInverseContributionScan v.length v 0 0) +
        ((affineConst v : ℕ) : ZMod (2 ^ v.length)) := by
          ring
    _ = 0 := by
      rw [h']
      ring

/-- odd-position inverse formula は canonical parity class そのもの。 -/
theorem inverseOddPathSum_eq_parityStartClass (v : ParityWord) :
    inverseOddPathSum v = parityStartClass v := by
  apply parityStartClass_unique
  exact inverseOddPathSum_spec v

/-- terminal boundary `2^k 3^{-m}` は modulus `2^k` 上で 0。 -/
private theorem terminal_inverseBoundaryTerm_zero (v : ParityWord) :
    inverseBoundaryTerm v.length v.length (oddCount v) = 0 := by
  unfold inverseBoundaryTerm
  have htwo :
      (2 : ZMod (2 ^ v.length)) =
        ((2 : ℕ) : ZMod (2 ^ v.length)) := by
    norm_num
  rw [htwo, ← Nat.cast_pow]
  simp

/-- odd sum と zero sum は同じ parity class を表す。 -/
theorem inverseZeroPathSum_eq_inverseOddPathSum (v : ParityWord) :
    inverseZeroPathSum v = inverseOddPathSum v := by
  have h := odd_sub_zero_inverseContributionScan v.length v 0 0
  have hstart : inverseBoundaryTerm v.length 0 0 = 1 := by
    simp [inverseBoundaryTerm]
  have hend := terminal_inverseBoundaryTerm_zero v
  have htel :
      oddInverseContributionScan v.length v 0 0 -
          zeroInverseContributionScan v.length v 0 0 = 1 := by
    simpa [hstart, hend] using h
  have hsum :
      oddInverseContributionScan v.length v 0 0 =
        1 + zeroInverseContributionScan v.length v 0 0 := by
    exact (sub_eq_iff_eq_add).1 htel
  change
    -1 - zeroInverseContributionScan v.length v 0 0 =
      -oddInverseContributionScan v.length v 0 0
  rw [hsum]
  ring

/-- zero-position inverse formula も canonical parity class そのもの。 -/
theorem inverseZeroPathSum_eq_parityStartClass (v : ParityWord) :
    inverseZeroPathSum v = parityStartClass v := by
  rw [inverseZeroPathSum_eq_inverseOddPathSum,
    inverseOddPathSum_eq_parityStartClass]

/-- canonical class の least representative を modulus へ戻す。 -/
theorem leastRepresentative_cast (v : ParityWord) :
    ((leastRepresentative v : ℕ) : ZMod (parityModulus v)) =
      parityStartClass v := by
  haveI : NeZero (parityModulus v) :=
    ⟨by simp [parityModulus]⟩
  simp only [leastRepresentative, ZMod.natCast_val, ZMod.cast_id', id_eq]

/-- `R(P)` は odd-position inverse sum の ordinary representative。 -/
theorem leastRepresentative_eq_inverseOddPathSum_val (v : ParityWord) :
    leastRepresentative v = (inverseOddPathSum v).val := by
  rw [inverseOddPathSum_eq_parityStartClass]
  rfl

/-- `R(P)` は zero-position inverse sum の ordinary representative。 -/
theorem leastRepresentative_eq_inverseZeroPathSum_val (v : ParityWord) :
    leastRepresentative v = (inverseZeroPathSum v).val := by
  rw [inverseZeroPathSum_eq_parityStartClass]
  rfl

end CSTMicro
end Collatz2
