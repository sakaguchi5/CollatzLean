import CollatzLean.Collatz.AdjacentReturn.PositiveReturn.NaturalZeroReplay
import CollatzLean.Collatz.Arithmetic.Growth

/-!
# first overshoot の replay saturation

PositiveReturn canonical chain では first-crossing endpoint は length の固定多項式で抑えられる。
一方 first overshoot cut `r` は `6*r < p` を満たすので、残り suffix 長 `p-r` は線形に増える。
従って十分長い chain 項では endpoint は suffix replay 幅 `2*3^(p-r)` より小さくなる。

これにより、PositiveReturn chain から自然な `j=0` sign-change packet が eventual に得られる。
-/

namespace Collatz
namespace AdjacentReturn
namespace PositiveReturn
namespace CanonicalChain

/-- Baker 型 endpoint bound を通常の固定多項式 bound に緩める。 -/
theorem endpoint_le_simple_polynomial
    {O : OddOrbit} (C : CanonicalChain O) :
    ∃ K A : ℕ,
      ∀ n : ℕ,
        (C.firstCrossing n).endpointValue ≤
          K * ((C.firstCrossing n).length + 1) ^ A := by
  obtain ⟨K, A, h⟩ := C.endpoint_polynomial_bound
  refine ⟨K, A + 1, ?_⟩
  intro n
  let F := C.firstCrossing n
  let p := F.length
  let T := F.endpointValue
  have hmain :
      3 * T ≤ F.returnSlack * (K * (p + 1) ^ A) := by
    simpa [F, p, T] using h n
  have hslack : F.returnSlack ≤ p + 1 := by
    dsimp [FirstCrossingData.returnSlack, p]
    omega
  have hTthree : T ≤ 3 * T := by omega
  calc
    T ≤ 3 * T := hTthree
    _ ≤ F.returnSlack * (K * (p + 1) ^ A) := hmain
    _ ≤ (p + 1) * (K * (p + 1) ^ A) :=
      Nat.mul_le_mul_right (K * (p + 1) ^ A) hslack
    _ = K * (p + 1) ^ (A + 1) := by
      rw [pow_succ]
      ring
    _ = K * (F.length + 1) ^ (A + 1) := by rfl

/--
`6*r < p` なら `p` の多項式は `q=p-r` の固定係数多項式へ移せる。
-/
private theorem polynomial_transfer_to_long_suffix
    (K A p r : ℕ)
    (hr : 6 * r < p) :
    K * (p + 1) ^ A ≤
      (K * 2 ^ A) * ((p - r) + 1) ^ A := by
  have hrLe : r ≤ p := by omega
  have hbase : p + 1 ≤ 2 * ((p - r) + 1) := by
    omega
  have hpow :
      (p + 1) ^ A ≤ (2 * ((p - r) + 1)) ^ A := by
    exact Nat.pow_le_pow_left hbase A
  calc
    K * (p + 1) ^ A
        ≤ K * (2 * ((p - r) + 1)) ^ A :=
      Nat.mul_le_mul_left K hpow
    _ = (K * 2 ^ A) * ((p - r) + 1) ^ A := by
      rw [mul_pow]
      ring

/-- sufficiently long な chain 項では first overshoot cut が replay-zero threshold 内に入る。 -/
theorem eventually_firstOvershoot_endpoint_lt_replayWidth
    {O : OddOrbit} (C : CanonicalChain O) :
    ∃ J : ℕ,
      ∀ n : ℕ, J ≤ n →
        (C.firstCrossing n).endpointValue <
          2 * 3 ^ Word.oddSteps
            (FirstCrossingData.suffixWord
              (C.firstCrossing n)
              (FirstCrossingData.firstOvershootCut
                (C.firstCrossing n))) := by
  obtain ⟨K, A, hpoly⟩ := C.endpoint_le_simple_polynomial
  let K' := K * 2 ^ A
  obtain ⟨N, hN⟩ :=
    Arithmetic.polynomialBelowTwoMulThreePower K' A
  obtain ⟨J, hJ⟩ := C.lengths_tend_to_infinity (2 * N)
  refine ⟨J, ?_⟩
  intro n hn
  let F := C.firstCrossing n
  let p := F.length
  let r := FirstCrossingData.firstOvershootCut F
  let q := p - r
  have hpLarge : 2 * N < p := by
    simpa [F, p] using hJ n hn
  have hr : 6 * r < p := by
    simpa [r] using FirstCrossingData.six_mul_firstOvershootCut_lt_length F
  have hqLarge : N ≤ q := by
    dsimp [q]
    omega
  have hT : F.endpointValue ≤ K * (p + 1) ^ A := by
    simpa [F, p] using hpoly n
  have htransfer :
      K * (p + 1) ^ A ≤ K' * (q + 1) ^ A := by
    simpa [K', q] using
      polynomial_transfer_to_long_suffix K A p r hr
  have hgrowth :
      K' * (q + 1) ^ A < 2 * 3 ^ q :=
    hN q hqLarge
  have hsmall : F.endpointValue < 2 * 3 ^ q :=
    lt_of_le_of_lt (le_trans hT htransfer) hgrowth
  simpa [F, p, r, q, Word.oddSteps, FirstCrossingData.suffixWord] using hsmall

/-- PositiveReturn chain では自然な sign-change j=0 packet が eventually 現れる。 -/
theorem eventually_naturalZeroReplaySignChange
    {O : OddOrbit} (C : CanonicalChain O) :
    ∃ J : ℕ,
      ∀ n : ℕ, J ≤ n →
        Nonempty
          (FirstCrossingData.NaturalZeroReplaySignChangeData
            (C.firstCrossing n)) := by
  obtain ⟨J, hJ⟩ := C.eventually_firstOvershoot_endpoint_lt_replayWidth
  refine ⟨J, ?_⟩
  intro n hn
  exact ⟨
    FirstCrossingData.naturalZeroReplaySignChange_of_endpoint_lt
      (C.firstCrossing n) (hJ n hn)
  ⟩

end CanonicalChain

/--
新しい局所 proof target。
任意の actual first crossing に natural zero-replay sign-change packet は存在しない、という原理。
-/
def NoNaturalZeroReplaySignChange : Prop :=
  ∀ {O : OddOrbit} {R : State O}
    (F : FirstCrossingData R),
    FirstCrossingData.NaturalZeroReplaySignChangeData F → False

/-- 上の局所原理だけで PositiveReturn canonical chain 全体を排除できる。 -/
theorem no_canonicalChain_of_noNaturalZeroReplaySignChange
    (hNo : NoNaturalZeroReplaySignChange) :
    ¬ HasCanonicalChain := by
  rintro ⟨O, ⟨C⟩⟩
  obtain ⟨J, hJ⟩ := C.eventually_naturalZeroReplaySignChange
  obtain ⟨D⟩ := hJ J le_rfl
  exact hNo (C.firstCrossing J) D

end PositiveReturn
end AdjacentReturn
end Collatz
