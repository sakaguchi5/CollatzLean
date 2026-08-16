import CollatzLean.Collatz2.CSTMicro.MicroObject
import CollatzLean.Collatz2.External.TwoThreeGap

/-!
# General CST: polynomial upper bound for Archimedean capacity

`FirstPassagePath` の proper prefix expanding 条件から、
standard parity affine numerator を

  B(P) ≤ m * 3^m

で抑える。ここで `m = endpointOddCount P`。

さらに既存の Baker / Matveev 型 interface
`External.TwoThreeGapPolynomialBound` の witness

  3^m ≤ K * (m+1)^A * (2^k - 3^m)

を接続して

  Cap(P) ≤ m * K * (m+1)^A
         ≤ k * K * (k+1)^A
         ≤ K * (k+1)^(A+1)

を得る。

これにより general CST の Archimedean side は
length に関する explicit polynomial majorant に落ちる。
-/

namespace Collatz2
namespace CSTMicro

@[simp] theorem oddCount_false_cons (v : ParityWord) :
    oddCount (false :: v) = oddCount v := by
  simp [oddCount, bitNat]

@[simp] theorem oddCount_true_cons (v : ParityWord) :
    oddCount (true :: v) = oddCount v + 1 := by
  simp [oddCount, bitNat, Nat.add_comm]

@[simp] theorem prefixOddCount_zero (v : ParityWord) :
    prefixOddCount v 0 = 0 := by
  simp [prefixOddCount, oddCount]

@[simp] theorem prefixOddCount_cons_succ
    (b : Bool) (v : ParityWord) (j : ℕ) :
    prefixOddCount (b :: v) (j + 1) =
      bitNat b + prefixOddCount v j := by
  simp [prefixOddCount, oddCount]

/-- binary word の odd count は length 以下。 -/
theorem oddCount_le_length (v : ParityWord) :
    oddCount v ≤ v.length := by
  induction v with
  | nil =>
      simp [oddCount]
  | cons b v ih =>
      cases b <;> simp [oddCount, bitNat] at * <;> omega

/--
左から parity word を読む affine accumulator。

`B` を current affine numerator、`k` を current standard time として
odd step で `B <- 3B + 2^k`、even step では `B` を保つ。
-/
def affineScan : ParityWord → ℕ → ℕ → ℕ
  | [], _k, B => B
  | false :: v, k, B => affineScan v (k + 1) B
  | true :: v, k, B => affineScan v (k + 1) (3 * B + 2 ^ k)

/-- affine scan と既存 `affineConst` の exact relation。 -/
theorem affineScan_eq
    (v : ParityWord) (k B : ℕ) :
    affineScan v k B =
      3 ^ oddCount v * B + 2 ^ k * affineConst v := by
  induction v generalizing k B with
  | nil =>
      simp [affineScan, oddCount, affineConst]
  | cons b v ih =>
      cases b
      · simp [affineScan, oddCount, bitNat, affineConst, ih, pow_succ]
        ring
      · simp [affineScan, oddCount, bitNat, affineConst, ih, pow_succ]
        ring

/--
current position `(k,m)` から見て、word の各 step 開始点が
critical power boundary の expanding 側または境界上にある。
-/
def PrefixPowerBoundedFrom
    (v : ParityWord) (k m : ℕ) : Prop :=
  ∀ j : ℕ, j < v.length →
    2 ^ (k + j) ≤
      3 ^ (m + prefixOddCount v j)

/-- `PrefixPowerBoundedFrom` は head を一つ読むと tail へ移る。 -/
theorem PrefixPowerBoundedFrom.tail
    {b : Bool} {v : ParityWord} {k m : ℕ}
    (h : PrefixPowerBoundedFrom (b :: v) k m) :
    PrefixPowerBoundedFrom v (k + 1) (m + bitNat b) := by
  unfold PrefixPowerBoundedFrom at h ⊢
  intro j hj
  have hs := h (j + 1) (by simp; omega)
  have hk :
      k + (j + 1) = (k + 1) + j := by
    omega
  have hm :
      m + prefixOddCount (b :: v) (j + 1) =
        (m + bitNat b) + prefixOddCount v j := by
    simp [prefixOddCount_cons_succ]
    omega
  rw [hk, hm] at hs
  exact hs

/--
first-passage path の各 step 開始点は critical power boundary 以下には落ちない。
`j=0` は equality、`0<j<length` は proper expanding から従う。
-/
theorem FirstPassagePath.prefixPowerBoundedFrom_zero
    (P : FirstPassagePath) :
    PrefixPowerBoundedFrom P.word 0 0 := by
  unfold PrefixPowerBoundedFrom
  intro j hj
  simp only [Nat.zero_add]
  by_cases hj0 : j = 0
  · subst j
    simp
  · have hExp :=
      P.proper_expanding j (Nat.pos_of_ne_zero hj0) hj
    unfold CoefficientExpandingAt at hExp
    exact le_of_lt hExp

/--
critical boundary に沿う affine scan の invariant。

current numerator が `B ≤ m*3^m` なら、残りを読んだ後も
同じ形の bound が保存される。
-/
theorem affineScan_le_oddCount_mul_threePow_of_prefixPowerBoundedFrom
    {v : ParityWord} {k m B : ℕ}
    (hPrefix : PrefixPowerBoundedFrom v k m)
    (hB : B ≤ m * 3 ^ m) :
    affineScan v k B ≤
      (m + oddCount v) * 3 ^ (m + oddCount v) := by
  induction v generalizing k m B with
  | nil =>
      simpa [affineScan, oddCount] using hB
  | cons b v ih =>
      cases b
      · have hTail :
            PrefixPowerBoundedFrom v (k + 1) m := by
          simpa [bitNat] using PrefixPowerBoundedFrom.tail hPrefix
        have hRec := ih (k := k + 1) (m := m) (B := B) hTail hB
        simpa [affineScan, oddCount, bitNat] using hRec
      · have hkRaw := hPrefix 0 (by simp)
        have hk : 2 ^ k ≤ 3 ^ m := by
          simpa [prefixOddCount, oddCount] using hkRaw
        have hThreeB :
            3 * B ≤ 3 * (m * 3 ^ m) :=
          Nat.mul_le_mul_left 3 hB
        have hThreeB :
            3 * B ≤ 3 * (m * 3 ^ m) :=
          Nat.mul_le_mul_left 3 hB
        have hNextRaw :
            3 * B + 2 ^ k ≤
              3 * (m * 3 ^ m) + 3 ^ m :=
          Nat.add_le_add hThreeB hk
        have hNext :
            3 * B + 2 ^ k ≤
              (m + 1) * 3 ^ (m + 1) := by
          calc
            3 * B + 2 ^ k
                ≤ 3 * (m * 3 ^ m) + 3 ^ m := hNextRaw
            _ ≤ (m + 1) * 3 ^ (m + 1) := by
              rw [pow_succ]
              nlinarith [Nat.zero_le (3 ^ m)]
        have hTail :
            PrefixPowerBoundedFrom v (k + 1) (m + 1) := by
          simpa [bitNat] using PrefixPowerBoundedFrom.tail hPrefix
        have hRec :=
          ih (k := k + 1) (m := m + 1)
            (B := 3 * B + 2 ^ k) hTail hNext
        simpa [affineScan, oddCount, bitNat, Nat.add_assoc] using hRec

namespace FirstPassagePath

/--
first-passage geometry だけで standard affine numerator を
`m * 3^m` に抑える。
-/
theorem affineConst_le_endpointOddCount_mul_threePow
    (P : FirstPassagePath) :
    affineConst P.word ≤
      P.endpointOddCount * 3 ^ P.endpointOddCount := by
  have hScan :=
    affineScan_le_oddCount_mul_threePow_of_prefixPowerBoundedFrom
      (v := P.word) (k := 0) (m := 0) (B := 0)
      P.prefixPowerBoundedFrom_zero
      (by simp)
  have hScanEq :
      affineScan P.word 0 0 = affineConst P.word := by
    simpa using affineScan_eq P.word 0 0
  rw [hScanEq] at hScan
  simpa [endpointOddCount] using hScan

/-- endpoint odd count は path length 以下。 -/
theorem endpointOddCount_le_length
    (P : FirstPassagePath) :
    P.endpointOddCount ≤ P.length := by
  simpa [endpointOddCount, length] using oddCount_le_length P.word

private theorem natPow_le_natPow_of_le
    {a b : ℕ} (hab : a ≤ b) :
    ∀ n : ℕ, a ^ n ≤ b ^ n
  | 0 => by simp
  | n + 1 => by
      rw [pow_succ, pow_succ]
      exact Nat.mul_le_mul (natPow_le_natPow_of_le hab n) hab

/--
polynomial 2-3 gap の具体 witness `(K,A)` があれば、
capacity は endpoint odd count の explicit polynomial 以下。
-/
theorem capacity_le_endpointPolynomial_of_gap_witness
    (P : FirstPassagePath)
    {K A : ℕ}
    (hGap :
      ∀ p H : ℕ,
        0 < p →
        3 ^ p < 2 ^ H →
        3 ^ p ≤
          K * (p + 1) ^ A * (2 ^ H - 3 ^ p)) :
    P.capacity ≤
      P.endpointOddCount * K *
        (P.endpointOddCount + 1) ^ A := by
  have hB := P.affineConst_le_endpointOddCount_mul_threePow
  by_cases hm0 : P.endpointOddCount = 0
  · have hB0 : affineConst P.word = 0 := by
      apply Nat.eq_zero_of_le_zero
      simpa [hm0] using hB
    simp [capacity, hB0, hm0]
  · have hmPos : 0 < P.endpointOddCount :=
      Nat.pos_of_ne_zero hm0
    have hGapP :
        3 ^ P.endpointOddCount ≤
          K * (P.endpointOddCount + 1) ^ A * P.terminalGap := by
      have h :=
        hGap P.endpointOddCount P.length hmPos P.terminal_contracting
      simpa [terminalGap, length, endpointOddCount] using h
    have hNumerator :
        affineConst P.word ≤
          (P.endpointOddCount * K *
              (P.endpointOddCount + 1) ^ A) * P.terminalGap := by
      calc
        affineConst P.word
            ≤ P.endpointOddCount * 3 ^ P.endpointOddCount := hB
        _ ≤ P.endpointOddCount *
              (K * (P.endpointOddCount + 1) ^ A * P.terminalGap) :=
          Nat.mul_le_mul_left P.endpointOddCount hGapP
        _ =
            (P.endpointOddCount * K *
                (P.endpointOddCount + 1) ^ A) * P.terminalGap := by
          ring
    unfold capacity
    by_contra hnot
    have hlt :
        P.endpointOddCount * K * (P.endpointOddCount + 1) ^ A <
          affineConst P.word / P.terminalGap := by
      omega
    have hmul :
        (P.endpointOddCount * K * (P.endpointOddCount + 1) ^ A) *
            P.terminalGap <
          (affineConst P.word / P.terminalGap) * P.terminalGap :=
      (Nat.mul_lt_mul_right P.terminalGap_pos).2 hlt
    have hdiv :
        (affineConst P.word / P.terminalGap) * P.terminalGap ≤
          affineConst P.word :=
      Nat.div_mul_le_self _ _
    omega

/--
同じ bound を path length だけの polynomial に粗くする。
-/
theorem capacity_le_lengthPolynomial_of_gap_witness
    (P : FirstPassagePath)
    {K A : ℕ}
    (hGap :
      ∀ p H : ℕ,
        0 < p →
        3 ^ p < 2 ^ H →
        3 ^ p ≤
          K * (p + 1) ^ A * (2 ^ H - 3 ^ p)) :
    P.capacity ≤
      P.length * K * (P.length + 1) ^ A := by
  have hEndpoint :=
    P.capacity_le_endpointPolynomial_of_gap_witness hGap
  have hmle : P.endpointOddCount ≤ P.length :=
    P.endpointOddCount_le_length
  have hbase :
      P.endpointOddCount + 1 ≤ P.length + 1 := by
    omega
  have hpow :
      (P.endpointOddCount + 1) ^ A ≤
        (P.length + 1) ^ A :=
    natPow_le_natPow_of_le hbase A
  have hleft :
      P.endpointOddCount * K ≤ P.length * K :=
    Nat.mul_le_mul_right K hmle
  have hpoly :
      P.endpointOddCount * K *
          (P.endpointOddCount + 1) ^ A ≤
        P.length * K * (P.length + 1) ^ A :=
    Nat.mul_le_mul hleft hpow
  exact le_trans hEndpoint hpoly

/--
さらに一項 polynomial

  K * (length+1)^(A+1)

へまとめる。
-/
theorem capacity_le_simpleLengthPolynomial_of_gap_witness
    (P : FirstPassagePath)
    {K A : ℕ}
    (hGap :
      ∀ p H : ℕ,
        0 < p →
        3 ^ p < 2 ^ H →
        3 ^ p ≤
          K * (p + 1) ^ A * (2 ^ H - 3 ^ p)) :
    P.capacity ≤
      K * (P.length + 1) ^ (A + 1) := by
  have hLength :=
    P.capacity_le_lengthPolynomial_of_gap_witness hGap
  have hLen : P.length ≤ P.length + 1 := by
    omega
  have hKL :
      K * P.length ≤ K * (P.length + 1) :=
    Nat.mul_le_mul_left K hLen
  have hMul :
      K * P.length * (P.length + 1) ^ A ≤
        K * (P.length + 1) * (P.length + 1) ^ A :=
    Nat.mul_le_mul_right ((P.length + 1) ^ A) hKL
  calc
    P.capacity
        ≤ P.length * K * (P.length + 1) ^ A := hLength
    _ = K * P.length * (P.length + 1) ^ A := by ring
    _ ≤ K * (P.length + 1) * (P.length + 1) ^ A := hMul
    _ = K * (P.length + 1) ^ (A + 1) := by
      rw [pow_succ]
      ring

end FirstPassagePath

/--
既存 `TwoThreeGapPolynomialBound` から、全 first-passage path に共通する
length-polynomial capacity bound を抽出する。
-/
theorem exists_uniform_polynomial_capacity_bound
    (hGap : External.TwoThreeGapPolynomialBound) :
    ∃ K D : ℕ,
      0 < K ∧ 0 < D ∧
      ∀ P : FirstPassagePath,
        P.capacity ≤ K * (P.length + 1) ^ D := by
  rcases hGap with ⟨K, A, hK, hGapWitness⟩
  refine ⟨K, A + 1, hK, by omega, ?_⟩
  intro P
  exact
    P.capacity_le_simpleLengthPolynomial_of_gap_witness
      hGapWitness

namespace MicroObject

/-- path capacity と `MicroObject.Cap` は同じ量。 -/
theorem Cap_eq_path_capacity (M : MicroObject) :
    M.Cap = M.path.capacity := by
  rfl

/--
polynomial majorant より `R(P)` が大きければ CST は成立する。

これで general CST の残りを 2-adic representative の
polynomial domination problem として切り出せる。
-/
theorem cstHolds_of_simpleLengthPolynomial_lt_R
    (M : MicroObject)
    {K A : ℕ}
    (hGap :
      ∀ p H : ℕ,
        0 < p →
        3 ^ p < 2 ^ H →
        3 ^ p ≤
          K * (p + 1) ^ A * (2 ^ H - 3 ^ p))
    (hR :
      K * (M.path.length + 1) ^ (A + 1) < M.R) :
    M.CSTHolds := by
  apply (M.cstHolds_iff_R_gt_Cap).2
  rw [M.Cap_eq_path_capacity]
  have hCap :=
    M.path.capacity_le_simpleLengthPolynomial_of_gap_witness hGap
  exact lt_of_le_of_lt hCap hR

end MicroObject
end CSTMicro
end Collatz2
