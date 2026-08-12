import CollatzLean.Collatz.AdjacentReturn.PositiveReturn.EndpointFloorZeroE2CenteredSmallBand

set_option linter.style.emptyLine false
/-!
# E2 ZERO centered trajectory の forward residue tree

centered backward recurrence を forward 側へ読み替え、inner word の任意 prefix が
full level

  `L = h_m + n`

の 2-adic residue を一意に深掘りしていく構造を pure arithmetic にする。

`k` 番目の forward exponent を

  `e_k = backwardExponent (m-(k+1))`

とし、prefix boundary を

  `x_k = T + 2*h_(m-k)`

と置くと、

  `2^e_k * x_(k+1) = 3*x_k + 1`

が成立する。

さらに forward affine constant `A_k` を

  `A_0 = 0`
  `A_(k+1) = 3*A_k + 2^(prefixExponent k)`

で再構成すると

  `2^K_k * x_k = 3^k * start + A_k`

となる。

全 boundary は odd なので、`start+5=18*L` を入れることで任意 prefix に対し

  `18*3^k*L + A_k
     = 2^K_k + 2^(K_k+1)*q + 5*3^k`

という exact residue equation を得る。

この一般式の最初の有限特殊化として third / fourth step の全状態と
`L mod 2^K` を列挙する。
-/

namespace Collatz
namespace AdjacentReturn
namespace PositiveReturn
namespace EndpointFloorZero
namespace E2ZeroCenteredTrajectoryData

/-- forward index `k` の一文字 exponent。 -/
def forwardExponent
    (D : E2ZeroCenteredTrajectoryData)
    (k : ℕ) : ℕ :=
  D.backwardExponent (D.length - (k + 1))

/-- forward prefix `k` 段後の actual boundary。 -/
def forwardBoundary
    (D : E2ZeroCenteredTrajectoryData)
    (k : ℕ) : ℕ :=
  D.centeredValue (D.length - k)

/-- forward prefix affine constant の pure recurrence。 -/
def forwardAffine
    (D : E2ZeroCenteredTrajectoryData) : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
      3 * forwardAffine D k +
        2 ^ D.prefixExponent k

@[simp] theorem forwardAffine_zero
    (D : E2ZeroCenteredTrajectoryData) :
    D.forwardAffine 0 = 0 := rfl

@[simp] theorem forwardAffine_succ
    (D : E2ZeroCenteredTrajectoryData)
    (k : ℕ) :
    D.forwardAffine (k + 1) =
      3 * D.forwardAffine k +
        2 ^ D.prefixExponent k := rfl

/-- empty prefix exponent は0。 -/
theorem prefixExponent_zero
    (D : E2ZeroCenteredTrajectoryData) :
    D.prefixExponent 0 = 0 := by
  have h := D.exponent_split 0 (by omega)
  simpa using h

/-- 最初の forward exponent は1。 -/
theorem forwardExponent_zero_eq_one
    (D : E2ZeroCenteredTrajectoryData) :
    D.forwardExponent 0 = 1 := by
  simpa [forwardExponent] using
    D.first_backward_exponent_eq_one

/-- 範囲内 forward exponent は正。 -/
theorem forwardExponent_pos
    (D : E2ZeroCenteredTrajectoryData)
    {k : ℕ}
    (hk : k < D.length) :
    0 < D.forwardExponent k := by
  have hr :
      D.length - (k + 1) < D.length := by
    omega
  exact D.backwardExponent_pos _ hr

/--
prefix cumulative exponent の forward recurrence。

  `K_(k+1) = K_k + e_k`。
-/
theorem prefixExponent_succ
    (D : E2ZeroCenteredTrajectoryData)
    {k : ℕ}
    (hk : k < D.length) :
    D.prefixExponent (k + 1) =
      D.prefixExponent k + D.forwardExponent k := by
  let r := D.length - (k + 1)
  have hrLt : r < D.length := by
    dsimp [r]
    omega
  have hrSucc :
      r + 1 = D.length - k := by
    dsimp [r]
    omega
  have hsuffix := D.suffixExponent_succ r hrLt
  rw [hrSucc] at hsuffix
  have hsplit0 := D.exponent_split k (by omega)
  have hsplit1 := D.exponent_split (k + 1) (by omega)
  dsimp [forwardExponent, r] at hsuffix ⊢
  omega

/-- forward boundary `0` は inner start。 -/
theorem forwardBoundary_zero
    (D : E2ZeroCenteredTrajectoryData) :
    D.forwardBoundary 0 = D.startValue := by
  simp [forwardBoundary, startValue]

/-- forward boundary `m` は endpoint。 -/
theorem forwardBoundary_full
    (D : E2ZeroCenteredTrajectoryData) :
    D.forwardBoundary D.length = D.endpoint := by
  simp [forwardBoundary, centeredValue, D.halfGap_zero]

/--
centered recurrence の forward one-step 形。

  `2^e_k * x_(k+1) = 3*x_k + 1`。
-/
theorem forwardStepEquation
    (D : E2ZeroCenteredTrajectoryData)
    {k : ℕ}
    (hk : k < D.length) :
    2 ^ D.forwardExponent k *
        D.forwardBoundary (k + 1) =
      3 * D.forwardBoundary k + 1 := by
  let r := D.length - (k + 1)
  have hrLt : r < D.length := by
    dsimp [r]
    omega
  have hrSucc :
      r + 1 = D.length - k := by
    dsimp [r]
    omega
  have hrec := D.step_recurrence r hrLt
  rw [pow_succ] at hrec
  rw [hrSucc] at hrec
  dsimp [forwardExponent, forwardBoundary, centeredValue, r]
  nlinarith

/-- endpoint は odd。 -/
theorem endpoint_odd_rep
    (D : E2ZeroCenteredTrajectoryData) :
    ∃ q : ℕ, D.endpoint = q + q + 1 := by
  obtain ⟨q, hEven | hOdd⟩ := D.endpoint.even_or_odd'
  · have hbal := D.endpoint_balance
    rw [hEven] at hbal
    omega
  · exact ⟨q, by simpa [two_mul] using hOdd⟩

/-- 全 forward boundary は endpoint と同じ parity なので odd。 -/
theorem forwardBoundary_odd_rep
    (D : E2ZeroCenteredTrajectoryData)
    {k : ℕ} :
    ∃ q : ℕ, D.forwardBoundary k = q + q + 1 := by
  obtain ⟨a, ha⟩ := D.endpoint_odd_rep
  refine
    ⟨a + D.halfGap (D.length - k), ?_⟩
  dsimp [forwardBoundary, centeredValue]
  rw [ha]
  omega

/--
forward recurrence を `k` 段畳んだ exact affine realization。

  `2^K_k * x_k = 3^k * start + A_k`。
-/
theorem forwardAffine_realization
    (D : E2ZeroCenteredTrajectoryData)
    {k : ℕ}
    (hk : k ≤ D.length) :
    2 ^ D.prefixExponent k * D.forwardBoundary k =
      3 ^ k * D.startValue + D.forwardAffine k := by
  induction k with
  | zero =>
      have hK0 := D.prefixExponent_zero
      rw [hK0]
      simp [forwardBoundary, startValue]
  | succ k ih =>
      have hkLt : k < D.length := by
        omega
      have hkLe : k ≤ D.length := by
        omega
      have hi := ih hkLe
      have hstep := D.forwardStepEquation hkLt
      have hK := D.prefixExponent_succ hkLt
      rw [hK]
      calc
        2 ^ (D.prefixExponent k + D.forwardExponent k) *
            D.forwardBoundary (k + 1)
            =
          2 ^ D.prefixExponent k *
            (2 ^ D.forwardExponent k *
              D.forwardBoundary (k + 1)) := by
                rw [pow_add]
                ring
        _ =
          2 ^ D.prefixExponent k *
            (3 * D.forwardBoundary k + 1) := by
              rw [hstep]
        _ =
          3 *
              (2 ^ D.prefixExponent k *
                D.forwardBoundary k) +
            2 ^ D.prefixExponent k := by
              ring
        _ =
          3 *
              (3 ^ k * D.startValue +
                D.forwardAffine k) +
            2 ^ D.prefixExponent k := by
              rw [hi]
        _ =
          3 ^ (k + 1) * D.startValue +
            (3 * D.forwardAffine k +
              2 ^ D.prefixExponent k) := by
                rw [pow_succ]
                ring
        _ =
          3 ^ (k + 1) * D.startValue +
            D.forwardAffine (k + 1) := by
              rw [D.forwardAffine_succ]

/--
任意 prefix が full level `L` の exact 2-adic residue equation を与える。

  `18*3^k*L + A_k
     = 2^K_k + 2^(K_k+1)*q + 5*3^k`。
-/
theorem exists_fullLevel_prefixResidueEquation
    (D : E2ZeroCenteredTrajectoryData)
    {k : ℕ}
    (hk : k ≤ D.length) :
    ∃ q : ℕ,
      18 * 3 ^ k * D.fullLevel +
          D.forwardAffine k =
        2 ^ D.prefixExponent k +
          2 ^ (D.prefixExponent k + 1) * q +
          5 * 3 ^ k := by
  have hrun := D.forwardAffine_realization hk
  obtain ⟨q, hq⟩ := D.forwardBoundary_odd_rep
  rw [hq] at hrun
  have hS :=
    D.startValue_add_five_eq_eighteen_mul_fullLevel
  have hSscaled :=
    congrArg
      (fun z : ℕ => 3 ^ k * z)
      hS
  refine ⟨q, ?_⟩
  rw [pow_succ]
  ring_nf at hrun hSscaled ⊢
  nlinarith

/-- first prefix cumulative exponent は1。 -/
theorem prefixExponent_one
    (D : E2ZeroCenteredTrajectoryData) :
    D.prefixExponent 1 = 1 := by
  have h := D.prefixExponent_succ (k := 0) (by
    have h7 := D.seven_le_length
    omega)
  rw [D.prefixExponent_zero, D.forwardExponent_zero_eq_one] at h
  omega

/--
最初の3 exponent は

`111`, `112`, `121`

の三つだけ。
-/
theorem thirdForwardPattern
    (D : E2ZeroCenteredTrajectoryData) :
    (D.forwardExponent 1 = 1 ∧
      D.forwardExponent 2 = 1) ∨
    (D.forwardExponent 1 = 1 ∧
      D.forwardExponent 2 = 2) ∨
    (D.forwardExponent 1 = 2 ∧
      D.forwardExponent 2 = 1) := by
  have h7 := D.seven_le_length
  have h1cases :
      D.forwardExponent 1 = 1 ∨
        D.forwardExponent 1 = 2 := by
    simpa [forwardExponent] using
      D.secondBackwardExponent_one_or_two
  have he2Pos :
      0 < D.forwardExponent 2 :=
    D.forwardExponent_pos (by omega)
  have hK1 :
      D.prefixExponent 1 = 1 :=
    D.prefixExponent_one
  have hK2 :
      D.prefixExponent 2 =
        D.prefixExponent 1 +
          D.forwardExponent 1 := by
    simpa using
      D.prefixExponent_succ (k := 1) (by omega)
  have hK3 :
      D.prefixExponent 3 =
        D.prefixExponent 2 +
          D.forwardExponent 2 := by
    simpa using
      D.prefixExponent_succ (k := 2) (by omega)
  have hExp0 :=
    D.prefix_expanding 3 (by omega)
  have hExp :
      2 ^ (3 + D.prefixExponent 3) < 243 := by
    norm_num at hExp0
    exact hExp0
  have hK3le :
      D.prefixExponent 3 ≤ 4 := by
    by_contra hnot
    have hge :
        5 ≤ D.prefixExponent 3 := by
      omega
    have hpow :
        256 ≤
          2 ^ (3 + D.prefixExponent 3) := by
      have h :
          2 ^ 8 ≤
            2 ^ (3 + D.prefixExponent 3) :=
        Nat.pow_le_pow_right
          (by omega : 0 < (2 : ℕ))
          (by omega)
      norm_num at h ⊢
      exact h
    omega
  rcases h1cases with h11 | h12
  · have hK2eq :
        D.prefixExponent 2 = 2 := by
      rw [hK1, h11] at hK2
      norm_num at hK2
      exact hK2
    have he2le :
        D.forwardExponent 2 ≤ 2 := by
      rw [hK2eq] at hK3
      omega
    by_cases he2 :
        D.forwardExponent 2 = 1
    · exact Or.inl ⟨h11, he2⟩
    · have he22 :
          D.forwardExponent 2 = 2 := by
        omega
      exact Or.inr (Or.inl ⟨h11, he22⟩)
  · have hK2eq :
        D.prefixExponent 2 = 3 := by
      rw [hK1, h12] at hK2
      norm_num at hK2
      exact hK2
    have he21 :
        D.forwardExponent 2 = 1 := by
      rw [hK2eq] at hK3
      omega
    exact Or.inr (Or.inr ⟨h12, he21⟩)

/-- `x % m = r` から標準的な residue 表現を得る。 -/
private theorem exists_eq_mul_add_of_mod_eq
    {x m r : ℕ}
    (hmod : x % m = r) :
    ∃ q : ℕ, x = m * q + r := by
  refine ⟨x / m, ?_⟩
  have h := Nat.mod_add_div x m
  rw [hmod] at h
  omega

/-- `111` の exact equation から `L ≡ 2 (mod 8)`。 -/
private theorem fullLevel_mod_eight_eq_two_of_111
    {L q : ℕ}
    (h :
      486 * L + 19 =
        143 + 16 * q) :
    L % 8 = 2 := by
  have hhalf :
      243 * L =
        62 + 8 * q := by
    omega
  have hmod :
      243 * L ≡ 243 * 2 [MOD 8] := by
    rw [hhalf]
    norm_num [Nat.ModEq, Nat.add_mod, Nat.mul_mod]
  have hcancel :
      L ≡ 2 [MOD 8] :=
    Nat.ModEq.cancel_left_of_coprime
      (by decide)
      hmod
  simpa [Nat.ModEq] using hcancel


/-- `112` の exact equation から `L ≡ 6 (mod 16)`。 -/
private theorem fullLevel_mod_sixteen_eq_six_of_112
    {L q : ℕ}
    (h :
      486 * L + 19 =
        151 + 32 * q) :
    L % 16 = 6 := by
  have hhalf :
      243 * L =
        66 + 16 * q := by
    omega
  have hmod :
      243 * L ≡ 243 * 6 [MOD 16] := by
    rw [hhalf]
    norm_num [Nat.ModEq, Nat.add_mod, Nat.mul_mod]
  have hcancel :
      L ≡ 6 [MOD 16] :=
    Nat.ModEq.cancel_left_of_coprime
      (by decide)
      hmod
  simpa [Nat.ModEq] using hcancel


/-- `121` の exact equation から `L ≡ 0 (mod 16)`。 -/
private theorem fullLevel_mod_sixteen_eq_zero_of_121
    {L q : ℕ}
    (h :
      486 * L + 23 =
        151 + 32 * q) :
    L % 16 = 0 := by
  have hhalf :
      243 * L =
        64 + 16 * q := by
    omega
  have hmod :
      243 * L ≡ 243 * 0 [MOD 16] := by
    rw [hhalf]
    norm_num [Nat.ModEq, Nat.add_mod, Nat.mul_mod]
  have hcancel :
      L ≡ 0 [MOD 16] :=
    Nat.ModEq.cancel_left_of_coprime
      (by decide)
      hmod
  simpa [Nat.ModEq] using hcancel

/--
third step までで full level residue は三状態へ縮む。

- `111` -> `L = 8*q+2`
- `112` -> `L = 16*q+6`
- `121` -> `L = 16*q`
-/
theorem fullLevel_residue_of_thirdStep
    (D : E2ZeroCenteredTrajectoryData) :
    (∃ q : ℕ, D.fullLevel = 8 * q + 2) ∨
    (∃ q : ℕ, D.fullLevel = 16 * q + 6) ∨
    (∃ q : ℕ, D.fullLevel = 16 * q) := by
  have h7 := D.seven_le_length
  obtain ⟨q, hres⟩ :=
    D.exists_fullLevel_prefixResidueEquation
      (k := 3) (by omega)
  have hK0 :
      D.prefixExponent 0 = 0 :=
    D.prefixExponent_zero
  have hK1 :
      D.prefixExponent 1 = 1 :=
    D.prefixExponent_one
  have hK2 :
      D.prefixExponent 2 =
        D.prefixExponent 1 +
          D.forwardExponent 1 := by
    simpa using
      D.prefixExponent_succ
        (k := 1) (by omega)
  have hK3 :
      D.prefixExponent 3 =
        D.prefixExponent 2 +
          D.forwardExponent 2 := by
    simpa using
      D.prefixExponent_succ
        (k := 2) (by omega)
  rcases D.thirdForwardPattern with h111 | hrest
  · have hP2 :
        D.prefixExponent 2 = 2 := by
      calc
        D.prefixExponent 2
            =
          D.prefixExponent 1 +
            D.forwardExponent 1 := hK2
        _ = 1 + 1 := by
          rw [hK1, h111.1]
        _ = 2 := by
          norm_num
    have hP3 :
        D.prefixExponent 3 = 3 := by
      calc
        D.prefixExponent 3
            =
          D.prefixExponent 2 +
            D.forwardExponent 2 := hK3
        _ = 2 + 1 := by
          rw [hP2, h111.2]
        _ = 3 := by
          norm_num
    have hEq :
        486 * D.fullLevel + 19 =
          143 + 16 * q := by
      have h := hres
      simp [
        forwardAffine,
        hK0,
        hK1,
        hP2,
        hP3
      ] at h
      omega
    have hmod :
        D.fullLevel % 8 = 2 :=
      fullLevel_mod_eight_eq_two_of_111 hEq
    left
    exact exists_eq_mul_add_of_mod_eq hmod
  · rcases hrest with h112 | h121
    · have hP2 :
          D.prefixExponent 2 = 2 := by
        calc
          D.prefixExponent 2
              =
            D.prefixExponent 1 +
              D.forwardExponent 1 := hK2
          _ = 1 + 1 := by
            rw [hK1, h112.1]
          _ = 2 := by
            norm_num
      have hP3 :
          D.prefixExponent 3 = 4 := by
        calc
          D.prefixExponent 3
              =
            D.prefixExponent 2 +
              D.forwardExponent 2 := hK3
          _ = 2 + 2 := by
            rw [hP2, h112.2]
          _ = 4 := by
            norm_num
      have hEq :
          486 * D.fullLevel + 19 =
            151 + 32 * q := by
        have h := hres
        simp [
          forwardAffine,
          hK0,
          hK1,
          hP2,
          hP3
        ] at h
        omega
      have hmod :
          D.fullLevel % 16 = 6 :=
        fullLevel_mod_sixteen_eq_six_of_112 hEq
      right
      left
      exact exists_eq_mul_add_of_mod_eq hmod
    · have hP2 :
          D.prefixExponent 2 = 3 := by
        calc
          D.prefixExponent 2
              =
            D.prefixExponent 1 +
              D.forwardExponent 1 := hK2
          _ = 1 + 2 := by
            rw [hK1, h121.1]
          _ = 3 := by
            norm_num
      have hP3 :
          D.prefixExponent 3 = 4 := by
        calc
          D.prefixExponent 3
              =
            D.prefixExponent 2 +
              D.forwardExponent 2 := hK3
          _ = 3 + 1 := by
            rw [hP2, h121.2]
          _ = 4 := by
            norm_num
      have hEq :
          486 * D.fullLevel + 23 =
            151 + 32 * q := by
        have h := hres
        simp [
          forwardAffine,
          hK0,
          hK1,
          hP2,
          hP3
        ] at h
        omega
      have hmod :
          D.fullLevel % 16 = 0 :=
        fullLevel_mod_sixteen_eq_zero_of_121 hEq
      right
      right
      exact exists_eq_mul_add_of_mod_eq hmod


/-- `1111` から `L ≡ 2 (mod 16)`。 -/
private theorem fullLevel_mod_sixteen_eq_two_of_1111
    {L q : ℕ}
    (h :
      729 * L = 178 + 16 * q) :
    L % 16 = 2 := by
  have hmod :
      729 * L ≡ 729 * 2 [MOD 16] := by
    rw [h]
    norm_num [Nat.ModEq, Nat.add_mod, Nat.mul_mod]

  have hcancel :
      L ≡ 2 [MOD 16] :=
    Nat.ModEq.cancel_left_of_coprime
      (by decide)
      hmod

  simpa [Nat.ModEq] using hcancel


/-- `1112` から `L ≡ 10 (mod 32)`。 -/
private theorem fullLevel_mod_thirtyTwo_eq_ten_of_1112
    {L q : ℕ}
    (h :
      729 * L = 186 + 32 * q) :
    L % 32 = 10 := by
  have hmod :
      729 * L ≡ 729 * 10 [MOD 32] := by
    rw [h]
    norm_num [Nat.ModEq, Nat.add_mod, Nat.mul_mod]

  have hcancel :
      L ≡ 10 [MOD 32] :=
    Nat.ModEq.cancel_left_of_coprime
      (by decide)
      hmod

  simpa [Nat.ModEq] using hcancel


/-- `1113` から `L ≡ 26 (mod 64)`。 -/
private theorem fullLevel_mod_sixtyFour_eq_twentySix_of_1113
    {L q : ℕ}
    (h :
      729 * L = 202 + 64 * q) :
    L % 64 = 26 := by
  have hmod :
      729 * L ≡ 729 * 26 [MOD 64] := by
    rw [h]
    norm_num [Nat.ModEq, Nat.add_mod, Nat.mul_mod]

  have hcancel :
      L ≡ 26 [MOD 64] :=
    Nat.ModEq.cancel_left_of_coprime
      (by decide)
      hmod

  simpa [Nat.ModEq] using hcancel


/-- `1121` から `L ≡ 6 (mod 32)`。 -/
private theorem fullLevel_mod_thirtyTwo_eq_six_of_1121
    {L q : ℕ}
    (h :
      729 * L = 182 + 32 * q) :
    L % 32 = 6 := by
  have hmod :
      729 * L ≡ 729 * 6 [MOD 32] := by
    rw [h]
    norm_num [Nat.ModEq, Nat.add_mod, Nat.mul_mod]

  have hcancel :
      L ≡ 6 [MOD 32] :=
    Nat.ModEq.cancel_left_of_coprime
      (by decide)
      hmod

  simpa [Nat.ModEq] using hcancel


/-- `1122` から `L ≡ 54 (mod 64)`。 -/
private theorem fullLevel_mod_sixtyFour_eq_fiftyFour_of_1122
    {L q : ℕ}
    (h :
      729 * L = 198 + 64 * q) :
    L % 64 = 54 := by
  have hmod :
      729 * L ≡ 729 * 54 [MOD 64] := by
    rw [h]
    norm_num [Nat.ModEq, Nat.add_mod, Nat.mul_mod]

  have hcancel :
      L ≡ 54 [MOD 64] :=
    Nat.ModEq.cancel_left_of_coprime
      (by decide)
      hmod

  simpa [Nat.ModEq] using hcancel


/-- `1211` から `L ≡ 16 (mod 32)`。 -/
private theorem fullLevel_mod_thirtyTwo_eq_sixteen_of_1211
    {L q : ℕ}
    (h :
      729 * L = 176 + 32 * q) :
    L % 32 = 16 := by
  have hmod :
      729 * L ≡ 729 * 16 [MOD 32] := by
    rw [h]
    norm_num [Nat.ModEq, Nat.add_mod, Nat.mul_mod]

  have hcancel :
      L ≡ 16 [MOD 32] :=
    Nat.ModEq.cancel_left_of_coprime
      (by decide)
      hmod

  simpa [Nat.ModEq] using hcancel


/-- `1212` から `L ≡ 0 (mod 64)`。 -/
private theorem fullLevel_mod_sixtyFour_eq_zero_of_1212
    {L q : ℕ}
    (h :
      729 * L = 192 + 64 * q) :
    L % 64 = 0 := by
  have hmod :
      729 * L ≡ 729 * 0 [MOD 64] := by
    rw [h]
    norm_num [Nat.ModEq, Nat.add_mod, Nat.mul_mod]

  have hcancel :
      L ≡ 0 [MOD 64] :=
    Nat.ModEq.cancel_left_of_coprime
      (by decide)
      hmod

  simpa [Nat.ModEq] using hcancel

/--
fourth exponent までの許容状態。

first exponent `1` は固定なので、ここでは
`(e₂,e₃,e₄)` だけを書く。

- `(1,1,1/2/3)`
- `(1,2,1/2)`
- `(2,1,1/2)`
-/
theorem fourthForwardPattern
    (D : E2ZeroCenteredTrajectoryData) :
    (D.forwardExponent 1 = 1 ∧
      D.forwardExponent 2 = 1 ∧
      (D.forwardExponent 3 = 1 ∨
        D.forwardExponent 3 = 2 ∨
        D.forwardExponent 3 = 3)) ∨
    (D.forwardExponent 1 = 1 ∧
      D.forwardExponent 2 = 2 ∧
      (D.forwardExponent 3 = 1 ∨
        D.forwardExponent 3 = 2)) ∨
    (D.forwardExponent 1 = 2 ∧
      D.forwardExponent 2 = 1 ∧
      (D.forwardExponent 3 = 1 ∨
        D.forwardExponent 3 = 2)) := by
  have h7 := D.seven_le_length

  have he3Pos :
      0 < D.forwardExponent 3 :=
    D.forwardExponent_pos (by omega)

  have hK1 :
      D.prefixExponent 1 = 1 :=
    D.prefixExponent_one

  have hK2 :
      D.prefixExponent 2 =
        D.prefixExponent 1 +
          D.forwardExponent 1 := by
    simpa using
      D.prefixExponent_succ
        (k := 1) (by omega)

  have hK3 :
      D.prefixExponent 3 =
        D.prefixExponent 2 +
          D.forwardExponent 2 := by
    simpa using
      D.prefixExponent_succ
        (k := 2) (by omega)

  have hK4 :
      D.prefixExponent 4 =
        D.prefixExponent 3 +
          D.forwardExponent 3 := by
    simpa using
      D.prefixExponent_succ
        (k := 3) (by omega)

  have hExp0 :=
    D.prefix_expanding 4 (by omega)

  have hExp :
      2 ^ (3 + D.prefixExponent 4) < 729 := by
    norm_num at hExp0
    exact hExp0

  have hK4le :
      D.prefixExponent 4 ≤ 6 := by
    by_contra hnot

    have hge :
        7 ≤ D.prefixExponent 4 := by
      omega

    have hpow :
        1024 ≤
          2 ^ (3 + D.prefixExponent 4) := by
      have h :
          2 ^ 10 ≤
            2 ^ (3 + D.prefixExponent 4) :=
        Nat.pow_le_pow_right
          (by omega : 0 < (2 : ℕ))
          (by omega)
      norm_num at h ⊢
      exact h

    omega

  rcases D.thirdForwardPattern with h111 | hrest

  · have hP2 :
        D.prefixExponent 2 = 2 := by
      calc
        D.prefixExponent 2
            =
          D.prefixExponent 1 +
            D.forwardExponent 1 := hK2
        _ = 1 + 1 := by
          rw [hK1, h111.1]
        _ = 2 := by
          norm_num

    have hP3 :
        D.prefixExponent 3 = 3 := by
      calc
        D.prefixExponent 3
            =
          D.prefixExponent 2 +
            D.forwardExponent 2 := hK3
        _ = 2 + 1 := by
          rw [hP2, h111.2]
        _ = 3 := by
          norm_num

    have he3le :
        D.forwardExponent 3 ≤ 3 := by
      have h := hK4
      rw [hP3] at h
      omega

    have he3 :
        D.forwardExponent 3 = 1 ∨
        D.forwardExponent 3 = 2 ∨
        D.forwardExponent 3 = 3 := by
      by_cases h1 : D.forwardExponent 3 = 1
      · exact Or.inl h1
      · by_cases h2 : D.forwardExponent 3 = 2
        · exact Or.inr (Or.inl h2)
        · have h3 :
              D.forwardExponent 3 = 3 := by
            omega
          exact Or.inr (Or.inr h3)

    exact
      Or.inl
        ⟨h111.1, h111.2, he3⟩

  · rcases hrest with h112 | h121

    · have hP2 :
          D.prefixExponent 2 = 2 := by
        calc
          D.prefixExponent 2
              =
            D.prefixExponent 1 +
              D.forwardExponent 1 := hK2
          _ = 1 + 1 := by
            rw [hK1, h112.1]
          _ = 2 := by
            norm_num

      have hP3 :
          D.prefixExponent 3 = 4 := by
        calc
          D.prefixExponent 3
              =
            D.prefixExponent 2 +
              D.forwardExponent 2 := hK3
          _ = 2 + 2 := by
            rw [hP2, h112.2]
          _ = 4 := by
            norm_num

      have he3le :
          D.forwardExponent 3 ≤ 2 := by
        have h := hK4
        rw [hP3] at h
        omega

      have he3 :
          D.forwardExponent 3 = 1 ∨
          D.forwardExponent 3 = 2 := by
        by_cases h1 : D.forwardExponent 3 = 1
        · exact Or.inl h1
        · have h2 :
              D.forwardExponent 3 = 2 := by
            omega
          exact Or.inr h2

      exact
        Or.inr
          (Or.inl
            ⟨h112.1, h112.2, he3⟩)

    · have hP2 :
          D.prefixExponent 2 = 3 := by
        calc
          D.prefixExponent 2
              =
            D.prefixExponent 1 +
              D.forwardExponent 1 := hK2
          _ = 1 + 2 := by
            rw [hK1, h121.1]
          _ = 3 := by
            norm_num

      have hP3 :
          D.prefixExponent 3 = 4 := by
        calc
          D.prefixExponent 3
              =
            D.prefixExponent 2 +
              D.forwardExponent 2 := hK3
          _ = 3 + 1 := by
            rw [hP2, h121.2]
          _ = 4 := by
            norm_num

      have he3le :
          D.forwardExponent 3 ≤ 2 := by
        have h := hK4
        rw [hP3] at h
        omega

      have he3 :
          D.forwardExponent 3 = 1 ∨
          D.forwardExponent 3 = 2 := by
        by_cases h1 : D.forwardExponent 3 = 1
        · exact Or.inl h1
        · have h2 :
              D.forwardExponent 3 = 2 := by
            omega
          exact Or.inr h2

      exact
        Or.inr
          (Or.inr
            ⟨h121.1, h121.2, he3⟩)

/--
fourth step までの7 residue。

- `1111` -> `L = 16*q+2`
- `1112` -> `L = 32*q+10`
- `1113` -> `L = 64*q+26`
- `1121` -> `L = 32*q+6`
- `1122` -> `L = 64*q+54`
- `1211` -> `L = 32*q+16`
- `1212` -> `L = 64*q`
-/
theorem fullLevel_residue_of_fourthStep
    (D : E2ZeroCenteredTrajectoryData) :
    (∃ q : ℕ, D.fullLevel = 16 * q + 2) ∨
    (∃ q : ℕ, D.fullLevel = 32 * q + 10) ∨
    (∃ q : ℕ, D.fullLevel = 64 * q + 26) ∨
    (∃ q : ℕ, D.fullLevel = 32 * q + 6) ∨
    (∃ q : ℕ, D.fullLevel = 64 * q + 54) ∨
    (∃ q : ℕ, D.fullLevel = 32 * q + 16) ∨
    (∃ q : ℕ, D.fullLevel = 64 * q) := by
  have h7 := D.seven_le_length

  obtain ⟨q, hres⟩ :=
    D.exists_fullLevel_prefixResidueEquation
      (k := 4) (by omega)

  have hK0 :
      D.prefixExponent 0 = 0 :=
    D.prefixExponent_zero

  have hK1 :
      D.prefixExponent 1 = 1 :=
    D.prefixExponent_one

  have hK2 :
      D.prefixExponent 2 =
        D.prefixExponent 1 +
          D.forwardExponent 1 := by
    simpa using
      D.prefixExponent_succ
        (k := 1) (by omega)

  have hK3 :
      D.prefixExponent 3 =
        D.prefixExponent 2 +
          D.forwardExponent 2 := by
    simpa using
      D.prefixExponent_succ
        (k := 2) (by omega)

  have hK4 :
      D.prefixExponent 4 =
        D.prefixExponent 3 +
          D.forwardExponent 3 := by
    simpa using
      D.prefixExponent_succ
        (k := 3) (by omega)

  rcases D.fourthForwardPattern with h111 | hrest

  · rcases h111.2.2 with h1 | h23

    · have hP2 :
          D.prefixExponent 2 = 2 := by
        calc
          D.prefixExponent 2
              =
            D.prefixExponent 1 +
              D.forwardExponent 1 := hK2
          _ = 1 + 1 := by
            rw [hK1, h111.1]
          _ = 2 := by
            norm_num

      have hP3 :
          D.prefixExponent 3 = 3 := by
        calc
          D.prefixExponent 3
              =
            D.prefixExponent 2 +
              D.forwardExponent 2 := hK3
          _ = 2 + 1 := by
            rw [hP2, h111.2.1]
          _ = 3 := by
            norm_num

      have hP4 :
          D.prefixExponent 4 = 4 := by
        calc
          D.prefixExponent 4
              =
            D.prefixExponent 3 +
              D.forwardExponent 3 := hK4
          _ = 3 + 1 := by
            rw [hP3, h1]
          _ = 4 := by
            norm_num

      have hEq := hres
      rw [hP4] at hEq
      norm_num [
        forwardAffine,
        hK0,
        hK1,
        hP2,
        hP3
      ] at hEq
      have hhalf :
          729 * D.fullLevel =
            178 + 16 * q := by
        omega
      have hmod :
          D.fullLevel % 16 = 2 :=
        fullLevel_mod_sixteen_eq_two_of_1111 hhalf
      exact
        Or.inl
          (exists_eq_mul_add_of_mod_eq hmod)
    · rcases h23 with h2 | h3
      · have hP2 :
            D.prefixExponent 2 = 2 := by
          calc
            D.prefixExponent 2
                =
              D.prefixExponent 1 +
                D.forwardExponent 1 := hK2
            _ = 1 + 1 := by
              rw [hK1, h111.1]
            _ = 2 := by
              norm_num
        have hP3 :
            D.prefixExponent 3 = 3 := by
          calc
            D.prefixExponent 3
                =
              D.prefixExponent 2 +
                D.forwardExponent 2 := hK3
            _ = 2 + 1 := by
              rw [hP2, h111.2.1]
            _ = 3 := by
              norm_num
        have hP4 :
            D.prefixExponent 4 = 5 := by
          calc
            D.prefixExponent 4
                =
              D.prefixExponent 3 +
                D.forwardExponent 3 := hK4
            _ = 3 + 2 := by
              rw [hP3, h2]
            _ = 5 := by
              norm_num
        have hEq := hres
        rw [hP4] at hEq
        norm_num [
          forwardAffine,
          hK0,
          hK1,
          hP2,
          hP3
        ] at hEq
        have hhalf :
            729 * D.fullLevel =
              186 + 32 * q := by
          omega
        have hmod :
            D.fullLevel % 32 = 10 :=
          fullLevel_mod_thirtyTwo_eq_ten_of_1112 hhalf
        exact
          Or.inr
            (Or.inl
              (exists_eq_mul_add_of_mod_eq hmod))
      · have hP2 :
            D.prefixExponent 2 = 2 := by
          calc
            D.prefixExponent 2
                =
              D.prefixExponent 1 +
                D.forwardExponent 1 := hK2
            _ = 1 + 1 := by
              rw [hK1, h111.1]
            _ = 2 := by
              norm_num
        have hP3 :
            D.prefixExponent 3 = 3 := by
          calc
            D.prefixExponent 3
                =
              D.prefixExponent 2 +
                D.forwardExponent 2 := hK3
            _ = 2 + 1 := by
              rw [hP2, h111.2.1]
            _ = 3 := by
              norm_num
        have hP4 :
            D.prefixExponent 4 = 6 := by
          calc
            D.prefixExponent 4
                =
              D.prefixExponent 3 +
                D.forwardExponent 3 := hK4
            _ = 3 + 3 := by
              rw [hP3, h3]
            _ = 6 := by
              norm_num
        have hEq := hres
        rw [hP4] at hEq
        norm_num [
          forwardAffine,
          hK0,
          hK1,
          hP2,
          hP3
        ] at hEq
        have hhalf :
            729 * D.fullLevel =
              202 + 64 * q := by
          omega
        have hmod :
            D.fullLevel % 64 = 26 :=
          fullLevel_mod_sixtyFour_eq_twentySix_of_1113 hhalf
        exact
          Or.inr
            (Or.inr
              (Or.inl
                (exists_eq_mul_add_of_mod_eq hmod)))
  · rcases hrest with h112 | h121
    · rcases h112.2.2 with h1 | h2
      · have hP2 :
            D.prefixExponent 2 = 2 := by
          calc
            D.prefixExponent 2
                =
              D.prefixExponent 1 +
                D.forwardExponent 1 := hK2
            _ = 1 + 1 := by
              rw [hK1, h112.1]
            _ = 2 := by
              norm_num
        have hP3 :
            D.prefixExponent 3 = 4 := by
          calc
            D.prefixExponent 3
                =
              D.prefixExponent 2 +
                D.forwardExponent 2 := hK3
            _ = 2 + 2 := by
              rw [hP2, h112.2.1]
            _ = 4 := by
              norm_num
        have hP4 :
            D.prefixExponent 4 = 5 := by
          calc
            D.prefixExponent 4
                =
              D.prefixExponent 3 +
                D.forwardExponent 3 := hK4
            _ = 4 + 1 := by
              rw [hP3, h1]
            _ = 5 := by
              norm_num
        have hEq := hres
        rw [hP4] at hEq
        norm_num [
          forwardAffine,
          hK0,
          hK1,
          hP2,
          hP3
        ] at hEq
        have hhalf :
            729 * D.fullLevel =
              182 + 32 * q := by
          omega
        have hmod :
            D.fullLevel % 32 = 6 :=
          fullLevel_mod_thirtyTwo_eq_six_of_1121 hhalf
        exact
          Or.inr
            (Or.inr
              (Or.inr
                (Or.inl
                  (exists_eq_mul_add_of_mod_eq hmod))))
      · have hP2 :
            D.prefixExponent 2 = 2 := by
          calc
            D.prefixExponent 2
                =
              D.prefixExponent 1 +
                D.forwardExponent 1 := hK2
            _ = 1 + 1 := by
              rw [hK1, h112.1]
            _ = 2 := by
              norm_num
        have hP3 :
            D.prefixExponent 3 = 4 := by
          calc
            D.prefixExponent 3
                =
              D.prefixExponent 2 +
                D.forwardExponent 2 := hK3
            _ = 2 + 2 := by
              rw [hP2, h112.2.1]
            _ = 4 := by
              norm_num
        have hP4 :
            D.prefixExponent 4 = 6 := by
          calc
            D.prefixExponent 4
                =
              D.prefixExponent 3 +
                D.forwardExponent 3 := hK4
            _ = 4 + 2 := by
              rw [hP3, h2]
            _ = 6 := by
              norm_num
        have hEq := hres
        rw [hP4] at hEq
        norm_num [
          forwardAffine,
          hK0,
          hK1,
          hP2,
          hP3
        ] at hEq
        have hhalf :
            729 * D.fullLevel =
              198 + 64 * q := by
          omega
        have hmod :
            D.fullLevel % 64 = 54 :=
          fullLevel_mod_sixtyFour_eq_fiftyFour_of_1122 hhalf
        exact
          Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inl
                    (exists_eq_mul_add_of_mod_eq hmod)))))

    · rcases h121.2.2 with h1 | h2
      · have hP2 :
            D.prefixExponent 2 = 3 := by
          calc
            D.prefixExponent 2
                =
              D.prefixExponent 1 +
                D.forwardExponent 1 := hK2
            _ = 1 + 2 := by
              rw [hK1, h121.1]
            _ = 3 := by
              norm_num
        have hP3 :
            D.prefixExponent 3 = 4 := by
          calc
            D.prefixExponent 3
                =
              D.prefixExponent 2 +
                D.forwardExponent 2 := hK3
            _ = 3 + 1 := by
              rw [hP2, h121.2.1]
            _ = 4 := by
              norm_num
        have hP4 :
            D.prefixExponent 4 = 5 := by
          calc
            D.prefixExponent 4
                =
              D.prefixExponent 3 +
                D.forwardExponent 3 := hK4
            _ = 4 + 1 := by
              rw [hP3, h1]
            _ = 5 := by
              norm_num
        have hEq := hres
        rw [hP4] at hEq
        norm_num [
          forwardAffine,
          hK0,
          hK1,
          hP2,
          hP3
        ] at hEq
        have hhalf :
            729 * D.fullLevel =
              176 + 32 * q := by
          omega
        have hmod :
            D.fullLevel % 32 = 16 :=
          fullLevel_mod_thirtyTwo_eq_sixteen_of_1211 hhalf
        exact
          Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inl
                      (exists_eq_mul_add_of_mod_eq hmod))))))
      · have hP2 :
            D.prefixExponent 2 = 3 := by
          calc
            D.prefixExponent 2
                =
              D.prefixExponent 1 +
                D.forwardExponent 1 := hK2
            _ = 1 + 2 := by
              rw [hK1, h121.1]
            _ = 3 := by
              norm_num
        have hP3 :
            D.prefixExponent 3 = 4 := by
          calc
            D.prefixExponent 3
                =
              D.prefixExponent 2 +
                D.forwardExponent 2 := hK3
            _ = 3 + 1 := by
              rw [hP2, h121.2.1]
            _ = 4 := by
              norm_num
        have hP4 :
            D.prefixExponent 4 = 6 := by
          calc
            D.prefixExponent 4
                =
              D.prefixExponent 3 +
                D.forwardExponent 3 := hK4
            _ = 4 + 2 := by
              rw [hP3, h2]
            _ = 6 := by
              norm_num
        have hEq := hres
        rw [hP4] at hEq
        norm_num [
          forwardAffine,
          hK0,
          hK1,
          hP2,
          hP3
        ] at hEq
        have hhalf :
            729 * D.fullLevel =
              192 + 64 * q := by
          omega
        have hmod :
            D.fullLevel % 64 = 0 :=
          fullLevel_mod_sixtyFour_eq_zero_of_1212 hhalf
        exact
          Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (exists_eq_mul_add_of_mod_eq hmod))))))

end E2ZeroCenteredTrajectoryData
end EndpointFloorZero
end PositiveReturn
end AdjacentReturn
end Collatz
