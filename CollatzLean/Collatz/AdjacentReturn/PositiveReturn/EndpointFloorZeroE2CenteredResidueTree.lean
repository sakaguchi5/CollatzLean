import CollatzLean.Collatz.AdjacentReturn.PositiveReturn.EndpointFloorZeroE2CenteredSmallBand

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



/-- `x % m = r` から標準的な residue 表現を得る。 -/
private theorem exists_eq_mul_add_of_mod_eq
    {x m r : ℕ}
    (hmod : x % m = r) :
    ∃ q : ℕ, x = m * q + r := by
  refine ⟨x / m, ?_⟩
  have h := Nat.mod_add_div x m
  rw [hmod] at h
  omega

/--
forward prefix の pure state。

depth `k` まで進んだ時点で

- cumulative exponent が `K`
- affine constant が `A`

であることだけを保持する。
-/
structure ForwardPrefixStateAt
    (D : E2ZeroCenteredTrajectoryData)
    (k K A : ℕ) : Prop where
  exponent_eq :
    D.prefixExponent k = K
  affine_eq :
    D.forwardAffine k = A

/-- depth 0 の初期 state。 -/
theorem forwardPrefixState_zero
    (D : E2ZeroCenteredTrajectoryData) :
    ForwardPrefixStateAt D 0 0 0 := by
  exact {
    exponent_eq := D.prefixExponent_zero
    affine_eq := rfl
  }

/--
state を一段 forward に進める一般 transition。

`(k,K,A) --e--> (k+1, K+e, 3*A+2^K)`。
-/
theorem ForwardPrefixStateAt.step
    {D : E2ZeroCenteredTrajectoryData}
    {k K A e : ℕ}
    (S : ForwardPrefixStateAt D k K A)
    (hk : k < D.length)
    (he : D.forwardExponent k = e) :
    ForwardPrefixStateAt
      D
      (k + 1)
      (K + e)
      (3 * A + 2 ^ K) := by
  constructor
  · rw [
      D.prefixExponent_succ hk,
      S.exponent_eq,
      he
    ]
  · rw [
      D.forwardAffine_succ,
      S.affine_eq,
      S.exponent_eq
    ]

/-- 最初の exponent `1` を入れた depth 1 state。 -/
theorem forwardPrefixState_one
    (D : E2ZeroCenteredTrajectoryData) :
    ForwardPrefixStateAt D 1 1 1 := by
  have h7 := D.seven_le_length
  have h :=
    D.forwardPrefixState_zero.step
      (by omega)
      D.forwardExponent_zero_eq_one
  norm_num at h
  exact h

/--
expanding 条件だけから next exponent を一般に上から抑える。

`3^(k+3) ≤ 2^(3+K+E)` なら、
actual next exponent は `E` 未満。
-/
theorem ForwardPrefixStateAt.nextExponent_lt
    {D : E2ZeroCenteredTrajectoryData}
    {k K A E : ℕ}
    (S : ForwardPrefixStateAt D k K A)
    (hk : k + 1 < D.length)
    (hThreshold :
      3 ^ (k + 3) ≤
        2 ^ (3 + K + E)) :
    D.forwardExponent k < E := by
  have hk0 : k < D.length := by
    omega
  have hExp :=
    D.prefix_expanding (k + 1) hk
  have hK :=
    D.prefixExponent_succ (k := k) hk0
  rw [hK, S.exponent_eq] at hExp
  have hExp' :
      2 ^ (3 + K + D.forwardExponent k) <
        3 ^ (k + 3) := by
    simpa [
      Nat.add_assoc,
      Nat.add_comm,
      Nat.add_left_comm
    ] using hExp
  by_contra hnot
  have hE :
      E ≤ D.forwardExponent k := by
    omega
  have hpow :
      2 ^ (3 + K + E) ≤
        2 ^ (3 + K + D.forwardExponent k) :=
    Nat.pow_le_pow_right
      (by omega : 0 < (2 : ℕ))
      (by omega)
  omega

/--
prefix state `(k,K,A)` から full level の一般 2-adic residue を得る。

exact prefix equation
`18*3^k*L + A = 2^K + 2^(K+1)*q + 5*3^k`
を2で割った中心量 `C` を

`2*C + A = 2^K + 5*3^k`

で与える。

さらに
`C ≡ 3^(k+2)*r (mod 2^K)`
なら、odd coefficient `3^(k+2)` を cancel して
`L ≡ r (mod 2^K)`。
-/
theorem ForwardPrefixStateAt.fullLevel_modEq
    {D : E2ZeroCenteredTrajectoryData}
    {k K A C r : ℕ}
    (S : ForwardPrefixStateAt D k K A)
    (hk : k ≤ D.length)
    (hCenter :
      2 * C + A =
        2 ^ K + 5 * 3 ^ k)
    (hResidue :
      C ≡ 3 ^ (k + 2) * r [MOD 2 ^ K]) :
    D.fullLevel ≡ r [MOD 2 ^ K] := by
  obtain ⟨q, hEq⟩ :=
    D.exists_fullLevel_prefixResidueEquation hk
  rw [
    S.exponent_eq,
    S.affine_eq
  ] at hEq
  have hCoef :
      18 * 3 ^ k =
        2 * 3 ^ (k + 2) := by
    rw [pow_add]
    norm_num
    ring
  have hPow :
      2 ^ (K + 1) =
        2 * 2 ^ K := by
    rw [pow_succ]
    ring
  rw [hCoef, hPow] at hEq
  have hHalf :
      3 ^ (k + 2) * D.fullLevel =
        C + 2 ^ K * q := by
    nlinarith [hEq, hCenter]
  have hLeft :
      3 ^ (k + 2) * D.fullLevel ≡
        C [MOD 2 ^ K] := by
    change
      (3 ^ (k + 2) * D.fullLevel) % 2 ^ K =
        C % 2 ^ K
    rw [hHalf]
    simp [Nat.add_mod]
  have hCombined :
      3 ^ (k + 2) * D.fullLevel ≡
        3 ^ (k + 2) * r [MOD 2 ^ K] :=
    hLeft.trans hResidue
  have hCop :
      Nat.Coprime
        (3 ^ (k + 2))
        (2 ^ K) :=
    (by decide : Nat.Coprime 3 2).pow
      (k + 2) K
  have hCop' :
      (2 ^ K).gcd (3 ^ (k + 2)) = 1 := by
    simpa [Nat.Coprime] using hCop.symm
  exact
    Nat.ModEq.cancel_left_of_coprime
      hCop' hCombined

/--
prefix state から standard residue 表現
`L = 2^K*q+r` を直接得る。
-/
theorem ForwardPrefixStateAt.exists_fullLevel_eq
    {D : E2ZeroCenteredTrajectoryData}
    {k K A C r : ℕ}
    (S : ForwardPrefixStateAt D k K A)
    (hk : k ≤ D.length)
    (hr : r < 2 ^ K)
    (hCenter :
      2 * C + A =
        2 ^ K + 5 * 3 ^ k)
    (hResidue :
      C ≡ 3 ^ (k + 2) * r [MOD 2 ^ K]) :
    ∃ q : ℕ,
      D.fullLevel = 2 ^ K * q + r := by
  have hmodEq :=
    S.fullLevel_modEq hk hCenter hResidue
  have hmod :
      D.fullLevel % 2 ^ K = r := by
    simpa only [
      Nat.ModEq,
      Nat.mod_eq_of_lt hr
    ] using hmodEq
  exact exists_eq_mul_add_of_mod_eq hmod

/-- prefix `11` の state。 -/
private theorem forwardPrefixState_11
    (D : E2ZeroCenteredTrajectoryData)
    (h1 : D.forwardExponent 1 = 1) :
    ForwardPrefixStateAt D 2 2 5 := by
  have h7 := D.seven_le_length
  have h :=
    D.forwardPrefixState_one.step
      (by omega)
      h1
  norm_num at h
  exact h

/-- prefix `12` の state。 -/
private theorem forwardPrefixState_12
    (D : E2ZeroCenteredTrajectoryData)
    (h1 : D.forwardExponent 1 = 2) :
    ForwardPrefixStateAt D 2 3 5 := by
  have h7 := D.seven_le_length
  have h :=
    D.forwardPrefixState_one.step
      (by omega)
      h1
  norm_num at h
  exact h

/-- prefix `111` の state。 -/
private theorem forwardPrefixState_111
    (D : E2ZeroCenteredTrajectoryData)
    (h1 : D.forwardExponent 1 = 1)
    (h2 : D.forwardExponent 2 = 1) :
    ForwardPrefixStateAt D 3 3 19 := by
  have h7 := D.seven_le_length
  have h :=
    (D.forwardPrefixState_11 h1).step
      (by omega)
      h2
  norm_num at h
  exact h

/-- prefix `112` の state。 -/
private theorem forwardPrefixState_112
    (D : E2ZeroCenteredTrajectoryData)
    (h1 : D.forwardExponent 1 = 1)
    (h2 : D.forwardExponent 2 = 2) :
    ForwardPrefixStateAt D 3 4 19 := by
  have h7 := D.seven_le_length
  have h :=
    (D.forwardPrefixState_11 h1).step
      (by omega)
      h2
  norm_num at h
  exact h

/-- prefix `121` の state。 -/
private theorem forwardPrefixState_121
    (D : E2ZeroCenteredTrajectoryData)
    (h1 : D.forwardExponent 1 = 2)
    (h2 : D.forwardExponent 2 = 1) :
    ForwardPrefixStateAt D 3 4 23 := by
  have h7 := D.seven_le_length
  have h :=
    (D.forwardPrefixState_12 h1).step
      (by omega)
      h2
  norm_num at h
  exact h

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
  have he1Pos :
      0 < D.forwardExponent 1 :=
    D.forwardExponent_pos (by omega)
  have he1Lt :
      D.forwardExponent 1 < 3 :=
    D.forwardPrefixState_one.nextExponent_lt
      (E := 3)
      (by omega)
      (by norm_num)
  by_cases h11 :
      D.forwardExponent 1 = 1
  · have S2 :=
      D.forwardPrefixState_11 h11
    have he2Pos :
        0 < D.forwardExponent 2 :=
      D.forwardExponent_pos (by omega)
    have he2Lt :
        D.forwardExponent 2 < 3 :=
      S2.nextExponent_lt
        (E := 3)
        (by omega)
        (by norm_num)
    by_cases h21 :
        D.forwardExponent 2 = 1
    · exact Or.inl ⟨h11, h21⟩
    · have h22 :
          D.forwardExponent 2 = 2 := by
        omega
      exact
        Or.inr
          (Or.inl ⟨h11, h22⟩)
  · have h12 :
        D.forwardExponent 1 = 2 := by
      omega
    have S2 :=
      D.forwardPrefixState_12 h12
    have he2Pos :
        0 < D.forwardExponent 2 :=
      D.forwardExponent_pos (by omega)
    have he2Lt :
        D.forwardExponent 2 < 2 :=
      S2.nextExponent_lt
        (E := 2)
        (by omega)
        (by norm_num)
    have h21 :
        D.forwardExponent 2 = 1 := by
      omega
    exact
      Or.inr
        (Or.inr ⟨h12, h21⟩)

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
  rcases D.thirdForwardPattern with h111 | hrest
  · have S3 :=
      D.forwardPrefixState_111
        h111.1 h111.2
    have hL :=
      S3.exists_fullLevel_eq
        (hk := by omega)
        (C := 62)
        (r := 2)
        (hr := by norm_num)
        (hCenter := by norm_num)
        (hResidue := by
          norm_num [
            Nat.ModEq,
            Nat.add_mod,
            Nat.mul_mod
          ])
    norm_num at hL
    exact Or.inl hL
  · rcases hrest with h112 | h121
    · have S3 :=
        D.forwardPrefixState_112
          h112.1 h112.2
      have hL :=
        S3.exists_fullLevel_eq
          (hk := by omega)
          (C := 66)
          (r := 6)
          (hr := by norm_num)
          (hCenter := by norm_num)
          (hResidue := by
            norm_num [
              Nat.ModEq,
              Nat.add_mod,
              Nat.mul_mod
            ])
      norm_num at hL
      exact
        Or.inr
          (Or.inl hL)
    · have S3 :=
        D.forwardPrefixState_121
          h121.1 h121.2
      have hL :=
        S3.exists_fullLevel_eq
          (hk := by omega)
          (C := 64)
          (r := 0)
          (hr := by norm_num)
          (hCenter := by norm_num)
          (hResidue := by
            norm_num [
              Nat.ModEq,
              Nat.add_mod,
              Nat.mul_mod
            ])
      norm_num at hL
      exact
        Or.inr
          (Or.inr hL)

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
  rcases D.thirdForwardPattern with h111 | hrest
  · have S3 :=
      D.forwardPrefixState_111
        h111.1 h111.2
    have he3Lt :
        D.forwardExponent 3 < 4 :=
      S3.nextExponent_lt
        (E := 4)
        (by omega)
        (by norm_num)
    have he3 :
        D.forwardExponent 3 = 1 ∨
        D.forwardExponent 3 = 2 ∨
        D.forwardExponent 3 = 3 := by
      omega
    exact
      Or.inl
        ⟨h111.1, h111.2, he3⟩
  · rcases hrest with h112 | h121
    · have S3 :=
        D.forwardPrefixState_112
          h112.1 h112.2
      have he3Lt :
          D.forwardExponent 3 < 3 :=
        S3.nextExponent_lt
          (E := 3)
          (by omega)
          (by norm_num)
      have he3 :
          D.forwardExponent 3 = 1 ∨
          D.forwardExponent 3 = 2 := by
        omega
      exact
        Or.inr
          (Or.inl
            ⟨h112.1, h112.2, he3⟩)
    · have S3 :=
        D.forwardPrefixState_121
          h121.1 h121.2
      have he3Lt :
          D.forwardExponent 3 < 3 :=
        S3.nextExponent_lt
          (E := 3)
          (by omega)
          (by norm_num)
      have he3 :
          D.forwardExponent 3 = 1 ∨
          D.forwardExponent 3 = 2 := by
        omega
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
  rcases D.fourthForwardPattern with h111 | hrest
  · have S3 :=
      D.forwardPrefixState_111
        h111.1 h111.2.1
    rcases h111.2.2 with h1 | h23
    · have S4 :
          ForwardPrefixStateAt D 4 4 65 := by
        have h :=
          S3.step (by omega) h1
        norm_num at h
        exact h
      have hL :=
        S4.exists_fullLevel_eq
          (hk := by omega)
          (C := 178)
          (r := 2)
          (hr := by norm_num)
          (hCenter := by norm_num)
          (hResidue := by
            norm_num [
              Nat.ModEq,
              Nat.add_mod,
              Nat.mul_mod
            ])
      norm_num at hL
      exact Or.inl hL
    · rcases h23 with h2 | h3
      · have S4 :
            ForwardPrefixStateAt D 4 5 65 := by
          have h :=
            S3.step (by omega) h2
          norm_num at h
          exact h
        have hL :=
          S4.exists_fullLevel_eq
            (hk := by omega)
            (C := 186)
            (r := 10)
            (hr := by norm_num)
            (hCenter := by norm_num)
            (hResidue := by
              norm_num [
                Nat.ModEq,
                Nat.add_mod,
                Nat.mul_mod
              ])
        norm_num at hL
        exact
          Or.inr
            (Or.inl hL)
      · have S4 :
            ForwardPrefixStateAt D 4 6 65 := by
          have h :=
            S3.step (by omega) h3
          norm_num at h
          exact h
        have hL :=
          S4.exists_fullLevel_eq
            (hk := by omega)
            (C := 202)
            (r := 26)
            (hr := by norm_num)
            (hCenter := by norm_num)
            (hResidue := by
              norm_num [
                Nat.ModEq,
                Nat.add_mod,
                Nat.mul_mod
              ])
        norm_num at hL
        exact
          Or.inr
            (Or.inr
              (Or.inl hL))
  · rcases hrest with h112 | h121
    · have S3 :=
        D.forwardPrefixState_112
          h112.1 h112.2.1
      rcases h112.2.2 with h1 | h2
      · have S4 :
            ForwardPrefixStateAt D 4 5 73 := by
          have h :=
            S3.step (by omega) h1
          norm_num at h
          exact h
        have hL :=
          S4.exists_fullLevel_eq
            (hk := by omega)
            (C := 182)
            (r := 6)
            (hr := by norm_num)
            (hCenter := by norm_num)
            (hResidue := by
              norm_num [
                Nat.ModEq,
                Nat.add_mod,
                Nat.mul_mod
              ])
        norm_num at hL
        exact
          Or.inr
            (Or.inr
              (Or.inr
                (Or.inl hL)))
      · have S4 :
            ForwardPrefixStateAt D 4 6 73 := by
          have h :=
            S3.step (by omega) h2
          norm_num at h
          exact h
        have hL :=
          S4.exists_fullLevel_eq
            (hk := by omega)
            (C := 198)
            (r := 54)
            (hr := by norm_num)
            (hCenter := by norm_num)
            (hResidue := by
              norm_num [
                Nat.ModEq,
                Nat.add_mod,
                Nat.mul_mod
              ])
        norm_num at hL
        exact
          Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inl hL))))
    · have S3 :=
        D.forwardPrefixState_121
          h121.1 h121.2.1
      rcases h121.2.2 with h1 | h2
      · have S4 :
            ForwardPrefixStateAt D 4 5 85 := by
          have h :=
            S3.step (by omega) h1
          norm_num at h
          exact h
        have hL :=
          S4.exists_fullLevel_eq
            (hk := by omega)
            (C := 176)
            (r := 16)
            (hr := by norm_num)
            (hCenter := by norm_num)
            (hResidue := by
              norm_num [
                Nat.ModEq,
                Nat.add_mod,
                Nat.mul_mod
              ])
        norm_num at hL
        exact
          Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inl hL)))))
      · have S4 :
            ForwardPrefixStateAt D 4 6 85 := by
          have h :=
            S3.step (by omega) h2
          norm_num at h
          exact h
        have hL :=
          S4.exists_fullLevel_eq
            (hk := by omega)
            (C := 192)
            (r := 0)
            (hr := by norm_num)
            (hCenter := by norm_num)
            (hResidue := by
              norm_num [
                Nat.ModEq,
                Nat.add_mod,
                Nat.mul_mod
              ])
        norm_num at hL
        exact
          Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr hL)))))

end E2ZeroCenteredTrajectoryData
end EndpointFloorZero
end PositiveReturn
end AdjacentReturn
end Collatz
