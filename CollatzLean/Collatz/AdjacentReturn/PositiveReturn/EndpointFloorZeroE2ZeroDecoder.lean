import CollatzLean.Collatz.AdjacentReturn.PositiveReturn.EndpointFloorZeroE2Budget

/-!
# E2 quotient-zero survivor の endpoint-centered decoder

E2 inner replay の quotient `0` では inner word `u` 自身が
canonical start から canonical end まで actual に走る。
さらに whole endpoint-floor により、`u` の任意の nonempty suffix の
actual start は terminal endpoint `T` より真に上にある。

このファイルでは `j=0` 固有の情報を次の形へ圧縮する。

* `E2ZeroSurvivorData`:
  quotient zero と、既存 exponent-floor budget を生き残った packet。
* endpoint half-gap coordinate:
  suffix start `x_r = T + 2*h_r`。
* exact backward recurrence:

    `6*h_(r+1) + 1 + 3*T
       = 2^e*T + 2^(e+1)*h_r`。

* endpoint-floor-aware exact gap identity:

    `gap_r*T = B_r + 2*3^r*h_r`。

従って `h_r >= 1` から各 suffix で

    `B_r + 2*3^r <= gap_r*T`

が得られる。これを全 suffix へ重み付きで足した
`endpointFloorBudgetLower` を導入し、既存 `suffixExponentFloor` lower と
endpoint-floor lower を同時に保持する survivor inequality を作る。
-/

namespace Collatz
namespace Word

/--
endpoint-floor を使う suffix budget lower。

各 nonempty suffix `z` について endpoint-centered exact identity が

  `contractingGap z * T = affineConst z + 2*3^(oddSteps z)*h`

かつ `h >= 1` を与えるとき、右辺の最小値

  `affineConst z + 2*3^(oddSteps z)`

を head 側2冪で重み付けして足す。
-/
def endpointFloorBudgetLower : Collatz.Word → ℕ
  | [] => 0
  | e :: w =>
      Word.affineConst (e :: w) +
        2 * 3 ^ Word.oddSteps (e :: w) +
        2 ^ e * endpointFloorBudgetLower w

@[simp] theorem endpointFloorBudgetLower_nil :
    endpointFloorBudgetLower ([] : Collatz.Word) = 0 := rfl

@[simp] theorem endpointFloorBudgetLower_cons
    (e : ℕ) (w : Collatz.Word) :
    endpointFloorBudgetLower (e :: w) =
      Word.affineConst (e :: w) +
        2 * 3 ^ Word.oddSteps (e :: w) +
        2 ^ e * endpointFloorBudgetLower w := rfl

/--
各 nonempty suffix の endpoint-floor lower が成立することを recursive に保持する。
-/
def EndpointFloorSuffixCondition : Collatz.Word → ℕ → Prop
  | [], _ => True
  | e :: w, T =>
      Word.affineConst (e :: w) +
          2 * 3 ^ Word.oddSteps (e :: w) ≤
        Word.contractingGap (e :: w) * T ∧
      EndpointFloorSuffixCondition w T

/--
全 drop suffix に pointwise endpoint-floor lower があれば recursive condition を得る。
-/
theorem endpointFloorSuffixCondition_of_drop
    {w : Collatz.Word} {T : ℕ}
    (h :
      ∀ k : ℕ,
        k < w.length →
          Word.affineConst (w.drop k) +
              2 * 3 ^ Word.oddSteps (w.drop k) ≤
            Word.contractingGap (w.drop k) * T) :
    EndpointFloorSuffixCondition w T := by
  induction w with
  | nil =>
      simp [EndpointFloorSuffixCondition]
  | cons e w ih =>
      change
        Word.affineConst (e :: w) +
              2 * 3 ^ Word.oddSteps (e :: w) ≤
            Word.contractingGap (e :: w) * T ∧
          EndpointFloorSuffixCondition w T
      constructor
      · simpa using h 0 (by simp)
      · apply ih
        intro k hk
        have hk' : k + 1 < (e :: w).length := by
          simp only [List.length_cons]
          omega
        have hh := h (k + 1) hk'
        simpa using hh

/--
endpoint-floor lower の重み付き和は `T * suffixGapBudget` 以下。
-/
theorem endpointFloorBudgetLower_le_mul_suffixGapBudget
    {w : Collatz.Word} {T : ℕ}
    (h : EndpointFloorSuffixCondition w T) :
    endpointFloorBudgetLower w ≤ T * Word.suffixGapBudget w := by
  induction w with
  | nil =>
      simp [endpointFloorBudgetLower, Word.suffixGapBudget]
  | cons e w ih =>
      change
        Word.affineConst (e :: w) +
              2 * 3 ^ Word.oddSteps (e :: w) ≤
            Word.contractingGap (e :: w) * T ∧
          EndpointFloorSuffixCondition w T at h
      rcases h with ⟨hWhole, hTail⟩
      have hTailLower := ih hTail
      have hTailScaled :
          2 ^ e * endpointFloorBudgetLower w ≤
            2 ^ e * (T * Word.suffixGapBudget w) :=
        Nat.mul_le_mul_left (2 ^ e) hTailLower
      have hGapEq :
          Word.contractingGap (e :: w) =
            2 ^ Word.twoSteps (e :: w) -
              3 ^ Word.oddSteps (e :: w) := by
        rfl
      simp only [endpointFloorBudgetLower_cons, Word.suffixGapBudget_cons]
      rw [hGapEq] at hWhole
      calc
        Word.affineConst (e :: w) +
              2 * 3 ^ Word.oddSteps (e :: w) +
            2 ^ e * endpointFloorBudgetLower w
            ≤
          (2 ^ Word.twoSteps (e :: w) -
              3 ^ Word.oddSteps (e :: w)) * T +
            2 ^ e * (T * Word.suffixGapBudget w) :=
          Nat.add_le_add hWhole hTailScaled
        _ =
          T *
            ((2 ^ Word.twoSteps (e :: w) -
                3 ^ Word.oddSteps (e :: w)) +
              2 ^ e * Word.suffixGapBudget w) := by
          ring

end Word

namespace AdjacentReturn
namespace PositiveReturn
namespace EndpointFloorZero

namespace E2BranchData

/-- inner word の先頭から `m-r` 文字を取った prefix。 -/
def zeroPrefixWord
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (_B : E2BranchData v boundary n d u)
    (r : ℕ) : Collatz.Word :=
  u.take (u.length - r)

/-- inner word の末尾 `r` 文字。 -/
def zeroSuffixWord
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (_B : E2BranchData v boundary n d u)
    (r : ℕ) : Collatz.Word :=
  u.drop (u.length - r)

/-- canonical run を prefix/suffix に split した中間値は必ず存在する。 -/
theorem exists_zeroBackwardSplit
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E2BranchData v boundary n d u)
    (r : ℕ) :
    ∃ x : ℕ,
      Word.Runs (B.zeroPrefixWord r)
        (Word.canonicalStart u) x ∧
      Word.Runs (B.zeroSuffixWord r)
        x (Word.canonicalEnd u) := by
  have hrun :
      Word.Runs u
        (Word.canonicalStart u)
        (Word.canonicalEnd u) :=
    B.inner_valid.canonicalRuns
  have hdecomp :
      B.zeroPrefixWord r ++ B.zeroSuffixWord r = u := by
    dsimp [zeroPrefixWord, zeroSuffixWord]
    exact List.take_append_drop (u.length - r) u
  have hrun' :
      Word.Runs
        (B.zeroPrefixWord r ++ B.zeroSuffixWord r)
        (Word.canonicalStart u)
        (Word.canonicalEnd u) := by
    rw [hdecomp]
    exact hrun
  exact hrun'.split_append

/-- suffix length `r` に対応する canonical-run boundary。 -/
noncomputable def zeroBackwardValue
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E2BranchData v boundary n d u)
    (r : ℕ) : ℕ :=
  by
    classical
    exact Nat.find (B.exists_zeroBackwardSplit r)

/-- `zeroBackwardValue` までの canonical prefix run。 -/
theorem zeroPrefix_runs
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E2BranchData v boundary n d u)
    (r : ℕ) :
    Word.Runs (B.zeroPrefixWord r)
      (Word.canonicalStart u)
      (B.zeroBackwardValue r) := by
  classical
  exact (Nat.find_spec (B.exists_zeroBackwardSplit r)).1

/-- `zeroBackwardValue` から terminal までの canonical suffix run。 -/
theorem zeroSuffix_runs
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E2BranchData v boundary n d u)
    (r : ℕ) :
    Word.Runs (B.zeroSuffixWord r)
      (B.zeroBackwardValue r)
      (Word.canonicalEnd u) := by
  classical
  exact (Nat.find_spec (B.exists_zeroBackwardSplit r)).2

/-- suffix cumulative exponent。 -/
def zeroSuffixExponent
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E2BranchData v boundary n d u)
    (r : ℕ) : ℕ :=
  Word.twoSteps (B.zeroSuffixWord r)

/-- suffix affine constant。 -/
def zeroSuffixAffine
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E2BranchData v boundary n d u)
    (r : ℕ) : ℕ :=
  Word.affineConst (B.zeroSuffixWord r)

/-- `r ≤ m` なら inner suffix の odd-step 数は exactly `r`。 -/
@[simp] theorem zeroSuffix_oddSteps
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E2BranchData v boundary n d u)
    {r : ℕ} (hr : r ≤ u.length) :
    Word.oddSteps (B.zeroSuffixWord r) = r := by
  have hlen : u.length - (u.length - r) = r := by
    omega
  simp [zeroSuffixWord, Word.oddSteps, hlen]

/-- inner suffix の exact affine equation。 -/
theorem zeroSuffix_exactEquation
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E2BranchData v boundary n d u)
    {r : ℕ} (hr : r ≤ u.length) :
    3 ^ r * B.zeroBackwardValue r + B.zeroSuffixAffine r =
      2 ^ B.zeroSuffixExponent r * Word.canonicalEnd u := by
  have hreal := (B.zeroSuffix_runs r).realizes
  unfold Word.Realizes at hreal
  rw [B.zeroSuffix_oddSteps hr] at hreal
  simpa [zeroSuffixExponent, zeroSuffixAffine] using hreal.symm

/-- nonempty inner suffix は contracting。 -/
theorem zeroSuffix_threePow_lt_twoPow
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E2BranchData v boundary n d u)
    {r : ℕ}
    (hrPos : 0 < r)
    (hrLe : r ≤ u.length) :
    3 ^ r < 2 ^ B.zeroSuffixExponent r := by
  have h :=
    B.inner_allSuffixesContracting.lastSuffix_threePow_lt_twoPow
      hrPos hrLe
  simpa [zeroSuffixWord, zeroSuffixExponent] using h

/-- suffix length 0 の boundary は terminal endpoint。 -/
theorem zeroBackwardValue_zero
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E2BranchData v boundary n d u) :
    B.zeroBackwardValue 0 = Word.canonicalEnd u := by
  have h := B.zeroSuffix_exactEquation (r := 0) (by omega)
  simpa [zeroSuffixWord, zeroSuffixExponent, zeroSuffixAffine] using h

/-- suffix length `m` の boundary は inner canonical start。 -/
theorem zeroBackwardValue_full
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E2BranchData v boundary n d u) :
    B.zeroBackwardValue u.length = Word.canonicalStart u := by
  have hEq :=
    B.zeroSuffix_exactEquation (r := u.length) le_rfl
  have hCan := Word.canonicalEnd_realizes u
  have hCan' :
      2 ^ Word.twoSteps u * Word.canonicalEnd u =
        3 ^ u.length * Word.canonicalStart u +
          Word.affineConst u := by
    simpa [Word.Realizes, Word.oddSteps] using hCan
  have hEq' :
      3 ^ u.length * B.zeroBackwardValue u.length +
          Word.affineConst u =
        2 ^ Word.twoSteps u * Word.canonicalEnd u := by
    simpa [zeroSuffixWord, zeroSuffixExponent, zeroSuffixAffine] using hEq
  have hp : 0 < 3 ^ u.length := Nat.pow_pos (by omega)
  nlinarith


/-- zero backward boundary は奇数。quotient-zero 仮定は不要。 -/
theorem zeroBackwardValue_odd
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E2BranchData v boundary n d u)
    (r : ℕ) :
    Odd (B.zeroBackwardValue r) := by
  classical
  have hsuffix :
      Word.Runs
        (B.zeroSuffixWord r)
        (B.zeroBackwardValue r)
        (Word.canonicalEnd u) := by
    have hsplit :=
      Nat.find_spec (B.exists_zeroBackwardSplit r)
    simpa [E2BranchData.zeroBackwardValue] using hsplit.2
  exact
    hsuffix.start_odd
      (Word.canonicalEnd_odd u)

/--
末尾 `r+1` 文字が `e :: (末尾 r 文字)` と書けるときの one-step exact equation。
quotient-zero 仮定は不要で、E2 inner canonical run だけから従う。
-/
theorem zeroBackwardStepEquation
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E2BranchData v boundary n d u)
    {r e : ℕ}
    (hr : r < u.length)
    (hWord :
      B.zeroSuffixWord (r + 1) =
        e :: B.zeroSuffixWord r) :
    2 ^ e * B.zeroBackwardValue r =
      3 * B.zeroBackwardValue (r + 1) + 1 := by
  have hrLe : r ≤ u.length := by omega
  have hrSuccLe : r + 1 ≤ u.length := by omega
  have hEq0 := B.zeroSuffix_exactEquation hrLe
  have hEq1 := B.zeroSuffix_exactEquation hrSuccLe
  have hK :
      B.zeroSuffixExponent (r + 1) =
        e + B.zeroSuffixExponent r := by
    dsimp [E2BranchData.zeroSuffixExponent]
    rw [hWord]
    simp
  have hB :
      B.zeroSuffixAffine (r + 1) =
        3 ^ r + 2 ^ e * B.zeroSuffixAffine r := by
    dsimp [E2BranchData.zeroSuffixAffine]
    rw [hWord, Word.affineConst_cons, B.zeroSuffix_oddSteps hrLe]
  have h2pow :
      2 ^ (e + B.zeroSuffixExponent r) =
        2 ^ e * 2 ^ B.zeroSuffixExponent r := by
    rw [pow_add]
  rw [hK, hB, h2pow] at hEq1
  have hScaled :=
    congrArg (fun z : ℕ => 2 ^ e * z) hEq0
  have h3 : 3 ^ (r + 1) = 3 ^ r * 3 := by
    rw [pow_succ]
  rw [h3] at hEq1
  have hcancel :
      3 ^ r * (2 ^ e * B.zeroBackwardValue r) =
        3 ^ r * (3 * B.zeroBackwardValue (r + 1) + 1) := by
    ring_nf at hScaled hEq1 ⊢
    nlinarith
  exact
    Nat.mul_left_cancel
      (Nat.pow_pos (by omega : 0 < (3 : ℕ))) hcancel

/--
`u=1::z` を使った最初の backward step。
E2 branch 全体で成立し、quotient-zero survivor は不要。
-/
theorem firstBackwardWord
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E2BranchData v boundary n d u) :
    B.zeroSuffixWord ((u.length - 1) + 1) =
      1 :: B.zeroSuffixWord (u.length - 1) := by
  obtain ⟨z, hu⟩ := B.inner_head_eq_one
  have hm : 0 < u.length := by
    have h7 := B.seven_le_innerLength
    omega
  have hsucc : u.length - 1 + 1 = u.length := by
    omega
  have hsub : u.length - (u.length - 1) = 1 := by
    omega
  rw [hsucc]
  dsimp [E2BranchData.zeroSuffixWord]
  rw [Nat.sub_self, hsub, hu]
  simp

end E2BranchData

/--
E2 inner quotient-zero branch の current-budget survivor。

最後の inequality は新仮定ではなく、既存 `budgetLower ≤ suffixGapBudget` と
ZERO strict upper から自動的に得られる。
-/
structure E2ZeroSurvivorData
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E2BranchData v boundary n d u) : Type where
  innerReplay : E2BranchData.InnerReplayData B
  quotient_eq : innerReplay.coordinate.quotient = 0
  budget_survives :
    3 * B.budgetLower <
      (3 * B.sigma + 5) * 2 ^ Word.twoSteps u

namespace E2BranchData

/-- 任意の quotient-zero inner replay は `E2ZeroSurvivorData` を与える。 -/
def zeroSurvivorData
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E2BranchData v boundary n d u)
    (I : InnerReplayData B)
    (hq : I.coordinate.quotient = 0) :
    E2ZeroSurvivorData B := by
  have hLower := B.budgetLower_le_suffixGapBudget
  have hLower3 :
      3 * B.budgetLower ≤ 3 * Word.suffixGapBudget u :=
    Nat.mul_le_mul_left 3 hLower
  have hUpper := B.innerReplay_zero_budget_strict_upper I hq
  exact {
    innerReplay := I
    quotient_eq := hq
    budget_survives := lt_of_le_of_lt hLower3 hUpper
  }

end E2BranchData

namespace E2ZeroSurvivorData

/-- quotient zero では inner actual start/end が double-canonical。 -/
theorem doubleCanonical
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    {B : E2BranchData v boundary n d u}
    (Z : E2ZeroSurvivorData B) :
    Z.innerReplay.y = Word.canonicalStart u ∧
      Word.canonicalEnd (1 :: v) = Word.canonicalEnd u :=
  B.innerReplay_zero_doubleCanonical Z.innerReplay Z.quotient_eq

/-- quotient zero では `2*s = 9*(n+d)-1`。 -/
theorem two_mul_start_eq
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    {B : E2BranchData v boundary n d u}
    (Z : E2ZeroSurvivorData B) :
    2 * Word.canonicalStart u = 9 * (n + d) - 1 := by
  have h := Z.innerReplay.two_y_eq
  rw [Z.doubleCanonical.1] at h
  exact h

/-- quotient zero では inner canonical endpoint は E2 endpoint coordinate そのもの。 -/
theorem end_add_one_eq
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    {B : E2BranchData v boundary n d u}
    (Z : E2ZeroSurvivorData B) :
    Word.canonicalEnd u + 1 = 6 * n + 4 * d := by
  have hFullTail := B.packet.fullEnd_eq_tailEnd
  have hZeroEnd := Z.doubleCanonical.2
  calc
    Word.canonicalEnd u + 1
        = Word.canonicalEnd (1 :: v) + 1 := by rw [hZeroEnd]
    _ = Word.canonicalEnd v + 1 := by rw [hFullTail]
    _ = 6 * n + 4 * d := B.coordinates.endpoint_add_one

/-- E2 ZERO では `d = 3*n+3+4*r₀` と一意的な非負余剰へ落ちる。 -/
theorem exists_zeroParameter
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    {B : E2BranchData v boundary n d u}
    (_Z : E2ZeroSurvivorData B) :
    ∃ r : ℕ, d = 3 * n + 3 + 4 * r := by
  obtain ⟨k, hk⟩ := B.coordinateSum_eq_four_mul_add_three
  have hd := B.three_mul_n_add_three_le_d
  have hnk : n ≤ k := by
    omega
  refine ⟨k - n, ?_⟩
  omega

/-- E2 ZERO の余剰 parameter `r₀`。 -/
noncomputable def zeroParameter
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    {B : E2BranchData v boundary n d u}
    (Z : E2ZeroSurvivorData B) : ℕ :=
  Nat.find Z.exists_zeroParameter

/-- `d = 3*n+3+4*r₀`。 -/
theorem zeroParameter_spec
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    {B : E2BranchData v boundary n d u}
    (Z : E2ZeroSurvivorData B) :
    d = 3 * n + 3 + 4 * Z.zeroParameter :=
  Nat.find_spec Z.exists_zeroParameter

/-- `q=n+d = 4*(n+r₀)+3`。 -/
theorem coordinateSum_eq_zeroParameter
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    {B : E2BranchData v boundary n d u}
    (Z : E2ZeroSurvivorData B) :
    n + d = 4 * (n + Z.zeroParameter) + 3 := by
  have hd := Z.zeroParameter_spec
  omega

/-- endpoint half-gap `h_m = r₀+1`。 -/
noncomputable def endpointHalfGap
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    {B : E2BranchData v boundary n d u}
    (Z : E2ZeroSurvivorData B) : ℕ :=
  Z.zeroParameter + 1

/-- full inner start は endpoint より `2*h_m` 上。 -/
theorem start_eq_end_add_two_mul_endpointHalfGap
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    {B : E2BranchData v boundary n d u}
    (Z : E2ZeroSurvivorData B) :
    Word.canonicalStart u =
      Word.canonicalEnd u + 2 * Z.endpointHalfGap := by
  have hs := Z.two_mul_start_eq
  have ht := Z.end_add_one_eq
  have hd := Z.zeroParameter_spec
  have hn := B.coordinates.n_pos
  dsimp [endpointHalfGap]
  omega

/-- endpoint を `(n,h_m)` だけで書く subtraction-free exact relation。 -/
theorem endpoint_add_five_eq
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    {B : E2BranchData v boundary n d u}
    (Z : E2ZeroSurvivorData B) :
    Word.canonicalEnd u + 5 =
      16 * Z.endpointHalfGap + 18 * n := by
  have ht := Z.end_add_one_eq
  have hd := Z.zeroParameter_spec
  dsimp [endpointHalfGap]
  omega

/-- ZERO defect: `9*T+5 = 8*s+18*n`。 -/
theorem zero_defect_balance
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    {B : E2BranchData v boundary n d u}
    (Z : E2ZeroSurvivorData B) :
    9 * Word.canonicalEnd u + 5 =
      8 * Word.canonicalStart u + 18 * n := by
  have h := B.innerReplay_balance Z.innerReplay
  rw [Z.quotient_eq] at h
  simp only [mul_zero, add_zero] at h
  exact h

/-- whole `[1,2]` は ZERO inner canonical start へ接続する。 -/
theorem headTwo_runs
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    {B : E2BranchData v boundary n d u}
    (Z : E2ZeroSurvivorData B) :
    Word.Runs ([1, 2] : Collatz.Word)
      (Word.canonicalStart (1 :: v))
      (Word.canonicalStart u) := by
  have h1 := B.packet.headRuns
  rw [B.packet.boundary_eq_tailStart] at h1
  obtain ⟨y, h2, _hyOdd, hy⟩ := B.firstTailStep
  have hIy := Z.innerReplay.two_y_eq
  have hyEq : y = Z.innerReplay.y := by
    omega
  rw [hyEq] at h2
  rw [Z.doubleCanonical.1] at h2
  have happ := h1.append h2
  simpa using happ

/-- inner prefix boundary まで whole prefix を actual に走る。 -/
theorem wholePrefix_runs_zeroBackwardValue
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    {B : E2BranchData v boundary n d u}
    (Z : E2ZeroSurvivorData B)
    {r : ℕ} :
    Word.Runs
      ((1 :: v).take (u.length - r + 2))
      (Word.canonicalStart (1 :: v))
      (B.zeroBackwardValue r) := by
  have hhead := Z.headTwo_runs
  have hpre := B.zeroPrefix_runs r
  have happ := hhead.append hpre
  have hword :
      ([1, 2] : Collatz.Word) ++ B.zeroPrefixWord r =
        (1 :: v).take (u.length - r + 2) := by
    change
      ([1, 2] : Collatz.Word) ++
          u.take (u.length - r) =
        (1 :: v).take (u.length - r + 2)
    rw [B.tail_eq]
    rw [show
      u.length - r + 2 =
        Nat.succ (Nat.succ (u.length - r)) by
          omega]
    simp
  rw [← hword]
  exact happ

/-- nonempty inner suffix の start は endpoint floor より terminal より真に上。 -/
theorem endpoint_lt_zeroBackwardValue
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    {B : E2BranchData v boundary n d u}
    (Z : E2ZeroSurvivorData B)
    {r : ℕ}
    (hrPos : 0 < r)
    (hrLe : r ≤ u.length) :
    Word.canonicalEnd u < B.zeroBackwardValue r := by
  let k := u.length - r + 2
  have hkPos : 0 < k := by
    dsimp [k]
    omega
  have hkLt : k < (1 :: v).length := by
    rw [B.tail_eq]
    simp only [List.length_cons]
    dsimp [k]
    omega
  have hrun := Z.wholePrefix_runs_zeroBackwardValue (r := r)
  have hfloor :=
    B.packet.endpointFloor k (B.zeroBackwardValue r)
      hkPos hkLt (by simpa [k] using hrun)
  have hZeroEnd := Z.doubleCanonical.2
  rw [← hZeroEnd]
  exact hfloor

/-- `r ≤ m` なら endpoint half-gap representation が存在する。 -/
theorem exists_zeroHalfGap
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    {B : E2BranchData v boundary n d u}
    (Z : E2ZeroSurvivorData B)
    {r : ℕ} (hrLe : r ≤ u.length) :
    ∃ h : ℕ,
      B.zeroBackwardValue r = Word.canonicalEnd u + 2 * h := by
  by_cases hr0 : r = 0
  · subst r
    refine ⟨0, ?_⟩
    simp [B.zeroBackwardValue_zero]
  · have hrPos : 0 < r := Nat.pos_of_ne_zero hr0
    have hfloor := Z.endpoint_lt_zeroBackwardValue hrPos hrLe
    have hxOdd := B.zeroBackwardValue_odd r
    have hTOdd := Word.canonicalEnd_odd u
    rcases hxOdd with ⟨a, ha⟩
    rcases hTOdd with ⟨b, hb⟩
    refine ⟨a - b, ?_⟩
    omega

/-- endpoint-centered half-gap `h_r`。範囲外では0に固定する。 -/
noncomputable def zeroHalfGap
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    {B : E2BranchData v boundary n d u}
    (Z : E2ZeroSurvivorData B)
    (r : ℕ) : ℕ :=
  if hr : r ≤ u.length then
    Nat.find (Z.exists_zeroHalfGap hr)
  else
    0

/-- `x_r = T + 2*h_r`。 -/
theorem zeroBackwardValue_eq_endpoint_add_two_mul_halfGap
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    {B : E2BranchData v boundary n d u}
    (Z : E2ZeroSurvivorData B)
    {r : ℕ} (hrLe : r ≤ u.length) :
    B.zeroBackwardValue r =
      Word.canonicalEnd u + 2 * Z.zeroHalfGap r := by
  unfold zeroHalfGap
  rw [dif_pos hrLe]
  exact Nat.find_spec (Z.exists_zeroHalfGap hrLe)

/-- `h_0=0`。 -/
theorem zeroHalfGap_zero
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    {B : E2BranchData v boundary n d u}
    (Z : E2ZeroSurvivorData B) :
    Z.zeroHalfGap 0 = 0 := by
  have h :=
    Z.zeroBackwardValue_eq_endpoint_add_two_mul_halfGap
      (r := 0) (by omega)
  rw [B.zeroBackwardValue_zero] at h
  omega

/-- nonempty suffix では `h_r>0`。 -/
theorem zeroHalfGap_pos
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    {B : E2BranchData v boundary n d u}
    (Z : E2ZeroSurvivorData B)
    {r : ℕ}
    (hrPos : 0 < r)
    (hrLe : r ≤ u.length) :
    0 < Z.zeroHalfGap r := by
  have hx :=
    Z.zeroBackwardValue_eq_endpoint_add_two_mul_halfGap hrLe
  have hfloor := Z.endpoint_lt_zeroBackwardValue hrPos hrLe
  omega

/-- full suffix half-gap は coordinate から得た `endpointHalfGap` と一致。 -/
theorem zeroHalfGap_full_eq_endpointHalfGap
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    {B : E2BranchData v boundary n d u}
    (Z : E2ZeroSurvivorData B) :
    Z.zeroHalfGap u.length = Z.endpointHalfGap := by
  have hx :=
    Z.zeroBackwardValue_eq_endpoint_add_two_mul_halfGap
      (r := u.length) le_rfl
  rw [B.zeroBackwardValue_full] at hx
  have hcoord := Z.start_eq_end_add_two_mul_endpointHalfGap
  omega

/--
endpoint-centered backward recurrence の subtraction-free 形。

`x_r=T+2h_r` と one-step equation を代入した exact identity。
-/
theorem zeroBackwardGapRecurrence
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    {B : E2BranchData v boundary n d u}
    (Z : E2ZeroSurvivorData B)
    {r e : ℕ}
    (hr : r < u.length)
    (hWord :
      B.zeroSuffixWord (r + 1) =
        e :: B.zeroSuffixWord r) :
    6 * Z.zeroHalfGap (r + 1) + 1 +
        3 * Word.canonicalEnd u =
      2 ^ e * Word.canonicalEnd u +
        2 ^ (e + 1) * Z.zeroHalfGap r := by
  have hrLe : r ≤ u.length := by omega
  have hrSuccLe : r + 1 ≤ u.length := by omega
  have hStep := B.zeroBackwardStepEquation hr hWord
  have hx0 :=
    Z.zeroBackwardValue_eq_endpoint_add_two_mul_halfGap hrLe
  have hx1 :=
    Z.zeroBackwardValue_eq_endpoint_add_two_mul_halfGap hrSuccLe
  rw [hx0, hx1] at hStep
  have hpow : 2 ^ (e + 1) = 2 ^ e * 2 := by
    rw [pow_succ]
  rw [hpow]
  nlinarith

/--
各 nonempty suffix の endpoint-centered exact gap identity。

`gap_r*T = B_r + 2*3^r*h_r`。
-/
theorem zeroSuffix_gap_mul_endpoint_eq_affine_add_center
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    {B : E2BranchData v boundary n d u}
    (Z : E2ZeroSurvivorData B)
    {r : ℕ}
    (hrPos : 0 < r)
    (hrLe : r ≤ u.length) :
    Word.contractingGap (B.zeroSuffixWord r) *
        Word.canonicalEnd u =
      B.zeroSuffixAffine r +
        2 * 3 ^ r * Z.zeroHalfGap r := by
  have hEq := B.zeroSuffix_exactEquation hrLe
  have hx :=
    Z.zeroBackwardValue_eq_endpoint_add_two_mul_halfGap hrLe
  rw [hx] at hEq
  have hC := B.zeroSuffix_threePow_lt_twoPow hrPos hrLe
  have hsplit :
      3 ^ r +
          (2 ^ B.zeroSuffixExponent r - 3 ^ r) =
        2 ^ B.zeroSuffixExponent r :=
    Nat.add_sub_of_le (Nat.le_of_lt hC)
  have hsplitT :=
    congrArg
      (fun z : ℕ => z * Word.canonicalEnd u)
      hsplit
  have hcore :
      (2 ^ B.zeroSuffixExponent r - 3 ^ r) *
          Word.canonicalEnd u =
        B.zeroSuffixAffine r +
          2 * 3 ^ r * Z.zeroHalfGap r := by
    ring_nf at hEq hsplitT ⊢
    nlinarith
  unfold Word.contractingGap
  rw [B.zeroSuffix_oddSteps hrLe]
  simpa [E2BranchData.zeroSuffixExponent] using hcore

/-- endpoint floor `h_r>=1` を入れた pointwise suffix lower。 -/
theorem zeroSuffix_endpointFloorLower
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    {B : E2BranchData v boundary n d u}
    (Z : E2ZeroSurvivorData B)
    {r : ℕ}
    (hrPos : 0 < r)
    (hrLe : r ≤ u.length) :
    Word.affineConst (B.zeroSuffixWord r) +
        2 * 3 ^ Word.oddSteps (B.zeroSuffixWord r) ≤
      Word.contractingGap (B.zeroSuffixWord r) *
        Word.canonicalEnd u := by
  have hEq :=
    Z.zeroSuffix_gap_mul_endpoint_eq_affine_add_center
      hrPos hrLe
  have hh : 1 ≤ Z.zeroHalfGap r := by
    exact Nat.succ_le_of_lt (Z.zeroHalfGap_pos hrPos hrLe)
  have hmul :
      2 * 3 ^ r ≤ 2 * 3 ^ r * Z.zeroHalfGap r := by
    have h := Nat.mul_le_mul_left (2 * 3 ^ r) hh
    simpa using h
  rw [B.zeroSuffix_oddSteps hrLe]
  calc
    Word.affineConst (B.zeroSuffixWord r) + 2 * 3 ^ r
        ≤ Word.affineConst (B.zeroSuffixWord r) +
            2 * 3 ^ r * Z.zeroHalfGap r :=
      Nat.add_le_add_left hmul _
    _ = Word.contractingGap (B.zeroSuffixWord r) *
          Word.canonicalEnd u := by
      simpa [E2BranchData.zeroSuffixAffine] using hEq.symm

/-- ZERO survivor では全 inner suffix が endpoint-floor budget condition を満たす。 -/
theorem endpointFloorSuffixCondition
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    {B : E2BranchData v boundary n d u}
    (Z : E2ZeroSurvivorData B) :
    Word.EndpointFloorSuffixCondition u (Word.canonicalEnd u) := by
  apply Word.endpointFloorSuffixCondition_of_drop
  intro k hk
  let r := u.length - k
  have hrPos : 0 < r := by
    dsimp [r]
    omega
  have hrLe : r ≤ u.length := by
    dsimp [r]
    omega
  have h := Z.zeroSuffix_endpointFloorLower hrPos hrLe
  have hword : B.zeroSuffixWord r = u.drop k := by
    dsimp [E2BranchData.zeroSuffixWord, r]
    have hidx : u.length - (u.length - k) = k := by
      omega
    rw [hidx]
  rw [hword] at h
  exact h

/-- endpoint-floor-aware weighted suffix budget lower。 -/
def endpointFloorBudgetLower
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    {B : E2BranchData v boundary n d u}
    (_Z : E2ZeroSurvivorData B) : ℕ :=
  Word.endpointFloorBudgetLower u

/-- 新 endpoint-floor lower は `T * suffixGapBudget` 以下。 -/
theorem endpointFloorBudgetLower_le
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    {B : E2BranchData v boundary n d u}
    (Z : E2ZeroSurvivorData B) :
    Z.endpointFloorBudgetLower ≤
      Word.canonicalEnd u * Word.suffixGapBudget u := by
  dsimp [endpointFloorBudgetLower]
  exact
    Word.endpointFloorBudgetLower_le_mul_suffixGapBudget
      Z.endpointFloorSuffixCondition

/--
既存 exponent-floor lower と endpoint-floor lower を同時に保持する combined lower。

`max (T*oldLower) newLower` とすることで、どちらの情報も落とさず
`T * actualBudget` 以下に保つ。
-/
noncomputable def combinedBudgetLower
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    {B : E2BranchData v boundary n d u}
    (Z : E2ZeroSurvivorData B) : ℕ :=
  max
    (Word.canonicalEnd u * B.budgetLower)
    Z.endpointFloorBudgetLower

/-- combined lower も `T * actualBudget` 以下。 -/
theorem combinedBudgetLower_le
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    {B : E2BranchData v boundary n d u}
    (Z : E2ZeroSurvivorData B) :
    Z.combinedBudgetLower ≤
      Word.canonicalEnd u * Word.suffixGapBudget u := by
  dsimp [combinedBudgetLower]
  apply max_le
  · exact Nat.mul_le_mul_left _ B.budgetLower_le_suffixGapBudget
  · exact Z.endpointFloorBudgetLower_le

/--
ZERO survivor が新 endpoint-floor-aware lower も生き残ることを exact に記録する。

これが次の kill target。
-/
theorem combinedBudget_survives
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    {B : E2BranchData v boundary n d u}
    (Z : E2ZeroSurvivorData B) :
    3 * Z.combinedBudgetLower <
      (3 * B.sigma + 5) * 2 ^ Word.twoSteps u *
        Word.canonicalEnd u := by
  have hLower := Z.combinedBudgetLower_le
  have hLower3 :
      3 * Z.combinedBudgetLower ≤
        3 * (Word.canonicalEnd u * Word.suffixGapBudget u) :=
    Nat.mul_le_mul_left 3 hLower
  have hUpper := B.innerReplay_zero_budget_strict_upper
    Z.innerReplay Z.quotient_eq
  have hTpos : 0 < Word.canonicalEnd u := by
    rcases Word.canonicalEnd_odd u with ⟨a, ha⟩
    omega
  have hUpperT :
      3 * Word.suffixGapBudget u * Word.canonicalEnd u <
        (3 * B.sigma + 5) * 2 ^ Word.twoSteps u *
          Word.canonicalEnd u :=
    (Nat.mul_lt_mul_right hTpos).2 hUpper
  have hLower3' :
      3 * Z.combinedBudgetLower ≤
        3 * Word.suffixGapBudget u * Word.canonicalEnd u := by
    calc
      3 * Z.combinedBudgetLower
          ≤ 3 * (Word.canonicalEnd u * Word.suffixGapBudget u) := hLower3
      _ = 3 * Word.suffixGapBudget u * Word.canonicalEnd u := by ring
  exact lt_of_le_of_lt hLower3' hUpperT

/--
最初の backward recurrence を coordinate defect と結合した exact penultimate relation。
`h_m` を full inner half-gap、`h_(m-1)` を一段後の half-gap とすると
`2*h_(m-1) + 2 = 11*h_m + 9*n`。
-/
theorem zero_penultimateHalfGap
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    {B : E2BranchData v boundary n d u}
    (Z : E2ZeroSurvivorData B) :
    2 * Z.zeroHalfGap (u.length - 1) + 2 =
      11 * Z.zeroHalfGap u.length + 9 * n := by
  have hm : 0 < u.length := by
    have h7 := B.seven_le_innerLength
    omega
  have hr : u.length - 1 < u.length := by
    omega
  have hrec :=
    Z.zeroBackwardGapRecurrence
      (r := u.length - 1) (e := 1)
      hr B.firstBackwardWord
  norm_num at hrec
  have hidx :
      u.length - 1 + 1 = u.length := by
    omega
  rw [hidx] at hrec
  have hfull :=
    Z.zeroHalfGap_full_eq_endpointHalfGap
  have hend :=
    Z.endpoint_add_five_eq
  rw [hfull] at hrec ⊢
  nlinarith
end E2ZeroSurvivorData

/-- E2 ZERO survivor を直接排除する最終局所 principle。 -/
def NoE2ZeroSurvivor : Prop :=
  ∀ {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E2BranchData v boundary n d u),
    E2ZeroSurvivorData B → False

/-- `NoE2ZeroSurvivor` があれば任意の inner quotient-zero branch は排除できる。 -/
theorem no_innerReplay_zero_of_noE2ZeroSurvivor
    (hNo : NoE2ZeroSurvivor)
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E2BranchData v boundary n d u)
    (I : E2BranchData.InnerReplayData B)
    (hq : I.coordinate.quotient = 0) :
    False :=
  hNo B (B.zeroSurvivorData I hq)

end EndpointFloorZero
end PositiveReturn
end AdjacentReturn
end Collatz
