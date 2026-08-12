import CollatzLean.Collatz.AdjacentReturn.PositiveReturn.EndpointFloorZeroE2InnerReplay
import CollatzLean.Collatz.Word.SuffixExponentBound

/-!
# E2 zero branch の sigma-dependent suffix budget

E2 zero branch の inner word `u` では、二種類の exponent floor が同時に使える。

1. 各 nonempty suffix は contracting。
2. whole `[1,2] ++ u` は terminal contracting で、全 proper prefix は expanding。

`tau(r)` を `3^r < 2^h` となる最小 exponent とする。
末尾 `r` 文字の cumulative exponent `H_r` は

  H_r >= tau(r)

だけでなく

  H_r >= tau(m+2) - tau(m-r+2) + 1

も満たす。

この E2 固有 floor を suffixGapBudget の全 suffix contribution へ入れ、
quotient zero の ZERO equation と衝突する自然数版 kill criterion を構成する。
-/

namespace Collatz
namespace Word

/-- `3^r` を越える2冪は必ず存在する。 -/
private theorem exists_twoExponentAboveThreePow (r : ℕ) :
    ∃ h : ℕ, 3 ^ r < 2 ^ h := by
  refine ⟨2 * r + 1, ?_⟩
  induction r with
  | zero => norm_num
  | succ r ih =>
      have hmul :
          3 ^ r * 3 < 2 ^ (2 * r + 1) * 3 :=
        (Nat.mul_lt_mul_right (by omega : 0 < (3 : ℕ))).2 ih
      have hpowPos : 0 < 2 ^ (2 * r + 1) :=
        Nat.pow_pos (by omega)
      have h34 :
          2 ^ (2 * r + 1) * 3 <
            2 ^ (2 * r + 1) * 4 :=
        (Nat.mul_lt_mul_left hpowPos).2 (by omega)
      calc
        3 ^ (r + 1) = 3 ^ r * 3 := by rw [pow_succ]
        _ < 2 ^ (2 * r + 1) * 3 := hmul
        _ < 2 ^ (2 * r + 1) * 4 := h34
        _ = 2 ^ (2 * (r + 1) + 1) := by
          rw [show 2 * (r + 1) + 1 = (2 * r + 1) + 2 by omega]
          rw [pow_add]
          norm_num [pow_add]

/-- `tau(r)`: `3^r < 2^h` となる最小 exponent。 -/
noncomputable def twoExponentThreshold (r : ℕ) : ℕ :=
  Nat.find (exists_twoExponentAboveThreePow r)

/-- threshold の defining inequality。 -/
theorem twoExponentThreshold_spec (r : ℕ) :
    3 ^ r < 2 ^ twoExponentThreshold r :=
  Nat.find_spec (exists_twoExponentAboveThreePow r)

/-- `3^r < 2^H` なら threshold は H 以下。 -/
theorem twoExponentThreshold_le_of_threePow_lt_twoPow
    {r H : ℕ}
    (h : 3 ^ r < 2 ^ H) :
    twoExponentThreshold r ≤ H := by
  exact Nat.find_min' (exists_twoExponentAboveThreePow r) h

/--
低い exponent floor の contracting gap を高い exponent へ持ち上げても、
actual gap を越えない。
-/
theorem scaled_floorGap_le_gap
    {r h H : ℕ}
    (hcontract : 3 ^ r < 2 ^ h)
    (hle : h ≤ H) :
    2 ^ (H - h) * (2 ^ h - 3 ^ r) ≤
      2 ^ H - 3 ^ r := by
  have hfloorEq :
      3 ^ r + (2 ^ h - 3 ^ r) = 2 ^ h :=
    Nat.add_sub_of_le (Nat.le_of_lt hcontract)
  have hdecomp : h + (H - h) = H :=
    Nat.add_sub_of_le hle
  have hpowOne : 1 ≤ 2 ^ (H - h) := by
    have hp : 0 < 2 ^ (H - h) := Nat.pow_pos (by omega)
    omega
  have hthreeScaled :
      3 ^ r ≤ 2 ^ (H - h) * 3 ^ r := by
    have h := Nat.mul_le_mul_right (3 ^ r) hpowOne
    simpa [Nat.mul_comm] using h
  have hadd :
      2 ^ (H - h) * (2 ^ h - 3 ^ r) + 3 ^ r ≤
        2 ^ H := by
    calc
      2 ^ (H - h) * (2 ^ h - 3 ^ r) + 3 ^ r
          ≤
        2 ^ (H - h) * (2 ^ h - 3 ^ r) +
          2 ^ (H - h) * 3 ^ r :=
        Nat.add_le_add_left hthreeScaled _
      _ =
        2 ^ (H - h) *
          ((2 ^ h - 3 ^ r) + 3 ^ r) := by ring
      _ = 2 ^ (H - h) * 2 ^ h := by rw [Nat.sub_add_cancel (Nat.le_of_lt hcontract)]
      _ = 2 ^ H := by
        rw [← pow_add]
        congr 1
        omega
  have hthreeLe : 3 ^ r ≤ 2 ^ H :=
    le_trans (Nat.le_of_lt hcontract)
      (Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hle)
  have hsubadd :
      (2 ^ H - 3 ^ r) + 3 ^ r = 2 ^ H :=
    Nat.sub_add_cancel hthreeLe
  omega

/--
指定した suffix exponent floor から作る budget lower expression。

各 suffix length r の contribution に

  2^(H_r - floor r) * (2^(floor r) - 3^r)

を入れ、prefix 2冪で元 word の scale へ戻す。
-/
def suffixGapBudgetFloor :
    Collatz.Word → (ℕ → ℕ) → ℕ
  | [], _ => 0
  | e :: w, floor =>
      2 ^
          (Word.twoSteps (e :: w) -
            floor (Word.oddSteps (e :: w))) *
        (2 ^ floor (Word.oddSteps (e :: w)) -
          3 ^ Word.oddSteps (e :: w)) +
      2 ^ e * suffixGapBudgetFloor w floor

@[simp] theorem suffixGapBudgetFloor_nil (floor : ℕ → ℕ) :
    suffixGapBudgetFloor ([] : Collatz.Word) floor = 0 := rfl

@[simp] theorem suffixGapBudgetFloor_cons
    (e : ℕ) (w : Collatz.Word) (floor : ℕ → ℕ) :
    suffixGapBudgetFloor (e :: w) floor =
      2 ^
          (Word.twoSteps (e :: w) -
            floor (Word.oddSteps (e :: w))) *
        (2 ^ floor (Word.oddSteps (e :: w)) -
          3 ^ Word.oddSteps (e :: w)) +
      2 ^ e * suffixGapBudgetFloor w floor := rfl

/--
全 suffix の exponent が `floor` 以上なら、floor budget は actual budget 以下。
-/
theorem suffixGapBudgetFloor_le
    {w : Collatz.Word} {floor : ℕ → ℕ}
    (hFloorContract :
      ∀ r : ℕ,
        0 < r → r ≤ w.length →
          3 ^ r < 2 ^ floor r)
    (hExponentFloor :
      ∀ r : ℕ,
        0 < r → r ≤ w.length →
          floor r ≤
            Word.twoSteps (w.drop (w.length - r))) :
    suffixGapBudgetFloor w floor ≤ Word.suffixGapBudget w := by
  induction w with
  | nil =>
      simp [suffixGapBudgetFloor, Word.suffixGapBudget]
  | cons e w ih =>
      let r : ℕ := (e :: w).length
      have hrPos : 0 < r := by
        dsimp [r]
        simp
      have hrLe : r ≤ (e :: w).length := le_rfl
      have hFloorR := hFloorContract r hrPos hrLe
      have hExpR0 := hExponentFloor r hrPos hrLe
      have hdropR :
          (e :: w).drop ((e :: w).length - r) = e :: w := by
        dsimp [r]
        simp
      have hExpR :
          floor r ≤ Word.twoSteps (e :: w) := by
        rw [hdropR] at hExpR0
        exact hExpR0
      have hWhole :
          2 ^ (Word.twoSteps (e :: w) - floor r) *
              (2 ^ floor r - 3 ^ r) ≤
            2 ^ Word.twoSteps (e :: w) - 3 ^ r :=
        scaled_floorGap_le_gap hFloorR hExpR
      have hFloorTail :
          ∀ q : ℕ,
            0 < q → q ≤ w.length →
              3 ^ q < 2 ^ floor q := by
        intro q hqPos hqLe
        exact hFloorContract q hqPos (by simp; omega)
      have hExpTail :
          ∀ q : ℕ,
            0 < q → q ≤ w.length →
              floor q ≤
                Word.twoSteps (w.drop (w.length - q)) := by
        intro q hqPos hqLe
        have h := hExponentFloor q hqPos (by simp; omega)
        have hidx :
            (e :: w).length - q = (w.length - q) + 1 := by
          simp only [List.length_cons]
          omega
        rw [hidx] at h
        simp only [List.drop_succ_cons] at h
        exact h
      have hTail := ih hFloorTail hExpTail
      change
        2 ^
              (Word.twoSteps (e :: w) -
                floor (Word.oddSteps (e :: w))) *
            (2 ^ floor (Word.oddSteps (e :: w)) -
              3 ^ Word.oddSteps (e :: w)) +
          2 ^ e * suffixGapBudgetFloor w floor ≤
        (2 ^ Word.twoSteps (e :: w) -
            3 ^ Word.oddSteps (e :: w)) +
          2 ^ e * Word.suffixGapBudget w
      have hOdd : Word.oddSteps (e :: w) = r := by
        rfl
      rw [hOdd]
      exact Nat.add_le_add hWhole
        (Nat.mul_le_mul_left (2 ^ e) hTail)

end Word

namespace AdjacentReturn
namespace PositiveReturn
namespace EndpointFloorZero
namespace E2BranchData

/--
E2-specific suffix exponent floor。

suffix contracting 由来の `tau(r)` と、
whole terminal contracting / proper-prefix expanding の差から来る floor の最大。
-/
noncomputable def suffixExponentFloor
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (_B : E2BranchData v boundary n d u)
    (r : ℕ) : ℕ :=
  max
    (Word.twoExponentThreshold r)
    (Word.twoExponentThreshold (u.length + 2) -
      Word.twoExponentThreshold (u.length - r + 2) + 1)

/-- floor 自身は `3^r` を越えるだけの2冪を持つ。 -/
theorem threePow_lt_twoPow_suffixExponentFloor
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E2BranchData v boundary n d u)
    {r : ℕ} :
    3 ^ r < 2 ^ B.suffixExponentFloor r := by
  have hspec := Word.twoExponentThreshold_spec r
  have hle :
      Word.twoExponentThreshold r ≤ B.suffixExponentFloor r := by
    dsimp [suffixExponentFloor]
    exact le_max_left _ _
  have hpow :
      2 ^ Word.twoExponentThreshold r ≤
        2 ^ B.suffixExponentFloor r :=
    Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hle
  exact lt_of_lt_of_le hspec hpow

/--
E2 の末尾 `r` 文字 cumulative exponent は E2-specific floor 以上。
-/
theorem suffixExponentFloor_le
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E2BranchData v boundary n d u)
    {r : ℕ}
    (hrPos : 0 < r)
    (hrLe : r ≤ u.length) :
    B.suffixExponentFloor r ≤
      Word.twoSteps (u.drop (u.length - r)) := by
  let m := u.length
  let k := m - r
  let Hs := Word.twoSteps (u.drop k)
  let Hp := Word.twoSteps (u.take k)
  let H := Word.twoSteps u
  have hAll :=
    B.inner_allSuffixesContracting
  have hSuffixContract :
      3 ^ r < 2 ^ Hs := by
    have h :=
      hAll.lastSuffix_threePow_lt_twoPow hrPos hrLe
    simpa [Hs, k, m] using h
  have hHsPos :
      0 < Hs := by
    have hthreePos :
        0 < 3 ^ r :=
      Nat.pow_pos (by omega)
    by_contra hnot
    have hzero :
        Hs = 0 := by
      omega
    rw [hzero] at hSuffixContract
    simp only [pow_zero] at hSuffixContract
    omega
  have hThresholdSuffix :
      Word.twoExponentThreshold r ≤ Hs :=
    Word.twoExponentThreshold_le_of_threePow_lt_twoPow
      hSuffixContract
  have hkLe :
      k ≤ m := by
    dsimp [k]
    omega
  have hkLt :
      k < m := by
    dsimp [k]
    omega
  have htakeLen :
      (u.take k).length = k := by
    simp [k, m]
  have hsplit :
      H = Hp + Hs := by
    have hdecomp :=
      List.take_append_drop k u
    have htwo :=
      congrArg Word.twoSteps hdecomp
    dsimp [H, Hp, Hs]
    rw [Word.twoSteps_append] at htwo
    simpa using htwo.symm
  have hWholeC :=
    B.packet.paradoxical.firstCrossing.terminalContracting
  rw [B.tail_eq] at hWholeC
  have hWholeNorm :
      3 ^ (m + 2) < 2 ^ (H + 3) := by
    simpa [
      Word.Contracting,
      Word.oddSteps,
      Word.twoSteps,
      m,
      H,
      Nat.add_assoc,
      Nat.add_comm,
      Nat.add_left_comm
    ] using hWholeC
  have hThresholdWhole :
      Word.twoExponentThreshold (m + 2) ≤ H + 3 :=
    Word.twoExponentThreshold_le_of_threePow_lt_twoPow
      hWholeNorm
  have hwholeLen :
      k + 2 < (1 :: v).length := by
    rw [B.tail_eq]
    simp only [List.length_cons]
    dsimp [k, m]
    omega
  have hExp0 :=
    B.packet.paradoxical.firstCrossing.properExpanding
      (k + 2) (by omega) hwholeLen
  rw [B.tail_eq] at hExp0
  have htake :
      (1 :: 2 :: u).take (k + 2) =
        1 :: 2 :: u.take k := by
    rw [show k + 2 = Nat.succ (Nat.succ k) by omega]
    simp
  rw [htake] at hExp0
  have hPrefixNorm :
      2 ^ (Hp + 3) < 3 ^ (k + 2) := by
    simpa [
      Word.Expanding,
      Word.oddSteps,
      Word.twoSteps,
      Hp,
      htakeLen,
      Nat.add_assoc,
      Nat.add_comm,
      Nat.add_left_comm
    ] using hExp0
  have hPrefixThreshold :
      Hp + 3 <
        Word.twoExponentThreshold (k + 2) := by
    by_contra hnot
    have hle :
        Word.twoExponentThreshold (k + 2) ≤
          Hp + 3 := by
      omega
    have hspec :=
      Word.twoExponentThreshold_spec (k + 2)
    have hpow :
        2 ^ Word.twoExponentThreshold (k + 2) ≤
          2 ^ (Hp + 3) :=
      Nat.pow_le_pow_right
        (by omega : 0 < (2 : ℕ)) hle
    omega
  have hThresholdWholeSplit :
      Word.twoExponentThreshold (m + 2) ≤
        Hp + Hs + 3 := by
    calc
      Word.twoExponentThreshold (m + 2)
          ≤ H + 3 := hThresholdWhole
      _ = Hp + Hs + 3 := by
        rw [hsplit]
  have hPrefixThresholdLower :
      Hp + 4 ≤
        Word.twoExponentThreshold (k + 2) := by
    omega
  have hThresholdSum :
      Word.twoExponentThreshold (m + 2) + 1 ≤
        Word.twoExponentThreshold (k + 2) + Hs := by
    omega
  have hCrossK :
      Word.twoExponentThreshold (m + 2) -
          Word.twoExponentThreshold (k + 2) + 1 ≤
        Hs := by
    omega
  have hCross :
      Word.twoExponentThreshold (m + 2) -
          Word.twoExponentThreshold (m - r + 2) + 1 ≤
        Hs := by
    simpa [k] using hCrossK
  dsimp [suffixExponentFloor]
  exact max_le hThresholdSuffix hCross

/-- E2-specific floor を全 suffix へ入れた自然数 lower expression。 -/
noncomputable def budgetLower
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E2BranchData v boundary n d u) : ℕ :=
  Word.suffixGapBudgetFloor u B.suffixExponentFloor

/-- E2-specific budget lower expression は actual suffixGapBudget 以下。 -/
theorem budgetLower_le_suffixGapBudget
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E2BranchData v boundary n d u) :
    B.budgetLower ≤ Word.suffixGapBudget u := by
  apply Word.suffixGapBudgetFloor_le
  · intro r hrPos hrLe
    exact B.threePow_lt_twoPow_suffixExponentFloor
  · intro r hrPos hrLe
    exact B.suffixExponentFloor_le hrPos hrLe

/--
ZERO branch を殺す完全自然数 criterion。

sigma-dependent lower expression が ZERO の許容上限以上なら contradiction。
-/
theorem no_innerReplay_zero_of_budgetLower
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E2BranchData v boundary n d u)
    (I : InnerReplayData B)
    (hq : I.coordinate.quotient = 0)
    (hKill :
      (3 * B.sigma + 5) * 2 ^ Word.twoSteps u ≤
        3 * B.budgetLower) :
    False := by
  have hLower := B.budgetLower_le_suffixGapBudget
  have hUpper := B.innerReplay_zero_budget_strict_upper I hq
  have hLower3 :
      3 * B.budgetLower ≤
        3 * Word.suffixGapBudget u :=
    Nat.mul_le_mul_left 3 hLower
  omega

/--
E2 の inner replay は、effective gap のもとでは

* q=2 は不可能
* q=1 は exponential-polynomial trap
* q=0 は ZERO + sigma-budget criterion

の二残存枝へ圧縮される。
-/
inductive ReducedInnerOutcome
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E2BranchData v boundary n d u)
    (hEffective : External.TwoThreeEffectiveGapInput)
    (hPoly : External.TwoThreeGapPolynomialBound) : Type
  | zero
      (I : InnerReplayData B)
      (quotient_eq : I.coordinate.quotient = 0)
  | one
      (I : InnerReplayData B)
      (quotient_eq : I.coordinate.quotient = 1)
      (trap :
        ∃ K A : ℕ,
          0 < K ∧
          18 * n + 5 < u.length ∧
          4 * 3 ^ u.length < 9 * (n + d) ∧
          3 * (4 * (n + d) - 1) <
            (u.length + 2) *
              (K * (u.length + 3) ^ A + 1))

/-- E2 inner replay の最終 reduction。 -/
noncomputable def reducedInnerOutcome
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E2BranchData v boundary n d u)
    (hEffective : External.TwoThreeEffectiveGapInput)
    (hPoly : External.TwoThreeGapPolynomialBound) :
    ReducedInnerOutcome B hEffective hPoly := by
  classical
  let I := B.innerReplayData
  by_cases h0 : I.coordinate.quotient = 0
  · exact ReducedInnerOutcome.zero I h0
  by_cases h1 : I.coordinate.quotient = 1
  · exact
      ReducedInnerOutcome.one I h1
        (B.innerReplay_one_exponential_polynomial_trap
          hEffective hPoly I h1)
  · have hqLe :
        I.coordinate.quotient ≤ 2 :=
      I.quotient_le_two
    have h2 :
        I.coordinate.quotient = 2 := by
      omega
    exact False.elim
      (B.no_innerReplay_two hEffective I h2)

end E2BranchData
end EndpointFloorZero
end PositiveReturn
end AdjacentReturn
end Collatz
