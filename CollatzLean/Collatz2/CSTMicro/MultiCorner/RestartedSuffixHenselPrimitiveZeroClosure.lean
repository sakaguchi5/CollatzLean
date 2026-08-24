import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.TwoThreeCycleDenominator
import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedSuffixHenselZeroCycle

/-!
# Restarted suffix Hensel: primitive zero cycle closure

`gcd(d,e)=1` まで圧縮された actual Beatty zero cycle を分類する。

`d>=2` では cyclic carry ranks が `0,...,d-1` を全て走るため、
rank 0 rotation と rank 1 rotation を取れる。二つの cycle numerator の差は
exact に一項

  3^a * 2^b

だけである。一方、両 numerator は cycle denominator

  D = 3^d - 2^(d+e)

で割れる。`D` は 2 と 3 の双方に coprime なので `D` は unit、positivity から `D=1`。
最後は elementary arithmetic により `d=1` または `d=2`。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

namespace RestartedTerminalStraightPacket

/-- actual suffix chain の occupied qOne は正。 -/
theorem qOne_pos
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (hStart : 0 < P.criticalizationStart)
    {i : ℕ}
    (hi : i < S.width) :
    let C := S.toMonotoneSuffixHenselChain hStart
    0 < C.qOne i := by
  dsimp
  let C := S.toMonotoneSuffixHenselChain hStart
  have hQNonneg := S.suffixHenselQuotient_nonneg hStart hi
  change 0 < S.suffixHenselQuotient hStart i + 1
  omega

/-- primitive rise data から length `d-1` の actual SameDeltaOffsetBlock を復元。 -/
theorem primitiveRise_to_sameDeltaOffsetBlock
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (hStart : 0 < P.criticalizationStart)
    {i d e : ℕ}
    (hd : 0 < d)
    (hRise :
      ∀ r : ℕ, r < d →
        beattyIndex (S.b + i + r + d) =
          beattyIndex (S.b + i + r) + d + e) :
    let C := S.toMonotoneSuffixHenselChain hStart
    C.SameDeltaOffsetBlock i (i + d) (d - 1) e := by
  dsimp
  intro r hr
  have hrLt : r < d := by omega
  have hRel := S.suffixHenselDelta_relative_exact (i + r) d
  have hRiseR := hRise r hrLt
  have hIdx0 : S.b + (i + r) = S.b + i + r := by omega
  have hIdx1 : S.b + (i + r) + d = S.b + i + r + d := by omega
  rw [hIdx0, hRiseR] at hRel
  change
    S.suffixHenselDelta (i + d + r) =
      S.suffixHenselDelta (i + r) + e
  have hDeltaIdx : i + r + d = i + d + r := by omega
  rw [hDeltaIdx] at hRel
  omega

/--
primitive zero cycle の period が `1` なら offset は `0`。

`delta(i+1)` は actual suffix geometry により
`delta i` または `delta i + 1` の二通りしかない。

前者なら scaled state の delta relation から直ちに `e=0`。
後者なら `e=1` だが、quotient scaling

  Q_(i+1) = 2 Q_i

を qOne recurrence

  3 Q_i = 2 Q_(i+1) + 2^(delta_i)

へ代入すると、`Q_i>0` と矛盾する。
-/
private theorem primitiveZeroCycle_offset_eq_zero_of_period_one
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (hStart : 0 < P.criticalizationStart)
    {i e : ℕ}
    (hRoom : i + 1 ≤ S.width)
    (hState :
      let C := S.toMonotoneSuffixHenselChain hStart
      C.ScaledState i (i + 1) e) :
    e = 0 := by
  dsimp at hState
  let C := S.toMonotoneSuffixHenselChain hStart
  change C.ScaledState i (i + 1) e at hState
  have hStateDelta :
      C.delta (i + 1) = C.delta i + e :=
    hState.1
  have hStep :
      C.delta (i + 1) = C.delta i ∨
        C.delta (i + 1) = C.delta i + 1 := by
    change
      S.suffixHenselDelta (i + 1) =
          S.suffixHenselDelta i ∨
        S.suffixHenselDelta (i + 1) =
          S.suffixHenselDelta i + 1
    exact S.suffixHenselDelta_succ_eq_self_or_add_one i
  rcases hStep with hSame | hUp
  · omega
  · have heOne : e = 1 := by
      omega
    have hiS : i < S.width := by
      omega
    have hiC : i < C.width := by
      dsimp [C, toMonotoneSuffixHenselChain]
      exact hiS
    have hRec :=
      C.qOne_recurrence (i := i) hiC
    have hQ :
        C.qOne (i + 1) =
          (2 : ℤ) ^ e * C.qOne i :=
      hState.2
    rw [heOne] at hQ
    norm_num at hQ
    rw [hQ] at hRec
    have hQPos : 0 < C.qOne i := by
      exact S.qOne_pos hStart hiS
    have hPowPos :
        0 < (2 : ℤ) ^ C.delta i := by
      positivity
    nlinarith

/--
cycle equation

  D * Q = 2^a * Phi

があり、`D` と `2` が coprime なら `D ∣ Phi`。

Hensel/Beatty 固有の情報を持たない純粋な divisibility 補題。
-/
private theorem cycleDenominator_dvd_phi
    {D Q Phi : ℤ}
    {a : ℕ}
    (hCop2 : IsCoprime D (2 : ℤ))
    (hEq :
      D * Q = (2 : ℤ) ^ a * Phi) :
    D ∣ Phi := by
  have hDiv :
      D ∣ (2 : ℤ) ^ a * Phi :=
    ⟨Q, hEq.symm⟩
  have hCopPow :
      IsCoprime D ((2 : ℤ) ^ a) :=
    hCop2.pow_right
  exact hCopPow.dvd_of_dvd_mul_left hDiv

/--
整数 `D` が `2` と `3` の両方に coprime であり、

  D ∣ 3^a * 2^b

なら `D` は unit。

後段で carry rank `1` が作る単項式を処理するための純粋算術補題。
-/
private theorem isUnit_of_dvd_twoThreeMonomial
    {D : ℤ}
    {a b : ℕ}
    (hCop2 : IsCoprime D (2 : ℤ))
    (hCop3 : IsCoprime D (3 : ℤ))
    (hDiv :
      D ∣ (3 : ℤ) ^ a * (2 : ℤ) ^ b) :
    IsUnit D := by
  have h3pow :
      IsCoprime D ((3 : ℤ) ^ a) :=
    hCop3.pow_right
  have h2pow :
      IsCoprime D ((2 : ℤ) ^ b) :=
    hCop2.pow_right
  have hCop :
      IsCoprime D
        ((3 : ℤ) ^ a * (2 : ℤ) ^ b) :=
    h3pow.mul_right h2pow
  exact hCop.isUnit_of_dvd hDiv

/--
primitive rise と primitive scaled state を、
rotation に使える zero repeat data へまとめる。

rise から長さ `d-1` の actual delta block を復元し、
scaled state の quotient relation を zero scaled difference に変換する。
-/
private theorem primitiveZeroCycle_zeroRepeatData
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (hStart : 0 < P.criticalizationStart)
    {i d e : ℕ}
    (hd : 0 < d)
    (hState :
      let C := S.toMonotoneSuffixHenselChain hStart
      C.ScaledState i (i + d) e)
    (hRise :
      ∀ r : ℕ, r < d →
        beattyIndex (S.b + i + r + d) =
          beattyIndex (S.b + i + r) + d + e) :
    let C := S.toMonotoneSuffixHenselChain hStart
    C.SameDeltaOffsetBlock i (i + d) (d - 1) e ∧
      C.scaledDifference i (i + d) e 0 = 0 := by
  dsimp at hState ⊢
  let C := S.toMonotoneSuffixHenselChain hStart
  change C.ScaledState i (i + d) e at hState
  have hBlockRaw :=
    S.primitiveRise_to_sameDeltaOffsetBlock
      hStart hd hRise
  dsimp at hBlockRaw
  change
    C.SameDeltaOffsetBlock i (i + d) (d - 1) e
    at hBlockRaw
  have hZero :
      C.scaledDifference i (i + d) e 0 = 0 :=
    (C.scaledDifference_zero_eq_zero_iff
      (i := i) (j := i + d) (Delta := e)).2
      hState.2
  exact ⟨hBlockRaw, hZero⟩

/--
primitive zero repeat を `r < d` だけ rotation する。

`zeroRepeat_rotation_scaledState` が返す endpoint
`i+d+r` を、cycle equation が使いやすい `i+r+d` に正規化して返す。

この補題が width bridge と加法結合順の処理をすべて担当する。
-/
private theorem primitiveZeroCycle_rotation_scaledState
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (hStart : 0 < P.criticalizationStart)
    {i d e r : ℕ}
    (hd : 0 < d)
    (hRoom : i + (2 * d - 1) ≤ S.width)
    (hBlock :
      let C := S.toMonotoneSuffixHenselChain hStart
      C.SameDeltaOffsetBlock i (i + d) (d - 1) e)
    (hZero :
      let C := S.toMonotoneSuffixHenselChain hStart
      C.scaledDifference i (i + d) e 0 = 0)
    (hr : r < d) :
    let C := S.toMonotoneSuffixHenselChain hStart
    C.ScaledState (i + r) (i + r + d) e := by
  have hrLe : r ≤ d - 1 := by
    omega
  have hiEnd :
      i + (d - 1) ≤ S.width := by
    omega
  have hjEnd :
      i + d + (d - 1) ≤ S.width := by
    omega
  have h :=
    S.zeroRepeat_rotation_scaledState
      hStart
      (i := i)
      (p := d)
      (m := d - 1)
      (Delta := e)
      (r := r)
      hiEnd
      hjEnd
      hBlock
      hZero
      hrLe
  dsimp at h ⊢
  simpa [
    Nat.add_assoc,
    Nat.add_comm,
    Nat.add_left_comm
  ] using h

/--
primitive zero cycle の任意の rotation に対する
zero cycle equation を構成する。

rotation の state 構成と endpoint bound は内部で処理する。
-/
private theorem primitiveZeroCycle_rotation_cycleEquation
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (hStart : 0 < P.criticalizationStart)
    {i d e r : ℕ}
    (hd : 0 < d)
    (hRoom : i + (2 * d - 1) ≤ S.width)
    (hBlock :
      let C := S.toMonotoneSuffixHenselChain hStart
      C.SameDeltaOffsetBlock i (i + d) (d - 1) e)
    (hZero :
      let C := S.toMonotoneSuffixHenselChain hStart
      C.scaledDifference i (i + d) e 0 = 0)
    (hr : r < d) :
    let C := S.toMonotoneSuffixHenselChain hStart
    twoThreeCycleDenominator d (d + e) *
        C.qOne (i + r) =
      (2 : ℤ) ^ S.suffixHenselDelta (i + r) *
        beattyCyclePhi (S.b + i + r) d := by
  have hStateR :=
    primitiveZeroCycle_rotation_scaledState
      S hStart hd hRoom hBlock hZero hr
  have hEnd :
      i + r + d ≤ S.width := by
    omega
  have hEq :=
    S.zeroScaledState_cycleEquation
      hStart
      (i := i + r)
      (p := d)
      (Delta := e)
      hEnd
      hStateR
  dsimp at hEq ⊢
  simpa [twoThreeCycleDenominator, Nat.add_assoc] using hEq

/--
rank `0` と rank `1` の二つの cycle numerator をともに `D` が割るなら、
`D` は rank `1` が追加する単一の `2,3` monomial も割る。

これは Hensel state を一切使わない純粋な cyclic-carry arithmetic。
-/
private theorem dvd_twoThreeMonomial_of_rank_zero_one
    {D : ℤ}
    {s0 s1 d : ℕ}
    (hRank0 :
      beattyCyclicCarryRank s0 d = 0)
    (hRank1 :
      beattyCyclicCarryRank s1 d = 1)
    (hDvd0 :
      D ∣ beattyCyclePhi s0 d)
    (hDvd1 :
      D ∣ beattyCyclePhi s1 d) :
    ∃ u : ℕ,
      u < d ∧
      D ∣
        (3 : ℤ) ^ (d - 1 - u) *
          (2 : ℤ) ^ beattyIndex u := by
  have hCarry0 :=
    beattyCycleCarryPhi_eq_zero_of_rank_eq_zero
      hRank0
  have hPhi0 :
      beattyCyclePhi s0 d =
        beattyCycleBasePhi d := by
    rw [
      beattyCyclePhi_eq_base_add_carry,
      hCarry0,
      add_zero
    ]
  rcases
      exists_beattyCycleCarryPhi_eq_single_of_rank_eq_one
        hRank1 with
    ⟨u, hu, hCarry1⟩
  have hPhi1 :
      beattyCyclePhi s1 d =
        beattyCycleBasePhi d +
          (3 : ℤ) ^ (d - 1 - u) *
            (2 : ℤ) ^ beattyIndex u := by
    rw [
      beattyCyclePhi_eq_base_add_carry,
      hCarry1
    ]
  refine ⟨u, hu, ?_⟩
  have hSub :
      D ∣
        beattyCyclePhi s1 d -
          beattyCyclePhi s0 d :=
    dvd_sub hDvd1 hDvd0
  rw [hPhi1, hPhi0] at hSub
  simpa using hSub

/--
period `d ≥ 2` の primitive zero cycle では、
cycle denominator は unit。

cyclic carry rank の全値性から rank `0` と rank `1` の rotation を取り、
各 rotation の cycle equation から `D ∣ Phi` を得る。

二つの numerator の差は一つの `3^a 2^b` monomial なので、
`D` はその monomial を割る。

一方 `D` は `2,3` の両方と coprime だから unit である。
-/
private theorem primitiveZeroCycle_denominator_isUnit_of_two_le
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (hStart : 0 < P.criticalizationStart)
    {i d e : ℕ}
    (hd : 0 < d)
    (hdTwo : 2 ≤ d)
    (hCoprime : d.Coprime e)
    (hRoom : i + (2 * d - 1) ≤ S.width)
    (hBlock :
      let C := S.toMonotoneSuffixHenselChain hStart
      C.SameDeltaOffsetBlock i (i + d) (d - 1) e)
    (hZero :
      let C := S.toMonotoneSuffixHenselChain hStart
      C.scaledDifference i (i + d) e 0 = 0)
    (hRise :
      ∀ r : ℕ, r < d →
        beattyIndex (S.b + i + r + d) =
          beattyIndex (S.b + i + r) + d + e) :
    IsUnit (twoThreeCycleDenominator d (d + e)) := by
  let D : ℤ :=
    twoThreeCycleDenominator d (d + e)
  have hR0 :=
    exists_rotation_of_cyclicCarryRank_eq
      (s := S.b + i)
      (p := d)
      (Delta := e)
      (target := 0)
      hd
      (by omega)
      hCoprime
      hRise
  have hR1 :=
    exists_rotation_of_cyclicCarryRank_eq
      (s := S.b + i)
      (p := d)
      (Delta := e)
      (target := 1)
      hd
      (by omega)
      hCoprime
      hRise
  rcases hR0 with
    ⟨r0, hr0, hRank0⟩
  rcases hR1 with
    ⟨r1, hr1, hRank1⟩
  have hHPos : 0 < d + e := by
    omega
  have hCop2 :
      IsCoprime D (2 : ℤ) := by
    simpa [D] using
      (twoThreeCycleDenominator_isCoprime_two hHPos)
  have hCop3 :
      IsCoprime D (3 : ℤ) := by
    simpa [D] using
      (twoThreeCycleDenominator_isCoprime_three hd)
  have hEq0 :=
    primitiveZeroCycle_rotation_cycleEquation
      S hStart
      hd hRoom hBlock hZero hr0
  have hEq1 :=
    primitiveZeroCycle_rotation_cycleEquation
      S hStart
      hd hRoom hBlock hZero hr1
  dsimp at hEq0 hEq1
  have hDvd0 :
      D ∣ beattyCyclePhi (S.b + i + r0) d := by
    apply cycleDenominator_dvd_phi hCop2
    simpa [D] using hEq0
  have hDvd1 :
      D ∣ beattyCyclePhi (S.b + i + r1) d := by
    apply cycleDenominator_dvd_phi hCop2
    simpa [D] using hEq1
  rcases
      dvd_twoThreeMonomial_of_rank_zero_one
        hRank0 hRank1 hDvd0 hDvd1 with
    ⟨u, hu, hDvdMonomial⟩
  apply
    isUnit_of_dvd_twoThreeMonomial
      hCop2 hCop3
  exact hDvdMonomial

/--
primitive zero cycle の cycle denominator は正。

これは rotation を必要としない。
元の scaled state 自身の cycle equation

  D * Q_i = 2^delta * Phi

を使う。

右辺、`Q_i` はともに正なので `D>0`。
-/
private theorem primitiveZeroCycle_denominator_pos
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (hStart : 0 < P.criticalizationStart)
    {i d e : ℕ}
    (hd : 0 < d)
    (hEnd : i + d ≤ S.width)
    (hState :
      let C := S.toMonotoneSuffixHenselChain hStart
      C.ScaledState i (i + d) e) :
    0 < twoThreeCycleDenominator d (d + e) := by
  dsimp at hState
  let C :=
    S.toMonotoneSuffixHenselChain hStart
  change
    C.ScaledState i (i + d) e
    at hState
  have hEqRaw :=
    S.zeroScaledState_cycleEquation
      hStart
      (i := i)
      (p := d)
      (Delta := e)
      hEnd
      (by
        dsimp
        exact hState)
  dsimp at hEqRaw
  have hEq :
      twoThreeCycleDenominator d (d + e) *
          C.qOne i =
        (2 : ℤ) ^ S.suffixHenselDelta i *
          beattyCyclePhi (S.b + i) d := by
    simpa [
      C,
      twoThreeCycleDenominator,
      Nat.add_assoc
    ] using hEqRaw
  have hi :
      i < S.width := by
    omega
  have hQPos :
      0 < C.qOne i :=
    S.qOne_pos hStart hi
  have hPhiPos :
      0 < beattyCyclePhi (S.b + i) d :=
    beattyCyclePhi_pos _ _ hd
  have hPowPos :
      0 <
        (2 : ℤ) ^
          S.suffixHenselDelta i := by
    positivity
  have hProdPos :
      0 <
        twoThreeCycleDenominator d (d + e) *
          C.qOne i := by
    rw [hEq]
    exact mul_pos hPowPos hPhiPos
  nlinarith

/--
primitive zero cycle の period が少なくとも `2` なら、
その cycle denominator

  D = 3^d - 2^(d+e)

は `1`。

primitive rise/state から zero repeat data を復元する。

cyclic carry rank `0,1` の二つの rotation の差を使うと、
`D` は `2,3` monomial を割るため unit になる。

一方、元の cycle equation 自身から `D>0`。

したがって正の整数 unit である `D` は `1`。
-/
private theorem primitiveZeroCycle_denominator_eq_one_of_two_le
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (hStart : 0 < P.criticalizationStart)
    {i d e : ℕ}
    (hd : 0 < d)
    (hdTwo : 2 ≤ d)
    (hCoprime : d.Coprime e)
    (hRoom : i + (2 * d - 1) ≤ S.width)
    (hState :
      let C := S.toMonotoneSuffixHenselChain hStart
      C.ScaledState i (i + d) e)
    (hRise :
      ∀ r : ℕ, r < d →
        beattyIndex (S.b + i + r + d) =
          beattyIndex (S.b + i + r) + d + e) :
    twoThreeCycleDenominator d (d + e) = 1 := by
  have hData :=
    primitiveZeroCycle_zeroRepeatData
      S hStart hd hState hRise
  rcases hData with
    ⟨hBlock, hZero⟩
  have hUnit :
      IsUnit
        (twoThreeCycleDenominator d (d + e)) :=
    primitiveZeroCycle_denominator_isUnit_of_two_le
      S hStart
      hd hdTwo hCoprime hRoom
      hBlock hZero hRise
  have hEnd :
      i + d ≤ S.width := by
    omega
  have hPos :
      0 <
        twoThreeCycleDenominator d (d + e) :=
    primitiveZeroCycle_denominator_pos
      S hStart
      hd hEnd hState
  exact
    int_eq_one_of_isUnit_of_pos
      hUnit hPos

/--
primitive actual zero cycle の period/offset は

  (d,e) = (1,0)
  または
  (d,e) = (2,1)

の二通りだけ。

`d=1` の場合は actual one-step delta と qOne recurrence により
offset `e=1` を直接排除し、`e=0` を得る。

`d≥2` の場合は cyclic carry rank `0,1` の二つの rotation を比較する。
cycle denominator は両 numerator を割るため single-carry monomial も割るが、
denominator は `2,3` と coprime なので unit になる。
正の unit なので denominator は `1`。

最後に pure arithmetic theorem
`period_offset_cases_of_denominator_eq_one` を適用して
`(1,0)` または `(2,1)` に分類する。
-/
theorem primitiveZeroCycle_period_offset_cases
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (hStart : 0 < P.criticalizationStart)
    {i d e : ℕ}
    (hd : 0 < d)
    (hCoprime : d.Coprime e)
    (hRoom : i + (2 * d - 1) ≤ S.width)
    (hState :
      let C := S.toMonotoneSuffixHenselChain hStart
      C.ScaledState i (i + d) e)
    (hRise :
      ∀ r : ℕ, r < d →
        beattyIndex (S.b + i + r + d) =
          beattyIndex (S.b + i + r) + d + e) :
    (d = 1 ∧ e = 0) ∨
      (d = 2 ∧ e = 1) := by
  by_cases hdOne : d = 1
  · left
    refine ⟨hdOne, ?_⟩
    subst d
    have hRoomOne :
        i + 1 ≤ S.width := by
      simpa using hRoom
    exact
      S.primitiveZeroCycle_offset_eq_zero_of_period_one
        hStart
        hRoomOne
        hState
  · have hdTwo : 2 ≤ d := by
      omega
    have hDone :
        twoThreeCycleDenominator d (d + e) = 1 :=
      S.primitiveZeroCycle_denominator_eq_one_of_two_le
        hStart
        hd
        hdTwo
        hCoprime
        hRoom
        hState
        hRise
    exact
      period_offset_cases_of_denominator_eq_one
        hd hDone

/-- primitive cycle の period だけを取り出した従来形。 -/
theorem primitiveZeroCycle_period_eq_one_or_two
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (hStart : 0 < P.criticalizationStart)
    {i d e : ℕ}
    (hd : 0 < d)
    (hCoprime : d.Coprime e)
    (hRoom : i + (2 * d - 1) ≤ S.width)
    (hState :
      let C := S.toMonotoneSuffixHenselChain hStart
      C.ScaledState i (i + d) e)
    (hRise :
      ∀ r : ℕ, r < d →
        beattyIndex (S.b + i + r + d) =
          beattyIndex (S.b + i + r) + d + e) :
    d = 1 ∨ d = 2 := by
  rcases
      S.primitiveZeroCycle_period_offset_cases
        hStart hd hCoprime hRoom hState hRise with hOne | hTwo
  · exact Or.inl hOne.1
  · exact Or.inr hTwo.1

end RestartedTerminalStraightPacket

end MultiCorner
end CSTMicro
end Collatz2
