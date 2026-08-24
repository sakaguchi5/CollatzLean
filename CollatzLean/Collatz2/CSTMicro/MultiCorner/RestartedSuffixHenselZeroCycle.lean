import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.BeattyCyclicCarryArithmetic
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.MonotoneSuffixHenselZeroCycleArithmetic
import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedSuffixHenselNonzeroRepeat

/-!
# Restarted suffix Hensel: zero repeat -> primitive Beatty cycle

large-width で forced repeat の nonzero branch は既に排除済み。
このファイルでは zero scaled-state branch を actual Beatty geometry と結び付ける。

主な内容:

* actual delta の relative formula
* qOne block numerator = `2^delta * beattyCyclePhi`
* zero repeat の各 rotation が同じ cycle equation を持つ
* gcd(p,Delta) による shorter primitive period への一括圧縮

最終的な 12-cell contradiction は次ファイルに分ける。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

namespace RestartedTerminalStraightPacket

/--
actual Hensel delta の relative exact formula。

  r + delta_(i+r)
    = delta_i + (beta(b+i+r)-beta(b+i)).
-/
theorem suffixHenselDelta_relative_exact
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (i r : ℕ) :
    r + S.suffixHenselDelta (i + r) =
      S.suffixHenselDelta i +
        (beattyIndex (S.b + i + r) - beattyIndex (S.b + i)) := by
  have h0 := S.suffixHenselBase_add_delta_eq_beattyIndex i
  have h1 := S.suffixHenselBase_add_delta_eq_beattyIndex (i + r)
  have hBase := S.suffixHenselBase_add i r
  have hIdx : S.b + (i + r) = S.b + i + r := by omega
  rw [hBase, hIdx] at h1
  have hMono : beattyIndex (S.b + i) ≤ beattyIndex (S.b + i + r) := by
    by_cases hr0 : r = 0
    · subst r
      simp
    · exact Nat.le_of_lt (beattyIndex_strictMono (by omega))
  omega

/--
actual qOne block numerator は common dyadic factor の後に pure Beatty cycle numerator を持つ。
-/
theorem qOneBlockNumerator_eq_pow_mul_beattyCyclePhi
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (hStart : 0 < P.criticalizationStart)
    (i n : ℕ) :
    let C := S.toMonotoneSuffixHenselChain hStart
    C.qOneBlockNumerator i n =
      (2 : ℤ) ^ S.suffixHenselDelta i *
        beattyCyclePhi (S.b + i) n := by
  dsimp
  let C := S.toMonotoneSuffixHenselChain hStart
  induction n with
  | zero =>
      simp [MonotoneSuffixHenselChain.qOneBlockNumerator,
        beattyCyclePhi]
  | succ n ih =>
      have hPhi := beattyCyclePhi_succ (S.b + i) n
      have hExp := S.suffixHenselDelta_relative_exact i n
      have hPow :
          (2 : ℤ) ^ n *
              (2 : ℤ) ^ S.suffixHenselDelta (i + n) =
            (2 : ℤ) ^ S.suffixHenselDelta i *
              (2 : ℤ) ^
                (beattyIndex (S.b + i + n) - beattyIndex (S.b + i)) := by
        rw [← pow_add, ← pow_add]
        congr 1
      change
        3 * C.qOneBlockNumerator i n +
            (2 : ℤ) ^ n *
              (2 : ℤ) ^ S.suffixHenselDelta (i + n) =
          (2 : ℤ) ^ S.suffixHenselDelta i *
            beattyCyclePhi (S.b + i) (n + 1)
      rw [ih, hPow, hPhi]
      ring

/--
zero scaled state の period `p` に対する exact cycle equation。
-/
theorem zeroScaledState_cycleEquation
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (hStart : 0 < P.criticalizationStart)
    {i p Delta : ℕ}
    (hEnd : i + p ≤ S.width)
    (hState :
      let C := S.toMonotoneSuffixHenselChain hStart
      C.ScaledState i (i + p) Delta) :
    let C := S.toMonotoneSuffixHenselChain hStart
    ((3 : ℤ) ^ p - (2 : ℤ) ^ (p + Delta)) * C.qOne i =
      (2 : ℤ) ^ S.suffixHenselDelta i *
        beattyCyclePhi (S.b + i) p := by
  dsimp at hState ⊢
  let C := S.toMonotoneSuffixHenselChain hStart
  have hEndC : i + p ≤ C.width := by
    dsimp [C, toMonotoneSuffixHenselChain]
    exact hEnd
  have hIter :=
    C.qOne_iterate (i := i) (n := p) hEndC
  have hNum := S.qOneBlockNumerator_eq_pow_mul_beattyCyclePhi hStart i p
  dsimp [C] at hNum
  have hQ : C.qOne (i + p) = (2 : ℤ) ^ Delta * C.qOne i := hState.2
  rw [hQ, hNum] at hIter
  rw [pow_add]
  ring_nf at hIter ⊢
  linarith

/--
zero repeat の各 rotation `r ≤ m` でも scaled state は zero のまま保たれる。

開始点 `i` と `i+p` の間で

* delta offset が block 全体にわたって一定であり、
* offset `0` の scaled difference が zero

なら、zero scaled difference は repeated block の全 offset に伝播する。
したがって任意の `r ≤ m` について、回転した二点

  i+r,  i+p+r

の間にも同じ offset `Delta` を持つ scaled state が成立する。
-/
theorem zeroRepeat_rotation_scaledState
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (hStart : 0 < P.criticalizationStart)
    {i p m Delta r : ℕ}
    (hiEnd : i + m ≤ S.width)
    (hjEnd : i + p + m ≤ S.width)
    (hBlock :
      let C := S.toMonotoneSuffixHenselChain hStart
      C.SameDeltaOffsetBlock i (i + p) m Delta)
    (hZero :
      let C := S.toMonotoneSuffixHenselChain hStart
      C.scaledDifference i (i + p) Delta 0 = 0)
    (hr : r ≤ m) :
    let C := S.toMonotoneSuffixHenselChain hStart
    C.ScaledState (i + r) (i + p + r) Delta := by
  dsimp only at hBlock hZero ⊢
  let C := S.toMonotoneSuffixHenselChain hStart
  have hiEndC :
      i + m ≤ C.width := by
    dsimp [C, toMonotoneSuffixHenselChain]
    exact hiEnd
  have hjEndC :
      i + p + m ≤ C.width := by
    dsimp [C, toMonotoneSuffixHenselChain]
    exact hjEnd
  change
    C.SameDeltaOffsetBlock i (i + p) m Delta
    at hBlock
  change
    C.scaledDifference i (i + p) Delta 0 = 0
    at hZero
  have hState :=
    C.scaledState_at_of_zero_repeat
      (i := i)
      (j := i + p)
      (m := m)
      (Delta := Delta)
      (r := r)
      hiEndC
      hjEndC
      hBlock
      hZero
      hr
  simpa [Nat.add_assoc] using hState

/--
cyclic carry rank が二つの開始位置で一致するなら、
一周期内の各 offset における Beatty displacement も一致する。

これは

  carry rank equality
    → cyclic carry set equality
    → Beatty displacement equality

という純粋な Beatty 側の橋をまとめた補題。
-/
private theorem beattyDisplacement_of_cyclicCarryRank_eq
    {s p d : ℕ}
    (hRank :
      beattyCyclicCarryRank s p =
        beattyCyclicCarryRank (s + d) p) :
    ∀ r : ℕ, r < p →
      beattyIndex (s + r) - beattyIndex s =
        beattyIndex (s + d + r) - beattyIndex (s + d) := by
  have hSet :=
    beattyCyclicCarrySet_eq_of_rank_eq hRank
  exact beattyDisplacement_eq_of_cyclicCarrySet_eq hSet
/--
正の offset `r` で Beatty displacement が一致するなら、
対応する `suffixHenselDelta` の差も一致する。

各 `suffixHenselDelta` を整数上の Beatty index 表現へ移し、
添字の加法結合を正規化してから displacement equality を消去する。
-/
private theorem suffixHenselDelta_difference_cast_of_beattyDisplacement
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    {i d r : ℕ}
    (hrPos : 0 < r)
    (hDisp :
      beattyIndex (S.b + i + r) -
          beattyIndex (S.b + i) =
        beattyIndex (S.b + i + d + r) -
          beattyIndex (S.b + i + d)) :
    (S.suffixHenselDelta (i + d + r) : ℤ) -
        (S.suffixHenselDelta (i + r) : ℤ) =
      (S.suffixHenselDelta (i + d) : ℤ) -
        (S.suffixHenselDelta i : ℤ) := by
  have hI0 :=
    S.suffixHenselDelta_cast_sub_one i
  have hD0 :=
    S.suffixHenselDelta_cast_sub_one (i + d)
  have hIr :=
    S.suffixHenselDelta_cast_sub_one (i + r)
  have hDr :=
    S.suffixHenselDelta_cast_sub_one (i + d + r)
  have hCast :=
    congrArg (fun n : ℕ => (n : ℤ)) hDisp
  have hMonoI :
      beattyIndex (S.b + i) ≤
        beattyIndex (S.b + i + r) := by
    exact Nat.le_of_lt
      (beattyIndex_strictMono (by omega))
  have hMonoD :
      beattyIndex (S.b + i + d) ≤
        beattyIndex (S.b + i + d + r) := by
    exact Nat.le_of_lt
      (beattyIndex_strictMono (by omega))
  rw [Nat.cast_sub hMonoI, Nat.cast_sub hMonoD] at hCast
  push_cast at hI0 hD0 hIr hDr
  have hBeatty :
      (beattyIndex (S.b + i + d + r) : ℤ) -
          (beattyIndex (S.b + i + r) : ℤ) =
        (beattyIndex (S.b + i + d) : ℤ) -
          (beattyIndex (S.b + i) : ℤ) := by
    linarith [hCast]
  simp only [Nat.add_assoc] at hI0 hD0 hIr hDr hBeatty ⊢
  linarith [hDr, hIr, hD0, hI0, hBeatty]


/--
Beatty displacement equality を、実際の `suffixHenselDelta` の
短周期 relation に戻す。

結論は

  delta(i+d+r)
    = delta(i+r) + (delta(i+d)-delta(i))

である。

`r = 0` は delta の単調性だけで直接従い、
`r > 0` では上の Int-valued displacement 補題を使う。
-/
private theorem suffixHenselDelta_shift_of_beattyDisplacement
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    {i d r : ℕ}
    (hDisp :
      beattyIndex (S.b + i + r) -
          beattyIndex (S.b + i) =
        beattyIndex (S.b + i + d + r) -
          beattyIndex (S.b + i + d)) :
    S.suffixHenselDelta (i + d + r) =
      S.suffixHenselDelta (i + r) +
        (S.suffixHenselDelta (i + d) -
          S.suffixHenselDelta i) := by
  have hMono :
      S.suffixHenselDelta i ≤
        S.suffixHenselDelta (i + d) :=
    S.suffixHenselDelta_mono_of_le (by omega)
  by_cases hr0 : r = 0
  · subst r
    simp only [Nat.add_zero]
    omega
  · have hrPos : 0 < r :=
      Nat.pos_of_ne_zero hr0
    have hInt :=
      suffixHenselDelta_difference_cast_of_beattyDisplacement
        S hrPos hDisp
    have hGoalInt :
        (S.suffixHenselDelta (i + d + r) : ℤ) =
          (S.suffixHenselDelta (i + r) : ℤ) +
            ((S.suffixHenselDelta (i + d) -
              S.suffixHenselDelta i : ℕ) : ℤ) := by
      rw [Nat.cast_sub hMono]
      linarith
    exact_mod_cast hGoalInt


/--
cyclic carry rank equality が与える shorter Beatty displacement period を、
actual restarted suffix の delta period に戻す。

二つの開始位置 `S.b+i` と `S.b+i+d` で period `p` の
cyclic carry rank が一致すると、一周期内の Beatty displacement が一致する。

その displacement equality を
`suffixHenselDelta_cast_sub_one` を通して delta 側へ戻すことで、

  delta(i+d+r) = delta(i+r) + e

を `0 ≤ r ≤ p-d` の全域で得る。

ここで

  e = delta(i+d) - delta(i)

は divisor shift `d` に対応する exact delta offset である。
-/
theorem sameDeltaOffsetBlock_of_cyclicCarryRank_eq
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (hStart : 0 < P.criticalizationStart)
    {i p d : ℕ}
    (hd : 0 < d)
    (hdLt : d < p)
    (hRank :
      beattyCyclicCarryRank (S.b + i) p =
        beattyCyclicCarryRank (S.b + i + d) p) :
    let C := S.toMonotoneSuffixHenselChain hStart
    let e :=
      S.suffixHenselDelta (i + d) -
        S.suffixHenselDelta i
    C.SameDeltaOffsetBlock i (i + d) (p - d) e := by
  dsimp
  let e :=
    S.suffixHenselDelta (i + d) -
      S.suffixHenselDelta i
  have hDisp :=
    beattyDisplacement_of_cyclicCarryRank_eq
      (s := S.b + i)
      (p := p)
      (d := d)
      hRank
  intro r hr
  have hrLt : r < p := by
    omega
  have hShift :=
    suffixHenselDelta_shift_of_beattyDisplacement
      S
      (hDisp r hrLt)
  change
    S.suffixHenselDelta (i + d + r) =
      S.suffixHenselDelta (i + r) + e
  simpa [e] using hShift

/--
delta offset relation

  delta(i+q+r) = delta(i+r) + E

を actual Beatty index の rise

  beta(b+i+r+q) = beta(b+i+r) + q + E

へ戻す。

`suffixHenselBase` が offset `q` だけ exact に増えることと、
`base + delta = Beatty index` を使う。
-/
theorem beattyRise_of_suffixHenselDelta_shift
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    {i q E r : ℕ}
    (hDelta :
      S.suffixHenselDelta (i + q + r) =
        S.suffixHenselDelta (i + r) + E) :
    beattyIndex (S.b + i + r + q) =
      beattyIndex (S.b + i + r) + q + E := by
  have hDelta' :
      S.suffixHenselDelta (i + r + q) =
        S.suffixHenselDelta (i + r) + E := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hDelta
  have h0 :=
    S.suffixHenselBase_add_delta_eq_beattyIndex (i + r)
  have h1 :=
    S.suffixHenselBase_add_delta_eq_beattyIndex (i + r + q)
  have hBase :=
    S.suffixHenselBase_add (i + r) q
  rw [hBase, hDelta'] at h1
  simp only [Nat.add_assoc] at h0 h1 ⊢
  omega


/--
`SameDeltaOffsetBlock` の各 offset を actual Beatty rise に変換する。

後続の gcd descent では delta block と Beatty cyclic carry arithmetic を
何度も往復するため、その境界をこの補題にまとめる。
-/
theorem beattyRise_of_sameDeltaOffsetBlock
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (hStart : 0 < P.criticalizationStart)
    {i q m E r : ℕ}
    (hBlock :
      let C := S.toMonotoneSuffixHenselChain hStart
      C.SameDeltaOffsetBlock i (i + q) m E)
    (hr : r ≤ m) :
    beattyIndex (S.b + i + r + q) =
      beattyIndex (S.b + i + r) + q + E := by
  dsimp at hBlock
  have hDelta := hBlock r hr
  change
    S.suffixHenselDelta (i + q + r) =
      S.suffixHenselDelta (i + r) + E
    at hDelta
  exact S.beattyRise_of_suffixHenselDelta_shift hDelta


/--
zero repeat の offset `0` から outer scaled state を構成する。

delta relation は `SameDeltaOffsetBlock` の offset `0`、
quotient scaling は scaled difference が zero であることから得る。
-/
theorem zeroScaledState_of_zeroRepeat
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (hStart : 0 < P.criticalizationStart)
    {i p m Delta : ℕ}
    (hBlock :
      let C := S.toMonotoneSuffixHenselChain hStart
      C.SameDeltaOffsetBlock i (i + p) m Delta)
    (hZero :
      let C := S.toMonotoneSuffixHenselChain hStart
      C.scaledDifference i (i + p) Delta 0 = 0) :
    let C := S.toMonotoneSuffixHenselChain hStart
    C.ScaledState i (i + p) Delta := by
  dsimp at hBlock hZero ⊢
  let C := S.toMonotoneSuffixHenselChain hStart
  constructor
  · have hDelta := hBlock 0 (by omega)
    simpa using hDelta
  · exact
      (C.scaledDifference_zero_eq_zero_iff
        (i := i) (j := i + p) (Delta := Delta)).1 hZero


/--
`d * Delta = p * e` で、length `p` の Beatty rise が最初の `d` starts で
一定なら、start `s` と `s+d` の cyclic carry rank は一致する。

rank shift formula により rank difference は `p` の倍数になる。
一方、両 cyclic rank はともに `[0,p)` に入るため、
その差として可能な `p` の倍数は `0` だけである。
-/
private theorem beattyCyclicCarryRank_eq_of_factor_shift
    {s p Delta d e : ℕ}
    (hp : 0 < p)
    (hdDelta : d * Delta = p * e)
    (hRise :
      ∀ r : ℕ, r < d →
        beattyIndex (s + r + p) =
          beattyIndex (s + r) + p + Delta) :
    beattyCyclicCarryRank s p =
      beattyCyclicCarryRank (s + d) p := by
  have hShift :=
    beattyCyclicCarryRank_shift_cast
      (s := s) (p := p) (Delta := Delta) (k := d)
      hRise
  have hdDeltaInt :
      (d : ℤ) * (Delta : ℤ) =
        (p : ℤ) * (e : ℤ) := by
    exact_mod_cast hdDelta
  have hMultiple :
      (p : ℤ) ∣
        ((beattyCyclicCarryRank (s + d) p : ℤ) -
          (beattyCyclicCarryRank s p : ℤ)) := by
    refine ⟨
      (d : ℤ) + (e : ℤ) -
        ((beattyIndex (s + d) : ℤ) -
          (beattyIndex s : ℤ)),
      ?_⟩
    calc
      (beattyCyclicCarryRank (s + d) p : ℤ) -
          (beattyCyclicCarryRank s p : ℤ)
          =
        (d : ℤ) * ((p : ℤ) + (Delta : ℤ)) -
          (p : ℤ) *
            ((beattyIndex (s + d) : ℤ) -
              (beattyIndex s : ℤ)) := hShift
      _ =
        (d : ℤ) * (p : ℤ) +
          (d : ℤ) * (Delta : ℤ) -
          (p : ℤ) *
            ((beattyIndex (s + d) : ℤ) -
              (beattyIndex s : ℤ)) := by
          ring
      _ =
        (d : ℤ) * (p : ℤ) +
          (p : ℤ) * (e : ℤ) -
          (p : ℤ) *
            ((beattyIndex (s + d) : ℤ) -
              (beattyIndex s : ℤ)) := by
          rw [hdDeltaInt]
      _ =
        (p : ℤ) *
          ((d : ℤ) + (e : ℤ) -
            ((beattyIndex (s + d) : ℤ) -
              (beattyIndex s : ℤ))) := by
          ring
  rcases hMultiple with ⟨z, hz⟩
  have hR0lt :=
    beattyCyclicCarryRank_lt s p hp
  have hRdlt :=
    beattyCyclicCarryRank_lt (s + d) p hp
  have hpZ : 0 < (p : ℤ) := by
    exact_mod_cast hp
  have hR0lo :
      0 ≤ (beattyCyclicCarryRank s p : ℤ) := by
    positivity
  have hRdlo :
      0 ≤ (beattyCyclicCarryRank (s + d) p : ℤ) := by
    positivity
  have hR0hi :
      (beattyCyclicCarryRank s p : ℤ) < (p : ℤ) := by
    exact_mod_cast hR0lt
  have hRdhi :
      (beattyCyclicCarryRank (s + d) p : ℤ) < (p : ℤ) := by
    exact_mod_cast hRdlt
  have hzZero : z = 0 := by
    by_contra hzNe
    rcases lt_or_gt_of_ne hzNe with hzNeg | hzPos
    · have hzLe : z ≤ -1 := by
        omega
      have hMulLe :
          (p : ℤ) * z ≤ -(p : ℤ) := by
        calc
          (p : ℤ) * z
              ≤ (p : ℤ) * (-1) :=
            mul_le_mul_of_nonneg_left hzLe (le_of_lt hpZ)
          _ = -(p : ℤ) := by ring
      linarith [hz, hMulLe, hRdlo, hR0hi]
    · have hzGe : 1 ≤ z := by
        omega
      have hMulGe :
          (p : ℤ) ≤ (p : ℤ) * z := by
        calc
          (p : ℤ) = (p : ℤ) * 1 := by ring
          _ ≤ (p : ℤ) * z :=
            mul_le_mul_of_nonneg_left hzGe (le_of_lt hpZ)
      linarith [hz, hMulGe, hR0lo, hRdhi]
  rw [hzZero, mul_zero] at hz
  have hEqInt :
      (beattyCyclicCarryRank (s + d) p : ℤ) =
        (beattyCyclicCarryRank s p : ℤ) := by
    linarith
  exact_mod_cast hEqInt.symm


/--
rank shift が zero になり、かつ

  d * Delta = p * e

なら、start を `d` だけ進めた actual Beatty displacement は exact に `d+e`。

この結果と `suffixHenselDelta_relative_exact` を組み合わせることで、
cyclic rank から得た shorter period の actual delta offset が
gcd quotient `e` と一致することを示す。
-/
private theorem suffixHenselDelta_divisorOffset_eq
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    {i p Delta d e : ℕ}
    (hp : 0 < p)
    (hd : 0 < d)
    (hdDelta : d * Delta = p * e)
    (hRise :
      ∀ r : ℕ, r < d →
        beattyIndex (S.b + i + r + p) =
          beattyIndex (S.b + i + r) + p + Delta)
    (hRank :
      beattyCyclicCarryRank (S.b + i) p =
        beattyCyclicCarryRank (S.b + i + d) p) :
    S.suffixHenselDelta (i + d) -
        S.suffixHenselDelta i = e := by
  have hShift :=
    beattyCyclicCarryRank_shift_cast
      (s := S.b + i)
      (p := p)
      (Delta := Delta)
      (k := d)
      hRise
  rw [← hRank] at hShift
  simp only [sub_self] at hShift
  have hdDeltaInt :
      (d : ℤ) * (Delta : ℤ) =
        (p : ℤ) * (e : ℤ) := by
    exact_mod_cast hdDelta
  have hFactor :
      (p : ℤ) *
          ((d : ℤ) + (e : ℤ) -
            ((beattyIndex (S.b + i + d) : ℤ) -
              (beattyIndex (S.b + i) : ℤ))) = 0 := by
    calc
      (p : ℤ) *
          ((d : ℤ) + (e : ℤ) -
            ((beattyIndex (S.b + i + d) : ℤ) -
              (beattyIndex (S.b + i) : ℤ)))
          =
        (d : ℤ) * (p : ℤ) +
          (p : ℤ) * (e : ℤ) -
          (p : ℤ) *
            ((beattyIndex (S.b + i + d) : ℤ) -
              (beattyIndex (S.b + i) : ℤ)) := by
          ring
      _ =
        (d : ℤ) * (p : ℤ) +
          (d : ℤ) * (Delta : ℤ) -
          (p : ℤ) *
            ((beattyIndex (S.b + i + d) : ℤ) -
              (beattyIndex (S.b + i) : ℤ)) := by
          rw [hdDeltaInt]
      _ =
        (d : ℤ) * ((p : ℤ) + (Delta : ℤ)) -
          (p : ℤ) *
            ((beattyIndex (S.b + i + d) : ℤ) -
              (beattyIndex (S.b + i) : ℤ)) := by
          ring
      _ = 0 := hShift.symm
  have hpNe : (p : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hp)
  have hInner :
      (d : ℤ) + (e : ℤ) -
          ((beattyIndex (S.b + i + d) : ℤ) -
            (beattyIndex (S.b + i) : ℤ)) = 0 := by
    rcases mul_eq_zero.mp hFactor with hp0 | h0
    · exact (hpNe hp0).elim
    · exact h0
  have hBeattyInt :
      (beattyIndex (S.b + i + d) : ℤ) -
          (beattyIndex (S.b + i) : ℤ) =
        (d : ℤ) + (e : ℤ) := by
    linarith
  have hBeattyMono :
      beattyIndex (S.b + i) ≤
        beattyIndex (S.b + i + d) := by
    exact Nat.le_of_lt
      (beattyIndex_strictMono (by omega))
  have hBeattyCast :
      ((beattyIndex (S.b + i + d) -
          beattyIndex (S.b + i) : ℕ) : ℤ) =
        ((d + e : ℕ) : ℤ) := by
    rw [Nat.cast_sub hBeattyMono]
    push_cast
    exact hBeattyInt
  have hBeattyNat :
      beattyIndex (S.b + i + d) -
          beattyIndex (S.b + i) =
        d + e := by
    exact_mod_cast hBeattyCast
  have hRelative :=
    S.suffixHenselDelta_relative_exact i d
  rw [hBeattyNat] at hRelative
  omega

/--
zero repeat を `gcd(p, Delta)` で一度に primitive period まで圧縮する。

`g = gcd(p,Delta)` と置き、

  p     = g*d
  Delta = g*e

とする。このとき `d` と `e` は互いに素である。

`g = 1` なら outer cycle 自身がすでに primitive。

`g > 1` なら、

1. outer delta block から period `p/Delta` の Beatty rise を得る。
2. cyclic rank shift formula に `d*Delta = p*e` を入れ、
   start `i` と `i+d` の cyclic rank が一致することを示す。
3. rank equality から shorter delta block を復元する。
4. rank shift formulaをもう一度使って actual shorter offset が
   gcd quotient `e` と一致することを直接示す。
5. repeated divisor cycle の zero descent と divisor-period extension により、
   scaled state と block relation を長さ `m` 全体へ戻す。

これにより `(d,e)` は primitive zero cycle となる。
-/
theorem zeroRepeat_exists_primitiveCycle
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (hStart : 0 < P.criticalizationStart)
    {i p m Delta : ℕ}
    (hp : 0 < p)
    (hpPred : p - 1 ≤ m)
    (hEnd : i + p + m ≤ S.width)
    (hBlock :
      let C := S.toMonotoneSuffixHenselChain hStart
      C.SameDeltaOffsetBlock i (i + p) m Delta)
    (hZero :
      let C := S.toMonotoneSuffixHenselChain hStart
      C.scaledDifference i (i + p) Delta 0 = 0) :
    let C := S.toMonotoneSuffixHenselChain hStart
    ∃ d e : ℕ,
      0 < d ∧
      d ≤ p ∧
      d.Coprime e ∧
      C.ScaledState i (i + d) e ∧
      C.SameDeltaOffsetBlock i (i + d) m e ∧
      (∀ r : ℕ, r < d →
        beattyIndex (S.b + i + r + d) =
          beattyIndex (S.b + i + r) + d + e) := by
  dsimp at hBlock hZero ⊢
  let C := S.toMonotoneSuffixHenselChain hStart
  change
    C.SameDeltaOffsetBlock i (i + p) m Delta
    at hBlock
  change
    C.scaledDifference i (i + p) Delta 0 = 0
    at hZero
  let g := Nat.gcd p Delta
  let d := p / g
  let e := Delta / g
  have hgPos : 0 < g := by
    dsimp [g]
    exact Nat.gcd_pos_of_pos_left Delta hp
  have hgP : g ∣ p := by
    dsimp [g]
    exact Nat.gcd_dvd_left p Delta
  have hgD : g ∣ Delta := by
    dsimp [g]
    exact Nat.gcd_dvd_right p Delta
  have hpEq : p = g * d := by
    dsimp [d]
    exact (Nat.mul_div_cancel' hgP).symm
  have hDeltaEq : Delta = g * e := by
    dsimp [e]
    exact (Nat.mul_div_cancel' hgD).symm
  have hdPos : 0 < d := by
    by_contra hdNot
    have hdZero : d = 0 :=
      Nat.eq_zero_of_not_pos hdNot
    rw [hpEq, hdZero] at hp
    simp at hp
  have hdLe : d ≤ p := by
    rw [hpEq]
    calc
      d = 1 * d := by simp
      _ ≤ g * d :=
        Nat.mul_le_mul_right d (by omega)
  have hCop : d.Coprime e := by
    dsimp [d, e, g]
    exact
      Nat.coprime_div_gcd_div_gcd
        (Nat.gcd_pos_of_pos_left Delta hp)
  have hOuterState :
      C.ScaledState i (i + p) Delta := by
    exact S.zeroScaledState_of_zeroRepeat hStart hBlock hZero
  have hRiseP :
      ∀ r : ℕ, r < p →
        beattyIndex (S.b + i + r + p) =
          beattyIndex (S.b + i + r) + p + Delta := by
    intro r hr
    have hrPred : r ≤ p - 1 := by
      omega
    have hrm : r ≤ m :=
      le_trans hrPred hpPred
    exact
      S.beattyRise_of_sameDeltaOffsetBlock
        hStart hBlock hrm
  have hEndP : i + p ≤ S.width := by
    omega
  have hEndPC : i + p ≤ C.width := by
    dsimp [C, toMonotoneSuffixHenselChain]
    exact hEndP
  have hPrimitive :
      C.ScaledState i (i + d) e ∧
        C.SameDeltaOffsetBlock i (i + d) m e := by
    by_cases hgOne : g = 1
    · have hdEq : d = p := by
        rw [hpEq, hgOne]
        simp
      have heEq : e = Delta := by
        rw [hDeltaEq, hgOne]
        simp
      constructor
      · rw [hdEq, heEq]
        exact hOuterState
      · rw [hdEq, heEq]
        exact hBlock
    · have hgTwo : 2 ≤ g := by
        omega
      have hdLt : d < p := by
        rw [hpEq]
        calc
          d = 1 * d := by simp
          _ < g * d :=
            Nat.mul_lt_mul_of_pos_right
              (by omega : 1 < g) hdPos
      have hdDelta :
          d * Delta = p * e := by
        rw [hpEq, hDeltaEq]
        ring
      have hRiseD :
          ∀ r : ℕ, r < d →
            beattyIndex (S.b + i + r + p) =
              beattyIndex (S.b + i + r) + p + Delta := by
        intro r hr
        exact hRiseP r (lt_trans hr hdLt)
      have hRankEq :
          beattyCyclicCarryRank (S.b + i) p =
            beattyCyclicCarryRank (S.b + i + d) p :=
        beattyCyclicCarryRank_eq_of_factor_shift
          hp hdDelta hRiseD
      have hShortActual :=
        S.sameDeltaOffsetBlock_of_cyclicCarryRank_eq
          hStart hdPos hdLt hRankEq
      change
        C.SameDeltaOffsetBlock
          i (i + d) (p - d)
          (S.suffixHenselDelta (i + d) -
            S.suffixHenselDelta i)
        at hShortActual
      have heActual :
          S.suffixHenselDelta (i + d) -
              S.suffixHenselDelta i =
            e :=
        suffixHenselDelta_divisorOffset_eq
          S hp hdPos hdDelta hRiseD hRankEq
      have hShortBlock :
          C.SameDeltaOffsetBlock
            i (i + d) (p - d) e := by
        rw [← heActual]
        exact hShortActual
      have hShortState :
          C.ScaledState i (i + d) e :=
        C.scaledState_of_repeated_divisor_cycle
          (i := i)
          (p := p)
          (d := d)
          (g := g)
          (Delta := Delta)
          (e := e)
          hgPos
          hpEq
          hDeltaEq
          hEndPC
          hShortBlock
          hOuterState
      have hExtended :
          C.SameDeltaOffsetBlock i (i + d) m e :=
        C.sameDeltaOffsetBlock_extend_divisor
          (i := i)
          (p := p)
          (d := d)
          (g := g)
          (Delta := Delta)
          (e := e)
          (m := m)
          hdPos
          hgPos
          hpEq
          hDeltaEq
          hpPred
          hBlock
          hShortBlock
      exact ⟨hShortState, hExtended⟩
  rcases hPrimitive with
    ⟨hShortState, hExtended⟩
  refine
    ⟨d, e, hdPos, hdLe, hCop,
      hShortState, hExtended, ?_⟩
  intro r hr
  have hrP : r < p := by
    exact lt_of_lt_of_le hr hdLe
  have hrPred : r ≤ p - 1 := by
    omega
  have hrm : r ≤ m :=
    le_trans hrPred hpPred
  exact
    S.beattyRise_of_sameDeltaOffsetBlock
      hStart hExtended hrm



end RestartedTerminalStraightPacket

end MultiCorner
end CSTMicro
end Collatz2
