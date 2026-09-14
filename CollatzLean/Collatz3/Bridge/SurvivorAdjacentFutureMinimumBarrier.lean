import CollatzLean.Collatz3.Bridge.SurvivorAdjacentFutureMinimumNoTripleRise
import CollatzLean.Collatz3.Bridge.SurvivorAdjacentFutureMinimumRigidity
import CollatzLean.Collatz3.Semantics.StandardFutureMinimum

/-!
# Collatz3 Bridge: double-rise barrier と flat recharge

二つの defect `+1` next-future-minimum block が連続した終点 `k` では、
既存 `NoTripleRise` の整数評価を捨てずに

`8 * 3^k ≤ 9 * 2^(beattyIndex k)`

という power barrier として公開する。

この barrier は carry `1` の Beatty addition を通る限り保存される。
一方、defect を再び `+1` する transition の開始点では逆向きの

`4 * 2^(beattyIndex a) < 3 * 3^a`

が必要であり、二つは両立しない。

従って標準 future-minimum 列で `+1,+1` の後に再び `+1` が起きるなら、
その前に少なくとも一度 carry `0` を通らなければならない。
defect がその区間で非減少なら、その carry `0` transition は exact に `(0,0)` である。

さらに double-rise endpoint から出る任意の carry `1` 長 `r` は

`16 * 2^(beattyIndex r) < 9 * 3^r`

という near-resonance 条件を満たす。

新しい primitive state / packet は導入しない。
-/

namespace Collatz3
namespace OddOrbit

open Bridge

/--
二つの defect `+1` next blocks が連続した終点 `k` に残る sharp power barrier。

既存 `NoTripleRise` の proof 内部で使っていた積の評価を独立 theorem として公開する。
-/
theorem double_nextFutureMinimum_defect_succ_powerBarrier
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {i j k : ℕ}
    (hStart : O.FutureMinimumAt i)
    (hIJ : O.NextFutureMinimum i j)
    (hJK : O.NextFutureMinimum j k)
    (hRiseIJ :
      infiniteSurvivorDefect O.exponent j =
        infiniteSurvivorDefect O.exponent i + 1)
    (hRiseJK :
      infiniteSurvivorDefect O.exponent k =
        infiniteSurvivorDefect O.exponent j + 1) :
    8 * 3 ^ k ≤ 9 * 2 ^ Critical.beattyIndex k := by
  let a : ℕ := j - i
  let b : ℕ := k - j
  have hJIndex : i + a = j := by
    dsimp [a]
    exact Nat.add_sub_of_le (Nat.le_of_lt hIJ.1)
  have hKIndex : j + b = k := by
    dsimp [b]
    exact Nat.add_sub_of_le (Nat.le_of_lt hJK.1)
  have hKIndex' : i + a + b = k := by omega
  have hBoundA :
      2 * 3 ^ a ≤ 3 * 2 ^ Critical.beattyIndex a := by
    simpa [a] using
      O.nextFutureMinimum_defect_succ_length_power_bound
        S hStart hIJ hRiseIJ
  have hMinJ : O.FutureMinimumAt j := hIJ.futureMinimumAt
  have hBoundB :
      2 * 3 ^ b ≤ 3 * 2 ^ Critical.beattyIndex b := by
    simpa [b] using
      O.nextFutureMinimum_defect_succ_length_power_bound
        S hMinJ hJK hRiseJK
  have hCarryA : Critical.beattyCarry i a = 1 := by
    have h := (O.nextFutureMinimum_defect_eq_succ_iff S hIJ).1 hRiseIJ
    simpa [a] using h.1
  have hCarryB : Critical.beattyCarry j b = 1 := by
    have h := (O.nextFutureMinimum_defect_eq_succ_iff S hJK).1 hRiseJK
    simpa [b] using h.1
  have hAddA := Critical.beattyIndex_add_eq i a
  rw [hJIndex, hCarryA] at hAddA
  have hAddB := Critical.beattyIndex_add_eq j b
  rw [hKIndex, hCarryB] at hAddB
  have hBk :
      Critical.beattyIndex k =
        Critical.beattyIndex i +
          Critical.beattyIndex a + Critical.beattyIndex b + 2 := by
    omega
  have hUpperI := Critical.beattyIndex_upper i
  have hAB := Nat.mul_le_mul hBoundA hBoundB
  have hAll := Nat.mul_le_mul hUpperI hAB
  have hBase :
      4 * 3 ^ k ≤
        9 * 2 ^
          (Critical.beattyIndex i +
            Critical.beattyIndex a + Critical.beattyIndex b + 1) := by
    calc
      4 * 3 ^ k =
          3 ^ i * ((2 * 3 ^ a) * (2 * 3 ^ b)) := by
        rw [← hKIndex']
        rw [pow_add, pow_add]
        ring
      _ ≤
          2 ^ (Critical.beattyIndex i + 1) *
            ((3 * 2 ^ Critical.beattyIndex a) *
              (3 * 2 ^ Critical.beattyIndex b)) := hAll
      _ =
          9 * 2 ^
            (Critical.beattyIndex i +
              Critical.beattyIndex a + Critical.beattyIndex b + 1) := by
        rw [show
          Critical.beattyIndex i +
              Critical.beattyIndex a + Critical.beattyIndex b + 1 =
            (Critical.beattyIndex i + 1) +
              Critical.beattyIndex a + Critical.beattyIndex b by omega]
        rw [pow_add, pow_add]
        ring
  have hTwice := Nat.mul_le_mul_left 2 hBase
  calc
    8 * 3 ^ k = 2 * (4 * 3 ^ k) := by ring
    _ ≤
        2 *
          (9 * 2 ^
            (Critical.beattyIndex i +
              Critical.beattyIndex a + Critical.beattyIndex b + 1)) :=
      hTwice
    _ = 9 * 2 ^ Critical.beattyIndex k := by
      rw [hBk]
      rw [show
        Critical.beattyIndex i + Critical.beattyIndex a +
              Critical.beattyIndex b + 2 =
          (Critical.beattyIndex i + Critical.beattyIndex a +
              Critical.beattyIndex b + 1) + 1 by omega]
      rw [pow_succ]
      ring

/--
power barrier は carry `1` の Beatty addition を通る限り保存される。

`3^r ≤ 2^(B_r+1)` と
`B_(a+r)=B_a+B_r+1` を掛け合わせるだけの純整数 cocycle。
-/
theorem powerBarrier_add_of_beattyCarry_eq_one
    {a r : ℕ}
    (hBarrier :
      8 * 3 ^ a ≤ 9 * 2 ^ Critical.beattyIndex a)
    (hCarry : Critical.beattyCarry a r = 1) :
    8 * 3 ^ (a + r) ≤
      9 * 2 ^ Critical.beattyIndex (a + r) := by
  have hUpperR := Critical.beattyIndex_upper r
  have hMul := Nat.mul_le_mul hBarrier hUpperR
  have hAdd := Critical.beattyIndex_add_eq a r
  rw [hCarry] at hAdd
  calc
    8 * 3 ^ (a + r) =
        (8 * 3 ^ a) * 3 ^ r := by
      rw [pow_add]
      ring
    _ ≤
        (9 * 2 ^ Critical.beattyIndex a) *
          2 ^ (Critical.beattyIndex r + 1) := hMul
    _ = 9 * 2 ^ Critical.beattyIndex (a + r) := by
      rw [hAdd]
      rw [show
        Critical.beattyIndex a + Critical.beattyIndex r + 1 =
          Critical.beattyIndex a + (Critical.beattyIndex r + 1) by omega]
      rw [pow_add]
      ring

/--
future minimum から defect を `+1` する transition の開始点は、
double-rise barrier と逆向きの power inequality を満たす。

`r=b-a` とすると rise block 自身の
`2*3^r ≤ 3*2^B_r`、carry `1`、endpoint の strict Beatty lower bound を組み合わせる。
-/
theorem nextFutureMinimum_defect_succ_start_oppositePowerBarrier
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {a b : ℕ}
    (hStart : O.FutureMinimumAt a)
    (hNext : O.NextFutureMinimum a b)
    (hRise :
      infiniteSurvivorDefect O.exponent b =
        infiniteSurvivorDefect O.exponent a + 1) :
    4 * 2 ^ Critical.beattyIndex a < 3 * 3 ^ a := by
  let r : ℕ := b - a
  have hrPos : 0 < r := by
    dsimp [r]
    exact Nat.sub_pos_of_lt hNext.1
  have hBIndex : a + r = b := by
    dsimp [r]
    exact Nat.add_sub_of_le (Nat.le_of_lt hNext.1)
  have hCarry : Critical.beattyCarry a r = 1 := by
    have h := (O.nextFutureMinimum_defect_eq_succ_iff S hNext).1 hRise
    simpa [r] using h.1
  have hBlock :
      2 * 3 ^ r ≤ 3 * 2 ^ Critical.beattyIndex r := by
    simpa [r] using
      O.nextFutureMinimum_defect_succ_length_power_bound
        S hStart hNext hRise
  have hAdd := Critical.beattyIndex_add_eq a r
  rw [hBIndex, hCarry] at hAdd
  have hbPos : 0 < b := by omega
  have hStrictB := Critical.beattyIndex_lower_strict hbPos
  have hScaled :=
    Nat.mul_le_mul_left (2 * 2 ^ Critical.beattyIndex a) hBlock
  have hLower :
      4 * 2 ^ Critical.beattyIndex a * 3 ^ r ≤
        3 * 2 ^ Critical.beattyIndex b := by
    calc
      4 * 2 ^ Critical.beattyIndex a * 3 ^ r =
          (2 * 2 ^ Critical.beattyIndex a) * (2 * 3 ^ r) := by ring
      _ ≤
          (2 * 2 ^ Critical.beattyIndex a) *
            (3 * 2 ^ Critical.beattyIndex r) := hScaled
      _ = 3 * 2 ^ Critical.beattyIndex b := by
        rw [hAdd]
        rw [show
          Critical.beattyIndex a + Critical.beattyIndex r + 1 =
            (Critical.beattyIndex a + Critical.beattyIndex r) + 1 by omega]
        rw [pow_succ, pow_add]
        ring
  have hUpper :
      3 * 2 ^ Critical.beattyIndex b < 3 * 3 ^ b :=
    (Nat.mul_lt_mul_left (by omega : 0 < (3 : ℕ))).2 hStrictB
  have hProd :
      3 ^ r * (4 * 2 ^ Critical.beattyIndex a) <
        3 ^ r * (3 * 3 ^ a) := by
    calc
      3 ^ r * (4 * 2 ^ Critical.beattyIndex a) =
          4 * 2 ^ Critical.beattyIndex a * 3 ^ r := by ring
      _ ≤ 3 * 2 ^ Critical.beattyIndex b := hLower
      _ < 3 * 3 ^ b := hUpper
      _ = 3 ^ r * (3 * 3 ^ a) := by
        rw [← hBIndex, pow_add]
        ring
  exact
    (Nat.mul_lt_mul_left (Nat.pow_pos (by decide : 0 < (3 : ℕ)))).mp hProd

/--
標準 future-minimum 列の有限区間で、各 transition の carry が `1` なら
開始点の power barrier は終点まで伝播する。
-/
theorem FutureMinima.powerBarrier_of_carry_one_interval
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    {n m : ℕ}
    (hnm : n ≤ m)
    (hBarrier :
      8 * 3 ^ F.index n ≤
        9 * 2 ^ Critical.beattyIndex (F.index n))
    (hCarry :
      ∀ t : ℕ,
        n ≤ t →
        t < m →
        Critical.beattyCarry
          (F.index t)
          (F.index (t + 1) - F.index t) = 1) :
    8 * 3 ^ F.index m ≤
      9 * 2 ^ Critical.beattyIndex (F.index m) := by
  induction m, hnm using Nat.le_induction with
  | base =>
      exact hBarrier
  | succ m hnm ih =>
      have hCarryPrev :
          ∀ t : ℕ,
            n ≤ t →
            t < m →
            Critical.beattyCarry
              (F.index t)
              (F.index (t + 1) - F.index t) = 1 := by
        intro t hnt htm
        exact hCarry t hnt (Nat.lt_trans htm (Nat.lt_succ_self m))
      have hBarrierM :
          8 * 3 ^ F.index m ≤
            9 * 2 ^ Critical.beattyIndex (F.index m) :=
        ih hCarryPrev
      have hCarryM :=
        hCarry m hnm (Nat.lt_succ_self m)
      have hProp :=
        powerBarrier_add_of_beattyCarry_eq_one
          (a := F.index m)
          (r := F.index (m + 1) - F.index m)
          hBarrierM hCarryM
      have hIndex :
          F.index m + (F.index (m + 1) - F.index m) =
            F.index (m + 1) := by
        exact Nat.add_sub_of_le
          (Nat.le_of_lt
            (F.index_strict (Nat.lt_succ_self m)))
      simpa [hIndex] using hProp

/--
標準 future-minimum 列で `+1,+1` の後に後続の `+1` が再び起きるなら、
その前に carry `0` transition が少なくとも一つ必要。

carry `1` だけなら double-rise barrier が後続 rise の開始点まで保存され、
rise-start opposite barrier と矛盾する。
-/
theorem FutureMinima.exists_carry_zero_before_later_rise_of_double_rise
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (S : O.IsInfiniteCoefficientSurvivor)
    (hStandard : F.IsStandard)
    {n m : ℕ}
    (hnm : n + 2 ≤ m)
    (hRiseN :
      infiniteSurvivorDefect O.exponent (F.index (n + 1)) =
        infiniteSurvivorDefect O.exponent (F.index n) + 1)
    (hRiseN1 :
      infiniteSurvivorDefect O.exponent (F.index (n + 2)) =
        infiniteSurvivorDefect O.exponent (F.index (n + 1)) + 1)
    (hRiseM :
      infiniteSurvivorDefect O.exponent (F.index (m + 1)) =
        infiniteSurvivorDefect O.exponent (F.index m) + 1) :
    ∃ t : ℕ,
      n + 2 ≤ t ∧
      t < m ∧
      Critical.beattyCarry
        (F.index t)
        (F.index (t + 1) - F.index t) = 0 := by
  have hNext :
      ∀ q : ℕ,
        O.NextFutureMinimum (F.index q) (F.index (q + 1)) :=
    (F.isStandard_iff_nextFutureMinimum).1 hStandard
  have hBarrier :=
    O.double_nextFutureMinimum_defect_succ_powerBarrier
      S (F.minimum n) (hNext n) (hNext (n + 1)) hRiseN hRiseN1
  by_contra hNo
  have hAllOne :
      ∀ t : ℕ,
        n + 2 ≤ t →
        t < m →
        Critical.beattyCarry
          (F.index t)
          (F.index (t + 1) - F.index t) = 1 := by
    intro t ht0 htm
    rcases Critical.beattyCarry_eq_zero_or_one
        (F.index t) (F.index (t + 1) - F.index t) with hZero | hOne
    · exfalso
      apply hNo
      exact ⟨t, ht0, htm, hZero⟩
    · exact hOne
  have hBarrierM :=
    F.powerBarrier_of_carry_one_interval
      hnm hBarrier hAllOne
  have hOpposite :=
    O.nextFutureMinimum_defect_succ_start_oppositePowerBarrier
      S (F.minimum m) (hNext m) hRiseM
  have hLeft := Nat.mul_le_mul_left 4 hBarrierM
  have hRight := (Nat.mul_lt_mul_left (by omega : 0 < (9 : ℕ))).2 hOpposite
  omega

/--
さらに double rise と後続 rise の間で defect が非減少なら、
上の carry `0` witness は exact `(carry, excess)=(0,0)` になる。

defect balance
`δ_next + excess = δ_start + carry`
に carry `0` と非減少を入れるだけで excess `0` と defect equality が従う。
-/
theorem FutureMinima.exists_zero_zero_before_later_rise_of_double_rise_of_nondec
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (S : O.IsInfiniteCoefficientSurvivor)
    (hStandard : F.IsStandard)
    {n m : ℕ}
    (hnm : n + 2 ≤ m)
    (hRiseN :
      infiniteSurvivorDefect O.exponent (F.index (n + 1)) =
        infiniteSurvivorDefect O.exponent (F.index n) + 1)
    (hRiseN1 :
      infiniteSurvivorDefect O.exponent (F.index (n + 2)) =
        infiniteSurvivorDefect O.exponent (F.index (n + 1)) + 1)
    (hRiseM :
      infiniteSurvivorDefect O.exponent (F.index (m + 1)) =
        infiniteSurvivorDefect O.exponent (F.index m) + 1)
    (hNondec :
      ∀ t : ℕ,
        n + 2 ≤ t →
        t < m →
        infiniteSurvivorDefect O.exponent (F.index t) ≤
          infiniteSurvivorDefect O.exponent (F.index (t + 1))) :
    ∃ t : ℕ,
      n + 2 ≤ t ∧
      t < m ∧
      Critical.beattyCarry
          (F.index t)
          (F.index (t + 1) - F.index t) = 0 ∧
      O.segmentBeattyExcess
          (F.index t)
          (F.index (t + 1) - F.index t) = 0 ∧
      infiniteSurvivorDefect O.exponent (F.index (t + 1)) =
        infiniteSurvivorDefect O.exponent (F.index t) := by
  rcases
      F.exists_carry_zero_before_later_rise_of_double_rise
        S hStandard hnm hRiseN hRiseN1 hRiseM with
    ⟨t, ht0, htm, hCarry⟩
  have hNext :
      O.NextFutureMinimum (F.index t) (F.index (t + 1)) :=
    ((F.isStandard_iff_nextFutureMinimum).1 hStandard) t
  have hBalance := O.nextFutureMinimum_defect_balance S hNext
  have hNd := hNondec t ht0 htm
  refine ⟨t, ht0, htm, hCarry, ?_, ?_⟩ <;> omega

/--
double-rise endpoint `k` から長さ `r` の carry `1` addition が出るなら、
その長さは pure Beatty power の near-resonance

`16 * 2^B_r < 9 * 3^r`

を満たす。

future-minimum / excess はこの結論自体には不要で、double-rise barrier と carry `1` だけが本質。
-/
theorem double_nextFutureMinimum_defect_succ_carry_one_length_nearResonant
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {i j k r : ℕ}
    (hStart : O.FutureMinimumAt i)
    (hIJ : O.NextFutureMinimum i j)
    (hJK : O.NextFutureMinimum j k)
    (hRiseIJ :
      infiniteSurvivorDefect O.exponent j =
        infiniteSurvivorDefect O.exponent i + 1)
    (hRiseJK :
      infiniteSurvivorDefect O.exponent k =
        infiniteSurvivorDefect O.exponent j + 1)
    (hCarry : Critical.beattyCarry k r = 1) :
    16 * 2 ^ Critical.beattyIndex r < 9 * 3 ^ r := by
  have hBarrier :=
    O.double_nextFutureMinimum_defect_succ_powerBarrier
      S hStart hIJ hJK hRiseIJ hRiseJK
  have hAdd := Critical.beattyIndex_add_eq k r
  rw [hCarry] at hAdd
  have hjk : j < k := hJK.1
  have hkPos : 0 < k := by
    omega
  have hkrPos : 0 < k + r := by omega
  have hStrict := Critical.beattyIndex_lower_strict hkrPos
  have hLower :
      3 ^ k * (16 * 2 ^ Critical.beattyIndex r) ≤
        9 * 2 ^ Critical.beattyIndex (k + r) := by
    calc
      3 ^ k * (16 * 2 ^ Critical.beattyIndex r) =
          (8 * 3 ^ k) * (2 * 2 ^ Critical.beattyIndex r) := by ring
      _ ≤
          (9 * 2 ^ Critical.beattyIndex k) *
            (2 * 2 ^ Critical.beattyIndex r) :=
        Nat.mul_le_mul_right _ hBarrier
      _ = 9 * 2 ^ Critical.beattyIndex (k + r) := by
        rw [hAdd]
        rw [show
          Critical.beattyIndex k + Critical.beattyIndex r + 1 =
            (Critical.beattyIndex k + Critical.beattyIndex r) + 1 by omega]
        rw [pow_succ, pow_add]
        ring
  have hUpper :
      9 * 2 ^ Critical.beattyIndex (k + r) <
        3 ^ k * (9 * 3 ^ r) := by
    calc
      9 * 2 ^ Critical.beattyIndex (k + r) <
          9 * 3 ^ (k + r) := (Nat.mul_lt_mul_left (by omega : 0 < (9 : ℕ))).2 hStrict
      _ = 3 ^ k * (9 * 3 ^ r) := by
        rw [pow_add]
        ring
  have hProd := lt_of_le_of_lt hLower hUpper
  exact
    (Nat.mul_lt_mul_left (Nat.pow_pos (by decide : 0 < (3 : ℕ)))).mp hProd

end OddOrbit
end Collatz3
