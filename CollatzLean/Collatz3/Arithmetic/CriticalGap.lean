import CollatzLean.Collatz3.Critical.Beatty


/-!
# Collatz3: critical 2--3 gap の純整数論 interface

CSTMicro の first coefficient crossing では、endpoint odd count `p` に対する
terminal depth は `criticalTwoDepth p` に一致する。

そこで純粋な 2--3 冪差

  criticalGap(p) = 2^(criticalTwoDepth p) - 3^p

を Collatz path から切り離して定義する。

このファイルでは positivity と exact decomposition は証明するが、

  p < 3 * criticalGap(p)

という universal linear lower bound 自体を未証明 theorem として置かない。
後段が必要とする外部整数論入力は `CriticalGapLinearBound : Prop` として明示する。
-/

namespace Collatz3
namespace Arithmetic

/-- endpoint odd count `p` に対応する critical positive 2--3 gap。 -/
def criticalGap (p : ℕ) : ℕ :=
  2 ^ Critical.criticalTwoDepth p - 3 ^ p

/-- critical depth では `3^p` より `2^H` が strict に大きい。 -/
theorem threePow_lt_twoPow_criticalTwoDepth (p : ℕ) :
    3 ^ p < 2 ^ Critical.criticalTwoDepth p := by
  have hLe := Critical.threePow_le_twoPow_criticalTwoDepth p
  have hDepthPos : 0 < Critical.criticalTwoDepth p := by
    simp [Critical.criticalTwoDepth]
  have hOdd : Odd (3 ^ p) :=
    (show Odd (3 : ℕ) by decide).pow
  have hEven : Even (2 ^ Critical.criticalTwoDepth p) :=
    (show Even (2 : ℕ) by decide).pow_of_ne_zero
      (Nat.ne_of_gt hDepthPos)
  rcases hOdd with ⟨a, ha⟩
  rcases hEven with ⟨b, hb⟩
  omega

/-- critical gap はすべての `p` で正。 -/
@[simp] theorem criticalGap_pos (p : ℕ) :
    0 < criticalGap p := by
  unfold criticalGap
  exact Nat.sub_pos_of_lt (threePow_lt_twoPow_criticalTwoDepth p)

/-- critical upper power の exact gap decomposition。 -/
theorem twoPow_critical_eq_threePow_add_criticalGap (p : ℕ) :
    2 ^ Critical.criticalTwoDepth p =
      3 ^ p + criticalGap p := by
  unfold criticalGap
  have h := threePow_lt_twoPow_criticalTwoDepth p
  omega

@[simp] theorem criticalGap_zero :
    criticalGap 0 = 1 := by
  simp [criticalGap, Critical.criticalTwoDepth]

/--
Stage 1 single-lift に十分な純整数論条件。

これは Prop interface であり、このファイルでは仮定定数や axiom を導入しない。
将来、2--3 exponential gap の certified theorem から導く対象である。
-/
def CriticalGapLinearBound : Prop :=
  ∀ p : ℕ,
    p < 3 * criticalGap p

/--
より強いが自然な形 `p ≤ criticalGap p`。
既知の強い 2--3 gap estimate を接続する場合の便利な interface として置く。
-/
def CriticalGapAtLeastOddCount : Prop :=
  ∀ p : ℕ,
    p ≤ criticalGap p

/-- `criticalGap p ≥ p` があれば Stage 1 に必要な linear bound が従う。 -/
theorem criticalGapLinearBound_of_atLeastOddCount
    (h : CriticalGapAtLeastOddCount) :
    CriticalGapLinearBound := by
  unfold CriticalGapAtLeastOddCount at h
  unfold CriticalGapLinearBound
  intro p
  have hpGap := h p
  have hPos := criticalGap_pos p
  omega

end Arithmetic
end Collatz3
