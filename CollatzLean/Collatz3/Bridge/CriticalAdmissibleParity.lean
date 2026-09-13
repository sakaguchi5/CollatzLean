import CollatzLean.Collatz3.Bridge.CriticalParityCode
import CollatzLean.Collatz3.Bridge.CriticalActualFiber
import CollatzLean.Collatz3.Bridge.CoefficientFirstPassage
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Collatz3 Bridge: critical word と admissible parity code

`Composition H` を binary parity word の run-length code と見なす。
幅 `m` の critical first crossing では

* block 数が `m`、
* total depth が `H_m = criticalTwoDepth m`、
* 各 proper block endpoint は coefficient expansion 側、

という条件だけが必要である。

このファイルでは

`CriticalWord m ≃ AdmissibleParityCode m`

および

`RestrictedCriticalPartition m ≃ AdmissibleParityCode m`

を exact equivalence として閉じる。

さらに total physical depth `n` を先に固定した generic first-crossing code を導入し、
それが「ある order `m` の admissible code」に一意に分解できる形を作る。
-/

namespace Collatz3
namespace Bridge

/-- 幅 `m` の admissible parity composition 条件。 -/
def IsAdmissibleParityCode
    (m : ℕ)
    (c : ParityComposition (Critical.criticalTwoDepth m)) : Prop :=
  c.length = m ∧
    ∀ k : ℕ, k < m →
      c.sizeUpTo k ≤ Critical.beattyIndex k

/-- 幅 `m` の admissible parity code。 -/
abbrev AdmissibleParityCode (m : ℕ) :=
  {c : ParityComposition (Critical.criticalTwoDepth m) //
    IsAdmissibleParityCode m c}

namespace IsAdmissibleParityCode

/-- admissible code の block 数は幅。 -/
theorem length_eq
    {m : ℕ}
    {c : ParityComposition (Critical.criticalTwoDepth m)}
    (h : IsAdmissibleParityCode m c) :
    c.length = m :=
  h.1

/-- proper block endpoint は Beatty roof 以下。 -/
theorem sizeUpTo_le_beatty
    {m : ℕ}
    {c : ParityComposition (Critical.criticalTwoDepth m)}
    (h : IsAdmissibleParityCode m c)
    {k : ℕ}
    (hk : k < m) :
    c.sizeUpTo k ≤ Critical.beattyIndex k :=
  h.2 k hk

end IsAdmissibleParityCode

/-- critical word を admissible composition に読む。 -/
def criticalWordToAdmissibleParityCode
    {m : ℕ}
    (W : Critical.CriticalWord m) :
    AdmissibleParityCode m := by
  let c : ParityComposition (Critical.criticalTwoDepth m) :=
    ⟨W.1,
      by
        intro e he
        exact W.2.valid e he,
      by
        simpa [Word.twoSteps] using W.2.twoSteps_eq⟩
  refine ⟨c, ?_⟩
  constructor
  · exact W.2.oddSteps_eq
  · intro k hk
    change Word.prefixTwoDepth W.1 k ≤ Critical.beattyIndex k
    exact W.2.prefixTwoDepth_le_beatty hk

/-- admissible composition を critical word に戻す。 -/
def admissibleParityCodeToCriticalWord
    {m : ℕ}
    (A : AdmissibleParityCode m) :
    Critical.CriticalWord m := by
  refine ⟨A.1.blocks, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e he
    exact A.1.blocks_pos he
  · simpa [Word.oddSteps] using A.2.length_eq
  · simp only [Word.twoSteps, Critical.criticalTwoDepth_eq, Composition.blocks_sum]
  · intro k hk
    simpa using A.2.sizeUpTo_le_beatty hk

/-- critical word と admissible parity code の exact equivalence。 -/
def criticalWordEquivAdmissibleParityCode
    (m : ℕ) :
    Critical.CriticalWord m ≃ AdmissibleParityCode m where
  toFun := criticalWordToAdmissibleParityCode
  invFun := admissibleParityCodeToCriticalWord
  left_inv W := by
    apply Subtype.ext
    rfl
  right_inv A := by
    apply Subtype.ext
    apply Composition.ext
    rfl

/-- restricted Young partition と admissible parity code の exact equivalence。 -/
def restrictedCriticalPartitionEquivAdmissibleParityCode
    (m : ℕ)
    (hm : 0 < m) :
    RestrictedCriticalPartition m ≃ AdmissibleParityCode m :=
  (criticalWordEquivRestrictedCriticalPartition m hm).symm.trans
    (criticalWordEquivAdmissibleParityCode m)

/-- proper block endpoint の coefficient は expansion 側。 -/
theorem admissibleParityCode_power_prefix
    {m : ℕ}
    (A : AdmissibleParityCode m)
    {k : ℕ}
    (hk : k < m) :
    2 ^ A.1.sizeUpTo k ≤ 3 ^ k := by
  have hDepth := A.2.sizeUpTo_le_beatty hk
  have hPow :
      2 ^ A.1.sizeUpTo k ≤ 2 ^ Critical.beattyIndex k :=
    Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hDepth
  exact le_trans hPow (Critical.beattyIndex_lower k)

/-- 臨界 total two-depth では coefficient が contraction 側へ入る。 -/
theorem criticalTwoDepth_terminal_crosses
    (m : ℕ) :
    3 ^ m < 2 ^ Critical.criticalTwoDepth m := by
  exact Critical.threePow_lt_twoPow_criticalTwoDepth m

/-- 臨界 total two-depth の一つ前までは expansion 側に留まる。 -/
theorem criticalTwoDepth_previous_safe
    (m : ℕ) :
    2 ^ (Critical.criticalTwoDepth m - 1) ≤ 3 ^ m := by
  rw [Critical.criticalTwoDepth_eq]
  simp only [Nat.add_sub_cancel]
  exact Critical.beattyIndex_lower m

/--
physical depth `n` の generic first-crossing parity condition。
block endpoints はすべて expansion 側にあり、terminal の最後の `/2` で初めて
power coefficient が contraction 側へ入る。
-/
def IsFirstCrossingParityComposition
    {n : ℕ}
    (c : ParityComposition n) : Prop :=
  2 ^ (n - 1) ≤ 3 ^ c.length ∧
    3 ^ c.length < 2 ^ n ∧
    ∀ k : ℕ, k < c.length →
      2 ^ c.sizeUpTo k ≤ 3 ^ k

/-- depth `n` の first-crossing parity code。 -/
abbrev FirstCrossingParityCode (n : ℕ) :=
  {c : ParityComposition n // IsFirstCrossingParityComposition c}

namespace IsFirstCrossingParityComposition

/-- first-crossing terminal window は critical depth を一意に決める。 -/
theorem criticalTwoDepth_eq
    {n : ℕ}
    {c : ParityComposition n}
    (h : IsFirstCrossingParityComposition c) :
    n = Critical.criticalTwoDepth c.length := by
  exact
    Critical.criticalTwoDepth_eq_of_powerWindow
      h.1 h.2.1

/-- proper block endpoint から Beatty roof 条件を復元する。 -/
theorem sizeUpTo_le_beatty
    {n : ℕ}
    {c : ParityComposition n}
    (h : IsFirstCrossingParityComposition c)
    {k : ℕ}
    (hk : k < c.length) :
    c.sizeUpTo k ≤ Critical.beattyIndex k := by
  exact
    Critical.prefixDepth_le_beatty_of_powerCoefficient
      (w := c.blocks)
      (k := k)
      (by
        simpa using h.2.2 k hk)

end IsFirstCrossingParityComposition

/--
order `m` と physical depth `n` を両方明示した admissible code。
`n = criticalTwoDepth m` を proof field として持つため、generic depth 分解で cast を避けられる。
-/
def IsAdmissibleParityCodeAtDepth
    (m n : ℕ)
    (c : ParityComposition n) : Prop :=
  c.length = m ∧
    n = Critical.criticalTwoDepth m ∧
    ∀ k : ℕ, k < m →
      c.sizeUpTo k ≤ Critical.beattyIndex k

abbrev AdmissibleParityCodeAtDepth (m n : ℕ) :=
  {c : ParityComposition n // IsAdmissibleParityCodeAtDepth m n c}

/-- generic first crossing から、その一意な order を読む。 -/
def firstCrossingToOrderCode
    {n : ℕ}
    (C : FirstCrossingParityCode n) :
    Σ m : ℕ, AdmissibleParityCodeAtDepth m n := by
  let m := C.1.length
  refine ⟨m, C.1, ?_⟩
  refine ⟨rfl, ?_, ?_⟩
  · exact C.2.criticalTwoDepth_eq
  · intro k hk
    exact C.2.sizeUpTo_le_beatty hk

/-- order付き admissible code は generic first crossing を与える。 -/
def orderCodeToFirstCrossing
    {n : ℕ}
    (C : Σ m : ℕ, AdmissibleParityCodeAtDepth m n) :
    FirstCrossingParityCode n := by
  rcases C with ⟨m, A⟩
  refine ⟨A.1, ?_⟩
  have hDepth : n = Critical.criticalTwoDepth m := A.2.2.1
  constructor
  · have hLen : A.1.length = m := A.2.1
    calc
      2 ^ (n - 1)
          = 2 ^ (Critical.criticalTwoDepth m - 1) := by
              rw [hDepth]
      _ ≤ 3 ^ m := by
              rw [Critical.criticalTwoDepth_eq]
              simp only [Nat.add_sub_cancel]
              exact Critical.beattyIndex_lower m
      _ = 3 ^ A.1.length := by
              rw [hLen]
  · constructor
    · rw [A.2.1, hDepth]
      exact Critical.threePow_lt_twoPow_criticalTwoDepth m
    · intro k hk
      have hkM : k < m := by simpa [A.2.1] using hk
      have hRoof := A.2.2.2 k hkM
      have hPow : 2 ^ A.1.sizeUpTo k ≤ 2 ^ Critical.beattyIndex k :=
        Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hRoof
      exact le_trans hPow (Critical.beattyIndex_lower k)

/--
generic first crossing と「order を付けた admissible code」の exact equivalence。
-/
def firstCrossingParityEquivOrderCode
    (n : ℕ) :
    FirstCrossingParityCode n ≃
      (Σ m : ℕ, AdmissibleParityCodeAtDepth m n) where
  toFun := firstCrossingToOrderCode
  invFun := orderCodeToFirstCrossing
  left_inv C := by
    apply Subtype.ext
    rfl
  right_inv C := by
    rcases C with ⟨m, ⟨c, hc⟩⟩
    rcases hc with ⟨hLen, hDepth, hBound⟩
    subst m
    rfl

/-- fixed critical depth では at-depth code は通常の admissible code と同値。 -/
def admissibleParityCodeEquivAtCriticalDepth
    (m : ℕ) :
    AdmissibleParityCode m ≃
      AdmissibleParityCodeAtDepth m (Critical.criticalTwoDepth m) where
  toFun A :=
    ⟨A.1, A.2.1, rfl, A.2.2⟩
  invFun A :=
    ⟨A.1, A.2.1, A.2.2.2⟩
  left_inv A := by
    apply Subtype.ext
    rfl
  right_inv A := by
    apply Subtype.ext
    rfl

/-- admissible parity code の cardinal は `criticalPartitionCount m = N_m`。 -/
theorem natCard_admissibleParityCode_eq_criticalPartitionCount
    {m : ℕ}
    (hm : 0 < m) :
    Nat.card (AdmissibleParityCode m) = criticalPartitionCount m := by
  unfold criticalPartitionCount
  exact
    Nat.card_congr
      (restrictedCriticalPartitionEquivAdmissibleParityCode m hm).symm

end Bridge
end Collatz3
