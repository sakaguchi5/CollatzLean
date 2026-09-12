import Mathlib.Data.List.Basic

/-!
# Collatz3 CSTMicro: standard parity first-passage path

一般の coefficient stopping time を、standard Collatz step を一歩ずつ数える
binary parity word として表す。

* `true`  : odd step
* `false` : even step
* 横軸     : standard step 数
* 縦軸     : prefix の odd step 数

この層では actual orbit、2-adic residue、Ferrers geometry を導入しない。
first coefficient crossing の純粋な有限 power geometry だけを保持する。
-/

namespace Collatz3
namespace CSTMicro

/-- standard Collatz parity word。`true = odd`, `false = even`。 -/
abbrev ParityWord := List Bool

/-- parity bit を odd-step 増分 `0/1` として読む。 -/
def bitNat : Bool → ℕ
  | false => 0
  | true => 1

@[simp] theorem bitNat_false : bitNat false = 0 := rfl
@[simp] theorem bitNat_true : bitNat true = 1 := rfl

/-- word 全体の odd step 数。 -/
def oddCount (v : ParityWord) : ℕ :=
  (v.map bitNat).sum

/-- 最初の `k` standard steps に含まれる odd step 数。 -/
def prefixOddCount (v : ParityWord) (k : ℕ) : ℕ :=
  oddCount (v.take k)

@[simp] theorem oddCount_nil : oddCount ([] : ParityWord) = 0 := by
  simp [oddCount]

@[simp] theorem oddCount_false_cons (v : ParityWord) :
    oddCount (false :: v) = oddCount v := by
  simp [oddCount]

@[simp] theorem oddCount_true_cons (v : ParityWord) :
    oddCount (true :: v) = oddCount v + 1 := by
  simp [oddCount, Nat.add_comm]

@[simp] theorem prefixOddCount_zero (v : ParityWord) :
    prefixOddCount v 0 = 0 := by
  simp [prefixOddCount]

@[simp] theorem prefixOddCount_cons_succ
    (b : Bool) (v : ParityWord) (j : ℕ) :
    prefixOddCount (b :: v) (j + 1) =
      bitNat b + prefixOddCount v j := by
  simp [prefixOddCount, oddCount]

/-- 任意の prefix の odd count は word 全体の odd count 以下。 -/
theorem prefixOddCount_le_oddCount (v : ParityWord) (k : ℕ) :
    prefixOddCount v k ≤ oddCount v := by
  induction v generalizing k with
  | nil =>
      simp [prefixOddCount, oddCount]
  | cons b v ih =>
      cases k with
      | zero =>
          simp
      | succ k =>
          cases b
          · simpa using ih k
          · have hk := ih k
            simp [prefixOddCount_cons_succ] at hk ⊢
            omega

/-- binary word の odd count は word length 以下。 -/
theorem oddCount_le_length (v : ParityWord) :
    oddCount v ≤ v.length := by
  induction v with
  | nil => simp
  | cons b v ih =>
      cases b <;> simp [oddCount] at * <;> omega

/-- 時刻 `k` で coefficient が 1 より大きい側にある。 -/
def CoefficientExpandingAt
    (v : ParityWord) (k : ℕ) : Prop :=
  2 ^ k < 3 ^ prefixOddCount v k

/-- terminal coefficient が 1 より小さい側にある。 -/
def CoefficientContracting
    (v : ParityWord) : Prop :=
  3 ^ oddCount v < 2 ^ v.length

/--
coefficient が初めて contracting 側へ入る finite standard parity path。

proper positive prefix はすべて expanding、terminal だけが contracting。
これは有限 coefficient stopping time の pure path data に対応する。
-/
structure FirstPassagePath where
  word : ParityWord
  nonempty : word ≠ []
  proper_expanding :
    ∀ k : ℕ, 0 < k → k < word.length →
      CoefficientExpandingAt word k
  terminal_contracting :
    CoefficientContracting word

namespace FirstPassagePath

/-- standard step length。 -/
def length (P : FirstPassagePath) : ℕ :=
  P.word.length

/-- terminal までに現れる odd step 数。 -/
def endpointOddCount (P : FirstPassagePath) : ℕ :=
  oddCount P.word

/-- terminal scale gap `2^H - 3^p`。 -/
def terminalGap (P : FirstPassagePath) : ℕ :=
  2 ^ P.length - 3 ^ P.endpointOddCount

/-- first-passage path の length は正。 -/
theorem length_pos (P : FirstPassagePath) :
    0 < P.length := by
  unfold length
  exact List.length_pos_of_ne_nil P.nonempty

/-- terminal scale gap は正。 -/
theorem terminalGap_pos (P : FirstPassagePath) :
    0 < P.terminalGap := by
  unfold terminalGap length endpointOddCount
  exact Nat.sub_pos_of_lt P.terminal_contracting

/-- terminal power を odd coefficient と positive gap に exact 分解する。 -/
theorem twoPow_eq_threePow_add_terminalGap (P : FirstPassagePath) :
    2 ^ P.length =
      3 ^ P.endpointOddCount + P.terminalGap := by
  unfold terminalGap
  have hle : 3 ^ P.endpointOddCount ≤ 2 ^ P.length :=
    Nat.le_of_lt P.terminal_contracting
  omega

/--
terminal より前の各時刻では、coefficient は expanding 側または境界上にある。
`k=0` は equality、`0<k<length` は strict expanding から従う。
-/
theorem prefix_twoPow_le_threePow
    (P : FirstPassagePath)
    {k : ℕ}
    (hk : k < P.length) :
    2 ^ k ≤ 3 ^ prefixOddCount P.word k := by
  by_cases hk0 : k = 0
  · subst k
    simp
  · exact Nat.le_of_lt
      (P.proper_expanding k (Nat.pos_of_ne_zero hk0) (by simpa [length] using hk))

/-- endpoint odd count は path length 以下。 -/
theorem endpointOddCount_le_length (P : FirstPassagePath) :
    P.endpointOddCount ≤ P.length := by
  simpa [endpointOddCount, length] using oddCount_le_length P.word

end FirstPassagePath
end CSTMicro
end Collatz3
