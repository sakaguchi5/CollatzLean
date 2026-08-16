import CollatzLean.Collatz2.Geometry.PrimitiveReducedChristoffelBridge

/-!
# General CST: binary first-passage micro geometry

一般 coefficient stopping time を standard parity word の有限格子路として持つ。

* 横軸: standard Collatz step 数
* 縦軸: odd step の prefix 個数
* proper prefix: `2^k < 3^m`
* terminal: `3^m < 2^k`

対数を導入せず、irrational boundary `m = k * log_3 2` を
exact な冪不等式で表す。
-/

namespace Collatz2
namespace CSTMicro

/-- standard Collatz parity word。`true = odd`, `false = even`。 -/
abbrev ParityWord := List Bool

/-- parity bit を height increment `0/1` に読む。 -/
def bitNat : Bool → ℕ
  | false => 0
  | true => 1

/-- word 全体の odd step 数。 -/
def oddCount (v : ParityWord) : ℕ :=
  (v.map bitNat).sum

/-- 最初の `k` step に含まれる odd step 数。 -/
def prefixOddCount (v : ParityWord) (k : ℕ) : ℕ :=
  oddCount (v.take k)

/-- coefficient が 1 より大きい側。 -/
def CoefficientExpandingAt (v : ParityWord) (k : ℕ) : Prop :=
  2 ^ k < 3 ^ prefixOddCount v k

/-- terminal coefficient が 1 より小さい側。 -/
def CoefficientContracting (v : ParityWord) : Prop :=
  3 ^ oddCount v < 2 ^ v.length

/--
general CST の first coefficient crossing path。

proper prefix はすべて expanding、
terminal で初めて contracting に入る。
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

/-- path length。 -/
def length (P : FirstPassagePath) : ℕ :=
  P.word.length

/-- endpoint の odd count。 -/
def endpointOddCount (P : FirstPassagePath) : ℕ :=
  oddCount P.word

/-- endpoint contraction gap `2^k - 3^m`。 -/
def terminalGap (P : FirstPassagePath) : ℕ :=
  2 ^ P.length - 3 ^ P.endpointOddCount

theorem length_pos (P : FirstPassagePath) :
    0 < P.length := by
  unfold length
  exact List.length_pos_of_ne_nil P.nonempty

theorem terminalGap_pos (P : FirstPassagePath) :
    0 < P.terminalGap := by
  unfold terminalGap length endpointOddCount
  exact Nat.sub_pos_of_lt P.terminal_contracting

/-- terminal power は odd coefficient と positive gap に exact 分解する。 -/
theorem twoPow_eq_threePow_add_terminalGap (P : FirstPassagePath) :
    2 ^ P.length =
      3 ^ P.endpointOddCount + P.terminalGap := by
  unfold terminalGap
  have h := P.terminal_contracting
  unfold CoefficientContracting at h
  have hle : 3 ^ P.endpointOddCount ≤ 2 ^ P.length := by
    exact le_of_lt h
  calc
    2 ^ P.length
        = (2 ^ P.length - 3 ^ P.endpointOddCount)
            + 3 ^ P.endpointOddCount := (Nat.sub_add_cancel hle).symm
    _ = 3 ^ P.endpointOddCount
          + (2 ^ P.length - 3 ^ P.endpointOddCount) := by
            ac_rfl

/--
irrational Sturmian boundary の exact power 版。

`m` が時刻 `k` の最小 expanding height であることを表す。
-/
def SturmianBoundaryAt (k m : ℕ) : Prop :=
  2 ^ k < 3 ^ m ∧
    ∀ r : ℕ, r < m → ¬ (2 ^ k < 3 ^ r)

/--
path height が Sturmian boundary より `q` 段上にある、
という Ferrers decoration の relational form。
-/
def FerrersDepthAt
    (P : FirstPassagePath)
    (k q : ℕ) : Prop :=
  ∃ m : ℕ,
    SturmianBoundaryAt k m ∧
    prefixOddCount P.word k = m + q

/--
endpoint chord `(length, endpointOddCount)` に対する signed integer rank。

positive なら rational chord の上側。
-/
def rationalRank
    (P : FirstPassagePath)
    (k : ℕ) : ℤ :=
  (P.length * prefixOddCount P.word k : ℕ) -
    (P.endpointOddCount * k : ℕ)

/--
Christoffel / rational-Dyck 側の proper positivity condition。
first-passage power geometry から切り離した pure endpoint geometry として保持する。
-/
def RationalDyckProper (P : FirstPassagePath) : Prop :=
  ∀ k : ℕ, 0 < k → k < P.length →
    0 < P.rationalRank k

end FirstPassagePath
end CSTMicro
end Collatz2
