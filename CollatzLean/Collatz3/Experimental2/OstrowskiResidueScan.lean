import CollatzLean.Collatz3.Experimental2.OstrowskiCanonicalArithmetic
import Mathlib.Data.Nat.ModEq

/-!
# Collatz3 Experimental2: Ostrowski digit の剰余走査

Ostrowski 表現の低位 suffix だけから `2` 進剰余が決まるとは限らない。
一方、固定した法 `M` に対して digit を一桁ずつ読み、

* 現在 weight `Q n` の剰余、
* 次 weight `Q (n+1)` の剰余、
* これまでの weighted sum の剰余

だけを保持すれば、全 weighted sum modulo `M` は局所更新できる。

このファイルは Collatz 固有の `3x+1` を持ち込まず、
一般の `UnitOstrowskiWeightSystem` に対する有限状態走査だけを置く。
-/

namespace Collatz3
namespace Experimental2

/--
固定法 `modulus` に対する Ostrowski digit 走査の最小状態。

index `n` の直前では

* `qCurr = Q n mod modulus`,
* `qNext = Q (n+1) mod modulus`,
* `sum = Σ_{i<n} d_i Q_i mod modulus`

という意味で使う。
-/
structure OstrowskiResidueState where
  qCurr : ℕ
  qNext : ℕ
  sum : ℕ
  deriving DecidableEq, Repr

/-- index `0` の直前の初期状態。 -/
def initialOstrowskiResidueState
    (W : UnitOstrowskiWeightSystem)
    (modulus : ℕ) : OstrowskiResidueState where
  qCurr := W.Q 0 % modulus
  qNext := W.Q 1 % modulus
  sum := 0

/--
一桁の局所更新。

現在 digit `digit = d n` と次段部分商 `aNext = a (n+1)` を読むと、
weighted sum を現在 weight だけ進め、weight pair 自身も continued-fraction recurrence で
一段前進させる。
-/
def ostrowskiResidueStep
    (modulus aNext digit : ℕ)
    (s : OstrowskiResidueState) : OstrowskiResidueState where
  qCurr := s.qNext
  qNext := (aNext * s.qNext + s.qCurr) % modulus
  sum := (s.sum + digit * s.qCurr) % modulus

/--
`n` 桁を読み終えた状態。

定義は一桁更新の反復だけであり、full weighted sum は保存しない。
-/
def ostrowskiResidueStateAfter
    (W : UnitOstrowskiWeightSystem)
    (modulus : ℕ)
    (d : ℕ → ℕ) : ℕ → OstrowskiResidueState
  | 0 => initialOstrowskiResidueState W modulus
  | n + 1 =>
      ostrowskiResidueStep modulus (W.a (n + 1)) (d n)
        (ostrowskiResidueStateAfter W modulus d n)

/-- 一桁局所更新は weight pair と prefix sum の剰余解釈を保存する。 -/
theorem ostrowskiResidueStep_sound
    (W : UnitOstrowskiWeightSystem)
    (modulus : ℕ)
    (d : ℕ → ℕ)
    (n : ℕ)
    (s : OstrowskiResidueState)
    (hCurr : s.qCurr = W.Q n % modulus)
    (hNext : s.qNext = W.Q (n + 1) % modulus)
    (hSum : s.sum = ostrowskiPrefixSum W.Q d n % modulus) :
    let t := ostrowskiResidueStep modulus (W.a (n + 1)) (d n) s
    t.qCurr = W.Q (n + 1) % modulus ∧
      t.qNext = W.Q (n + 2) % modulus ∧
      t.sum = ostrowskiPrefixSum W.Q d (n + 1) % modulus := by
  dsimp [ostrowskiResidueStep]
  constructor
  · exact hNext
  constructor
  · rw [W.q_rec n, hCurr, hNext]
    simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]
  · rw [hCurr, hSum]
    simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]

/--
`n` 桁走査後の状態は、期待した二つの weight residue と prefix weighted sum residue を
正確に保持する。
-/
theorem ostrowskiResidueStateAfter_spec
    (W : UnitOstrowskiWeightSystem)
    (modulus : ℕ)
    (d : ℕ → ℕ) :
    ∀ n : ℕ,
      let s := ostrowskiResidueStateAfter W modulus d n
      s.qCurr = W.Q n % modulus ∧
        s.qNext = W.Q (n + 1) % modulus ∧
        s.sum = ostrowskiPrefixSum W.Q d n % modulus := by
  intro n
  induction n with
  | zero =>
      simp [ostrowskiResidueStateAfter, initialOstrowskiResidueState]
  | succ n ih =>
      have h :=
        ostrowskiResidueStep_sound W modulus d n
          (ostrowskiResidueStateAfter W modulus d n)
          ih.1 ih.2.1 ih.2.2
      simpa [ostrowskiResidueStateAfter, Nat.add_assoc] using h

/-- 走査状態の `sum` は full prefix sum modulo `modulus` そのもの。 -/
theorem ostrowskiResidueStateAfter_sum
    (W : UnitOstrowskiWeightSystem)
    (modulus : ℕ)
    (d : ℕ → ℕ)
    (n : ℕ) :
    (ostrowskiResidueStateAfter W modulus d n).sum =
      ostrowskiPrefixSum W.Q d n % modulus := by
  exact (ostrowskiResidueStateAfter_spec W modulus d n).2.2

/--
二つの整数が同じ走査 residue を持てば、`3 * _ + 1` も同じ法で合同になる。

Collatz 固有の `2^r` は Bridge 側でこの一般補題へ代入する。
-/
theorem three_mul_add_one_modEq_of_modEq
    {modulus a b : ℕ}
    (h : a ≡ b [MOD modulus]) :
    3 * a + 1 ≡ 3 * b + 1 [MOD modulus] := by
  exact (h.mul_left 3).add_right 1

end Experimental2
end Collatz3
