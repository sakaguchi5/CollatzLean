import CollatzLean.Collatz2.Core.AffineTransfer

/-!
# Collatz2 Obstruction Audit: constraint packets

`EventuallyNegative` から導かれた条件のうち、
actual `OddOrbit` / `Runs` / exact word translation をいったん外し、
どの arithmetic / affine 条件集合まで明示的な無限 model が存在するかを監査する。

この directory の目的は `EventuallyNegative` 自体の存在を主張することではない。
各 packet に inhabitant を与えることで、そこに列挙した条件だけからは
`False` を導けないことを形式的に固定する。
-/

namespace Collatz2
namespace ObstructionAudit

/--
negative affine positive-return chain の最小 packet。

ここでは genuine Collatz word から来ることを要求しない。
-/
structure NegativeAffineConstraints where
  startValue : ℕ → ℕ
  oddCoeff : ℕ → ℕ
  twoCoeff : ℕ → ℕ
  translate : ℕ → ℕ

  start_gt_one : ∀ n, 1 < startValue n
  start_strict : StrictMono startValue
  positive_return : ∀ n, startValue n < startValue (n + 1)

  realizes : ∀ n,
    twoCoeff n * startValue (n + 1) =
      oddCoeff n * startValue n + translate n

  negative : ∀ n, oddCoeff n < twoCoeff n

/--
primitive center / return-gap arithmetic まで保持した packet。

`h = centerContent`, `d = primitive denominator`, `s = primitive return gap`,
`alpha = primitive center coordinate`, `kappa = adjacent separation` を保持する。
-/
structure PrimitiveReturnGapConstraints extends NegativeAffineConstraints where
  coordinate : ℕ → ℕ
  returnGap : ℕ → ℕ
  centerContent : ℕ → ℕ
  denominator : ℕ → ℕ
  primitiveGap : ℕ → ℕ
  alpha : ℕ → ℕ
  kappa : ℕ → ℤ

  start_coordinate : ∀ n,
    startValue n = 4 * coordinate n + 3

  returnGap_spec : ∀ n,
    startValue (n + 1) = startValue n + returnGap n

  centerGap_factor : ∀ n,
    twoCoeff n =
      oddCoeff n + centerContent n * denominator n

  returnGap_factor : ∀ n,
    returnGap n =
      4 * centerContent n * primitiveGap n

  centerContent_pos : ∀ n, 0 < centerContent n
  denominator_pos : ∀ n, 0 < denominator n
  primitiveGap_pos : ∀ n, 0 < primitiveGap n

  centerContent_odd : ∀ n, Odd (centerContent n)
  denominator_odd : ∀ n, Odd (denominator n)

  primitiveGap_coprime_denominator : ∀ n,
    Nat.Coprime (primitiveGap n) (denominator n)

  translate_center_normal_form : ∀ n,
    translate n =
      centerContent n *
        (3 * denominator n + 4 * alpha n)

  alpha_start_coordinate : ∀ n,
    alpha n =
      denominator n * coordinate n +
        twoCoeff n * primitiveGap n

  alpha_end_coordinate : ∀ n,
    alpha n =
      denominator n * coordinate (n + 1) +
        oddCoeff n * primitiveGap n

  kappa_center_cross : ∀ n,
    kappa n =
      (denominator n : ℤ) * (alpha (n + 1) : ℤ) -
        (denominator (n + 1) : ℤ) * (alpha n : ℤ)

  kappa_gap_balance : ∀ n,
    kappa n =
      (denominator n : ℤ) * (twoCoeff (n + 1) : ℤ) *
          (primitiveGap (n + 1) : ℤ) -
        (denominator (n + 1) : ℤ) * (oddCoeff n : ℤ) *
          (primitiveGap n : ℤ)

/--
primitive packet に `kappa > 0` と division-free center escape を加えたもの。

`M*d < 3*d+4*alpha` は primitive center `(3*d+4*alpha)/d` が
`M` より右にあることを division-free に表す。
-/
structure PositiveKappaConstraints extends PrimitiveReturnGapConstraints where
  kappa_pos : ∀ n, 0 < kappa n

  center_escape : ∀ M, ∃ n,
    M * denominator n <
      3 * denominator n + 4 * alpha n

/--
さらに diagonal が genuine word の `3^p / 2^H` から来て、
word が exponent `1` で始まることまで要求する packet。

重要: `translate = Word.affineConst word` はまだ要求しない。
ここが audit の intended boundary である。
-/
structure DiagonalWordProfileConstraints extends PositiveKappaConstraints where
  word : ℕ → Word

  word_valid : ∀ n, (word n).Valid
  word_nonempty : ∀ n, word n ≠ []
  word_begins_one : ∀ n, ∃ v : Word, word n = 1 :: v

  oddCoeff_eq_word : ∀ n,
    oddCoeff n = (AffineTransfer.ofWord (word n)).oddCoeff

  twoCoeff_eq_word : ∀ n,
    twoCoeff n = (AffineTransfer.ofWord (word n)).twoCoeff

/--
primitive affine level で `kappa = 1` を全点に課した sharp packet。
word profile は要求しない。
-/
structure SharpKappaOneConstraints extends PositiveKappaConstraints where
  kappa_eq_one : ∀ n, kappa n = 1

end ObstructionAudit
end Collatz2
