import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBTerminalTailLog196

set_option linter.style.emptyLine false

/-!
# Pure B terminal tail: one-short root そのものによる exact localization

既存の degree-196 theorem では、one-short square root `r` をいったん
巨大な polynomial majorant `Bnd` で上から押さえ、その後

  m - criticalizationStart <= 2 * Bnd

を得ていた。

しかし矛盾の本体に必要なのは root `r` 自身だけである。
もし terminal tail が `2*r` より長ければ one-short square 全体が
terminal range に入り、局所 rigidity から

  2^(r-2) <= 4*yNat

が従う。一方 `r >= 19+15*ell` と既存 Rhin dyadic bound から

  4*yNat < 2^(r-2)

となり矛盾する。

したがって degree 196 の denominator growth を経由せず、直接

  m - criticalizationStart <= 2*r

を得られる。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

namespace PureBProfileObstruction

/--
threshold `19+15*ell` 以上の actual one-short root が一つあれば、
criticalization tail はその root のちょうど二倍以内に局在する。
-/
theorem criticalizationTail_le_twice_oneShortRoot
    (R : RhinLinearForm14)
    (P : PureBProfileObstruction)
    (hy : 0 ≤ P.y)
    (hStartPos : 0 < P.criticalizationStart)
    {ell r : ℕ}
    (hmSize : P.m + 1 ≤ 2 ^ ell)
    (hNr : 19 + 15 * ell ≤ r)
    (hOneShort :
      CriticalBeattyOneShortSquareAt
        (P.criticalizationStart - 1) r) :
    P.m - P.criticalizationStart ≤ 2 * r := by
  have hrTwo : 2 ≤ r := by
    omega

  by_contra hnot

  have hTwoRTail :
      2 * r < P.m - P.criticalizationStart := by
    omega

  have hFit :
      P.criticalizationStart + 2 * r - 2 ≤ P.m :=
    criticalizationStart_two_root_fit P hTwoRTail

  have hSquareBound :=
    P.criticalizationStart_oneShortSquare_dyadic_bound
      hy hStartPos hrTwo hFit hOneShort

  have hYBound :=
    P.four_yNat_le_terminalDyadic15
      R hy hmSize

  have hContra :
      4 * P.yNat < 2 ^ (r - 2) :=
    oneShortSquare196_terminalDyadic_lt
      hNr hYBound

  omega

end PureBProfileObstruction

end ExternalArithmetic
end CSTMicro
end Collatz2
