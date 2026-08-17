import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Tactic.Linarith

/-!
# Critical residue arithmetic: López--Stoll approximant packet

このファイルは Collatz / Ferrers / Sturmian の語を使わず、
一つの rational approximant `-P/Q` が small nonnegative integer residue を
排除するために本当に必要な整数論 packet だけを切り出す。

外部文献側から必要なのは各 index `j` について概ね

* certified approximation precision `E_j`,
* Archimedean scale index `q_j`,
* integers `P_j,Q_j`,
* `Q_j` は odd,
* `-P_j/Q_j` は nonnegative integer ではない,

である。

重要なのは `E_j` を actual 2-adic valuation の最大値とは解釈しないこと。
後段が利用してよい precision budget を表すだけであり、
実際の valuation が `E_j` より大きくても何も問題はない。

2-adic approximation 自体は、後段では

  2^e ∣ P_j + R Q_j

という純整数 divisibility にだけ翻訳して使う。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-- `R` と rational approximant `-P/Q` が precision `2^e` で一致することの
    純整数版。 -/
def MatchesAtTwoPower
    (e : ℕ) (P Q : ℤ) (R : ℕ) : Prop :=
  ((2 : ℤ) ^ e) ∣ P + (R : ℤ) * Q

/-- exact equality `R = -P/Q` が nonnegative integer `R` では起こらない。 -/
def ExcludesNonnegativeExact (P Q : ℤ) : Prop :=
  ∀ R : ℕ, P + (R : ℤ) * Q ≠ 0

/--
一つの corrected López--Stoll approximant に必要な pure arithmetic packet。

`q` は Christoffel height scale、`E` は certified 2-adic precision budget。
`denominatorOdd` は `Q` が 2-adic unit であることを表す。
-/
structure LopezStollPacket where
  q : ℕ
  E : ℕ
  P : ℤ
  Q : ℤ
  q_le_E : q ≤ E
  Q_ne_zero : Q ≠ 0
  denominatorOdd : ¬ (2 : ℤ) ∣ Q
  exactNonnegativeExcluded : ExcludesNonnegativeExact P Q

namespace LopezStollPacket

/-- packet が precision `e` で integer `R` と一致するという略記。 -/
def Matches (A : LopezStollPacket) (e R : ℕ) : Prop :=
  MatchesAtTwoPower e A.P A.Q R

/-- exact equality branch は packet の仮定だけで即排除される。 -/
theorem exact_ne_zero
    (A : LopezStollPacket)
    (R : ℕ) :
    A.P + (R : ℤ) * A.Q ≠ 0 :=
  A.exactNonnegativeExcluded R

end LopezStollPacket

/--
odd convergent 側で使う最も安い exact-equality 排除。
`P>0,Q>0` なら `-P/Q<0` なので nonnegative integer にはならない。
-/
theorem excludesNonnegativeExact_of_pos
    {P Q : ℤ}
    (hP : 0 < P)
    (hQ : 0 < Q) :
    ExcludesNonnegativeExact P Q := by
  intro R hzero
  have hRQ : 0 ≤ (R : ℤ) * Q := by
    exact mul_nonneg (by exact_mod_cast Nat.zero_le R) (le_of_lt hQ)
  have hsum : 0 < P + (R : ℤ) * Q := by
    linarith
  linarith

/--
`Q` が 3 の倍数で `P` が 3 の倍数でなければ、`-P/Q` は整数ではない。
even convergent の right-gap corrected formula の mod-3 branch を受けるための
pure integer lemma。
-/
theorem excludesNonnegativeExact_of_three_dvd_denominator
    {P Q : ℤ}
    (hQ : (3 : ℤ) ∣ Q)
    (hP : ¬ (3 : ℤ) ∣ P) :
    ExcludesNonnegativeExact P Q := by
  intro R hzero
  apply hP
  have hRQ : (3 : ℤ) ∣ (R : ℤ) * Q := by
    exact dvd_mul_of_dvd_right hQ (R : ℤ)
  have hneg : (3 : ℤ) ∣ -((R : ℤ) * Q) := by
    exact dvd_neg.mpr hRQ
  have hEq : P = -((R : ℤ) * Q) := by
    linarith
  simpa [hEq] using hneg

end ExternalArithmetic
end CSTMicro
end Collatz2
