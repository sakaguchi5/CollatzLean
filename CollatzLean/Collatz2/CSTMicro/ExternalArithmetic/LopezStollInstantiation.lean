import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalIntegerResidueSeparation

/-!
# López--Stoll corrected convergents: actual-family interface

abstract `LopezStollPacket` を、実際の continued-fraction index `j` に沿う
一族としてまとめる。

このファイル自身は López--Stoll の解析定理を axiom 化しない。
原論文から移植すべき exact facts を structure field として明示し、
そこから既存の `LopezStollPacket` を構成する。

必要なのは各 `j` について

* denominator scale `q_j`,
* exact 2-adic precision `E_j = q_{j+1}+q_{j-1}`,
* corrected numerator / denominator `P_j,Q_j`,
* `Q_j` は odd,
* `-P_j/Q_j` は nonnegative integer ではない,

である。

odd convergent 側の sign branch と、
even convergent 側の mod-3 branch は
既存 pure-integer lemma で `ExcludesNonnegativeExact` に落とせる。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/--
López--Stoll corrected convergent family から必要な exact arithmetic data。

`start` は後段の height / two-log estimate が一様に使える index まで
有限個を捨ててよい。そのため theorem の内容を弱めず、十分大きい index から
family を開始できる。
-/
structure LopezStollInstantiation where
  q : ℕ → ℕ
  E : ℕ → ℕ
  P : ℕ → ℤ
  Q : ℕ → ℤ
  start : ℕ
  start_ge_three : 3 ≤ start

  /-- continued-fraction denominator は増加する。 -/
  q_mono : ∀ n : ℕ, q n ≤ q (n + 1)

  /-- packet scale は exact precision 以下。 -/
  q_le_E : ∀ j : ℕ, q j ≤ E j

  /-- López--Stoll Lemma 21 の precision formula。 -/
  precision_eq :
    ∀ j : ℕ,
      E j = denominatorWindowUpper q j

  /-- denominator は非零。 -/
  Q_ne_zero : ∀ j : ℕ, Q j ≠ 0

  /-- denominator は 2-adic unit。 -/
  Q_odd : ∀ j : ℕ, ¬ (2 : ℤ) ∣ Q j

  /--
  exact equality `R = -P_j/Q_j` は `R ≥ 0` では起こらない。

  odd `j` では sign、
  even `j` では corrected formula の mod-3 argument から入れる。
  -/
  exact_nonnegative_excluded :
    ∀ j : ℕ, ExcludesNonnegativeExact (P j) (Q j)

  /-- approximation windows の upper endpoints は cofinal。 -/
  upper_cofinal :
    ∀ N : ℕ, ∃ j : ℕ,
      start ≤ j ∧
        N ≤ denominatorWindowUpper q j

namespace LopezStollInstantiation

/-- index `j` の corrected approximant を abstract packet へ落とす。 -/
def packet
    (L : LopezStollInstantiation)
    (j : ℕ) : LopezStollPacket := {
  q := L.q j
  E := L.E j
  P := L.P j
  Q := L.Q j
  q_le_E := L.q_le_E j
  Q_ne_zero := L.Q_ne_zero j
  denominatorOdd := L.Q_odd j
  exactNonnegativeExcluded := L.exact_nonnegative_excluded j
}

@[simp] theorem packet_q
    (L : LopezStollInstantiation) (j : ℕ) :
    (L.packet j).q = L.q j := rfl

@[simp] theorem packet_E
    (L : LopezStollInstantiation) (j : ℕ) :
    (L.packet j).E = L.E j := rfl

@[simp] theorem packet_P
    (L : LopezStollInstantiation) (j : ℕ) :
    (L.packet j).P = L.P j := rfl

@[simp] theorem packet_Q
    (L : LopezStollInstantiation) (j : ℕ) :
    (L.packet j).Q = L.Q j := rfl

/-- packet precision は denominator window upper endpoint そのもの。 -/
theorem packet_precision
    (L : LopezStollInstantiation) (j : ℕ) :
    (L.packet j).E = denominatorWindowUpper L.q j := by
  simpa [packet] using L.precision_eq j

/--
odd-convergent 側の sign argument から
`ExcludesNonnegativeExact` を作るための入口。
-/
theorem exactExcluded_of_positive_branch
    {P Q : ℤ}
    (hP : 0 < P)
    (hQ : 0 < Q) :
    ExcludesNonnegativeExact P Q :=
  excludesNonnegativeExact_of_pos hP hQ

/--
even-convergent 側の corrected right-gap formula で、
`3 ∣ Q` かつ `3 ∤ P` が出た場合の入口。
-/
theorem exactExcluded_of_modThree_branch
    {P Q : ℤ}
    (hQ : (3 : ℤ) ∣ Q)
    (hP : ¬ (3 : ℤ) ∣ P) :
    ExcludesNonnegativeExact P Q :=
  excludesNonnegativeExact_of_three_dvd_denominator hQ hP

end LopezStollInstantiation

end ExternalArithmetic
end CSTMicro
end Collatz2
