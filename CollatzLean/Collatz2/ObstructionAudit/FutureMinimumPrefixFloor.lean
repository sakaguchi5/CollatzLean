import CollatzLean.Collatz2.ObstructionAudit.ExactWordTranslation
import CollatzLean.Collatz2.Global.AdjacentTransferChain
import CollatzLean.Collatz2.Core.Realization
/-!
# Collatz2 Obstruction Audit: future-minimum prefix floor

exact word translation から actual `Runs` は復元できるが、
future-minimum block にはさらに global order 情報がある。

block 内のすべての actual prefix boundary は block start 以上でなければならない。
この条件を exact word realizability とは分離した packet として置く。

同時に actual `AdjacentTransferChain` では、future-minimum 性から
index-level prefix floor が自動的に成立することを示す。
-/

namespace Collatz2

namespace Runs

/-- 同じ word と start を持つ normalized run の endpoint は一意。 -/
theorem end_unique
    {w : Word} {x y z : ℕ}
    (hy : Runs w x y)
    (hz : Runs w x z) :
    y = z := by
  induction hy generalizing z with
  | nil x =>
      cases hz
      rfl
  | @cons e w x a y he hstep haOdd htail ih =>
      cases hz with
      | @cons _ _ _ b z he' hstep' hbOdd htail' =>
          have habMul : 2 ^ e * a = 2 ^ e * b := by
            calc
              2 ^ e * a = 3 * x + 1 := hstep
              _ = 2 ^ e * b := hstep'.symm
          have hab : a = b :=
            Nat.mul_left_cancel (Nat.pow_pos (by omega)) habMul
          subst b
          exact ih htail'

end Runs

namespace ObstructionAudit

/--
exact word packet に actual prefix boundaries と future-minimum floor を追加する。

`prefixBoundary n k` は `word n` の長さ `k` prefix の endpoint。
`prefix_run` がその意味を lossless に固定し、`prefix_floor` が
全 boundary が start 以上であることを要求する。
-/
structure FutureMinimumPrefixFloorConstraints extends ExactWordTranslationConstraints where
  prefixBoundary : ℕ → ℕ → ℕ

  prefix_run : ∀ n k,
    k ≤ (word n).length →
      Runs ((word n).take k) (startValue n) (prefixBoundary n k)

  prefix_floor : ∀ n k,
    k ≤ (word n).length →
      startValue n ≤ prefixBoundary n k

namespace FutureMinimumPrefixFloorConstraints

/-- empty word の run は start と endpoint が一致する。 -/
theorem Runs.eq_of_nil
    {x z : ℕ}
    (hrun : Runs [] x z) :
    z = x := by
  have hEq :=
    (Word.realizes_iff ([] : Word) x z).1 hrun.realizes
  simpa [Word.twoSteps, Word.oddSteps, Word.affineConst] using hEq

/-- prefix 0 の boundary は start 自身。 -/
theorem prefixBoundary_zero
    (P : FutureMinimumPrefixFloorConstraints)
    (n : ℕ) :
    P.prefixBoundary n 0 = P.startValue n := by
  have hrun := P.prefix_run n 0 (by simp)
  simp only [List.take_zero] at hrun
  exact Runs.eq_of_nil hrun

/-- full prefix の boundary は block endpoint。 -/
theorem prefixBoundary_full
    (P : FutureMinimumPrefixFloorConstraints)
    (n : ℕ) :
    P.prefixBoundary n (P.word n).length = P.startValue (n + 1) := by
  have hp := P.prefix_run n (P.word n).length (by simp)
  have hp' :
      Runs (P.word n) (P.startValue n)
        (P.prefixBoundary n (P.word n).length) := by
    simpa using hp
  exact Runs.end_unique hp' (P.runs n)

end FutureMinimumPrefixFloorConstraints
end ObstructionAudit

namespace AdjacentTransferChain

/--
actual adjacent future-minimum block の index-level prefix floor。
`k ≤ length` のすべての prefix boundary で start value 以下へ落ちない。
-/
def FutureMinimumPrefixFloorAt
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) : Prop :=
  ∀ k : ℕ, k ≤ C.length n →
    C.startValue n ≤ O.value (C.startIndex n + k)

/-- future-minimum 性から prefix floor は各 adjacent block で自動的に成立する。 -/
theorem futureMinimumPrefixFloorAt
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (n : ℕ) :
    C.FutureMinimumPrefixFloorAt n := by
  intro k hk
  have hmin := C.startFutureMinimum n
  have hle : C.startIndex n ≤ C.startIndex n + k := by omega
  simpa [AdjacentTransferChain.startValue] using
    hmin (C.startIndex n + k) hle

/-- 正の長さの prefix boundary では unbounded orbit の injectivity により strict。 -/
theorem startValue_lt_prefixBoundary
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n k : ℕ}
    (hkPos : 0 < k)
    (hk : k ≤ C.length n) :
    C.startValue n < O.value (C.startIndex n + k) := by
  have hle := C.futureMinimumPrefixFloorAt n k hk
  have hneIndex : C.startIndex n ≠ C.startIndex n + k := by omega
  have hneValue :
      O.value (C.startIndex n) ≠ O.value (C.startIndex n + k) := by
    intro hEq
    have hinj := O.value_injective_of_unbounded C.unbounded
    exact hneIndex (hinj hEq)
  have hne :
      C.startValue n ≠ O.value (C.startIndex n + k) := by
    simpa [AdjacentTransferChain.startValue] using hneValue
  exact lt_of_le_of_ne hle hne

end AdjacentTransferChain
end Collatz2
