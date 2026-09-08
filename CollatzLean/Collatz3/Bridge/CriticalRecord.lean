import CollatzLean.Collatz3.Critical.WordProfileEquiv
import CollatzLean.Collatz3.Critical.RecordFerrers
import CollatzLean.Collatz3.Ferrers.RecordView
import CollatzLean.Collatz3.Bridge.FirstPassageProfile

/-!
# Collatz3: critical Word / Profile / Record 層の正しい接続

exact `Equiv` と、一方向の強い幾何 bridge を分離する。

  CriticalWord m <-> AdmissibleProfile m <-> RecordView m

は exact。

一方、strong `Critical.RecordFerrers m` は profile に追加の strict block geometry を持つため、
任意 profile と同値とは主張しない。underlying profile を経由して CriticalWord へ忘却できるだけである。
-/

namespace Collatz3
namespace Bridge

/-- critical word shape と finite admissible profile の exact equivalence。 -/
def criticalWordProfileEquiv
    (m : ℕ)
    (hm : 0 < m) :
    Critical.CriticalWord m ≃ Critical.AdmissibleProfile m :=
  Critical.criticalWordEquivAdmissibleProfile m hm

/-- finite profile と弱い canonical record view の exact equivalence。 -/
noncomputable def profileRecordViewEquiv
    (m : ℕ) :
    Critical.AdmissibleProfile m ≃ Ferrers.RecordView m :=
  Ferrers.admissibleProfileEquivRecordView m

/-- positive width では CriticalWord と弱い RecordView も exact `Equiv`。 -/
noncomputable def criticalWordRecordViewEquiv
    (m : ℕ)
    (hm : 0 < m) :
    Critical.CriticalWord m ≃ Ferrers.RecordView m :=
  (criticalWordProfileEquiv m hm).trans
    (profileRecordViewEquiv m)

end Bridge

namespace Critical
namespace RecordFerrers

/--
strong Record--Ferrers から underlying profile を通して critical word shape を復元する。
これは forgetful map であり、Record--Ferrers との `Equiv` ではない。
-/
def toCriticalWord
    {m : ℕ}
    (R : RecordFerrers m) : CriticalWord m :=
  (criticalWordEquivAdmissibleProfile m (by
    have hm := R.one_lt_width
    omega)).symm R.profile

/-- strong Record--Ferrers から得る word は exact に `[1]` から始まる。 -/
theorem toCriticalWord_startsWithOne
    {m : ℕ}
    (R : RecordFerrers m) :
    ∃ tail : Word, R.toCriticalWord.1 = 1 :: tail := by
  exact IsCriticalWord.exists_tail_eq_one_cons
    R.toCriticalWord.2 R.one_lt_width

end RecordFerrers
end Critical

namespace ActualFirstPassage

/-- actual first-passage を `IsCriticalWord` packet に上げる。 -/
theorem toCriticalWordShape
    {w : Word} {x y : ℕ}
    (h : ActualFirstPassage w x y) :
    Critical.IsCriticalWord (Word.oddSteps w) w := by
  refine ⟨h.valid, rfl, h.critical.totalTwoDepth_eq, ?_⟩
  intro k hk
  exact h.critical.prefixDepth_le_beatty hk

/-- odd-step 数が 2 以上の actual critical first-passage word も `[1]` から始まる。 -/
theorem word_startsWithOne
    {w : Word} {x y : ℕ}
    (h : ActualFirstPassage w x y)
    (hm : 1 < Word.oddSteps w) :
    ∃ tail : Word, w = 1 :: tail := by
  exact Critical.IsCriticalWord.exists_tail_eq_one_cons
    h.toCriticalWordShape hm

end ActualFirstPassage
end Collatz3
