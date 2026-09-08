import CollatzLean.Collatz3.Critical.WordProfileEquiv
import CollatzLean.Collatz3.Critical.RecordSkeleton
import CollatzLean.Collatz3.Critical.RecordFerrers
import CollatzLean.Collatz3.Ferrers.RecordView
import CollatzLean.Collatz3.Bridge.FirstPassageProfile

/-!
# Collatz3: critical Word / Profile / Record 層の接続

exact `Equiv` と、一方向の追加幾何 bridge を分離する。

`CriticalWord m <-> AdmissibleProfile m <-> RecordView m`

は exact。

一方、`CriticalRecordSkeleton` は strict rank/roof geometry を追加し、
full `RecordFerrers` はさらに local critical block geometry を追加する。
したがって後二者を arbitrary profile と `Equiv` にはしない。
-/

namespace Collatz3
namespace Bridge

/-- critical word shape と finite admissible profile の exact equivalence。 -/
def criticalWordProfileEquiv
    (m : ℕ)
    (hm : 0 < m) :
    Critical.CriticalWord m ≃ Critical.AdmissibleProfile m :=
  Critical.criticalWordEquivAdmissibleProfile m hm

/-- finite profile と弱い canonical record view の computable exact equivalence。 -/
def profileRecordViewEquiv
    (m : ℕ) :
    Critical.AdmissibleProfile m ≃ Ferrers.RecordView m :=
  Ferrers.admissibleProfileEquivRecordView m

/-- positive width では CriticalWord と弱い RecordView も computable exact `Equiv`。 -/
def criticalWordRecordViewEquiv
    (m : ℕ)
    (hm : 0 < m) :
    Critical.CriticalWord m ≃ Ferrers.RecordView m :=
  (criticalWordProfileEquiv m hm).trans
    (profileRecordViewEquiv m)

end Bridge

namespace Critical
namespace CriticalRecordSkeleton

/--
critical record skeleton から underlying profile を通して critical word shape を復元する。
これは forgetful map であり、skeleton との `Equiv` ではない。
-/
def toCriticalWord
    {m : ℕ}
    (R : CriticalRecordSkeleton m) : CriticalWord m :=
  (criticalWordEquivAdmissibleProfile m (by
    have hm := R.one_lt_width
    omega)).symm R.profile

/-- critical record skeleton から得る word は exact に `[1]` から始まる。 -/
theorem toCriticalWord_startsWithOne
    {m : ℕ}
    (R : CriticalRecordSkeleton m) :
    ∃ tail : Word, R.toCriticalWord.1 = 1 :: tail := by
  exact IsCriticalWord.exists_tail_eq_one_cons
    R.toCriticalWord.2 R.one_lt_width

end CriticalRecordSkeleton

namespace RecordFerrers

/-- full Record--Ferrers から whole critical word shape への忘却。 -/
def toCriticalWord
    {m : ℕ}
    (R : RecordFerrers m) : CriticalWord m :=
  R.record.toCriticalWord

/-- full Record--Ferrers の whole word も `[1]` から始まる。 -/
theorem toCriticalWord_startsWithOne
    {m : ℕ}
    (R : RecordFerrers m) :
    ∃ tail : Word, R.toCriticalWord.1 = 1 :: tail := by
  exact R.record.toCriticalWord_startsWithOne

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
