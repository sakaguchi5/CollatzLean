import CollatzLean.Collatz3.Experimental2.GenericRecordFerrers.RecordPartition
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Collatz3 Experimental2: 一般屋根の record-level tie 排除

`GenericRecordFerrers.RecordPartition` で定義した strict record cut に対して、
同じ level への再到達を許す weak record cut と、その tie を排除する条件を導入する。

このファイルの算術的な十分条件は

`Nat.Coprime (criticalDepth β m) m`

だけである。これは終端弦の整数係数が primitive であることを表す。
互いに素なら proper cut 上の `chordRank` は `mod m` で単射になり、
したがって weak running minimum と strict running minimum の間に tie は起こらない。

ここでは

* `HasUnitCarry β`,
* `β 1 = 1`,
* `IsAdmissibleRoofPath β m height`,
* roof cut 性,
* 実際の Collatz 軌道

を一切仮定しない。第4段階は純粋な有限順位 + 合同算術の層である。
-/

namespace Collatz3
namespace Experimental2
namespace GenericRecordFerrers

/--
`anchor` より後の cut `k` が、それ以前の区間に対する weak running minimum。
`IsRecordCutAfter` との違いは順位比較に `≤` を使うことだけである。
-/
def IsWeakRecordCutAfter
    (β : ℕ → ℕ)
    (m : ℕ)
    (height : ℕ → ℕ)
    (anchor k : ℕ) : Prop :=
  anchor < k ∧
    k < m ∧
    ∀ j : Fin k,
      anchor ≤ j.1 →
        chordRank β m height k ≤ chordRank β m height j.1

/-- `IsWeakRecordCutAfter` は有限比較なので決定可能。 -/
instance instDecidableIsWeakRecordCutAfter
    (β : ℕ → ℕ)
    (m : ℕ)
    (height : ℕ → ℕ)
    (anchor k : ℕ) :
    Decidable (IsWeakRecordCutAfter β m height anchor k) := by
  unfold IsWeakRecordCutAfter
  infer_instance

/-- weak record cut を通常の自然数区間で読む仕様定理。 -/
theorem isWeakRecordCutAfter_iff
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    {anchor k : ℕ} :
    IsWeakRecordCutAfter β m height anchor k ↔
      anchor < k ∧
      k < m ∧
      ∀ j : ℕ,
        anchor ≤ j →
        j < k →
          chordRank β m height k ≤ chordRank β m height j := by
  constructor
  · intro H
    refine ⟨H.1, H.2.1, ?_⟩
    intro j haj hjk
    exact H.2.2 ⟨j, hjk⟩ haj
  · intro H
    refine ⟨H.1, H.2.1, ?_⟩
    intro j haj
    exact H.2.2 j.1 haj j.2

/--
weak running minimum が現れたなら必ず strict running minimum である。

canonical partition の選択条件ではなく、同じ record level への再到達を
排除するためだけの薄い predicate。
-/
def NoRecordLevelTie
    (β : ℕ → ℕ)
    (m : ℕ)
    (height : ℕ → ℕ)
    (anchor : ℕ) : Prop :=
  ∀ k : ℕ,
    IsWeakRecordCutAfter β m height anchor k →
      IsRecordCutAfter β m height anchor k

/--
終端弦の係数対 `(criticalDepth β m, m)` が primitive である。

一般理論では `β` と幅 `m` だけの算術条件として置く。
-/
def IsPrimitiveWidth
    (β : ℕ → ℕ)
    (m : ℕ) : Prop :=
  Nat.Coprime (criticalDepth β m) m

/--
proper cut の `chordRank` が単射なら record-level tie は起こらない。

primitive 性を使う前の純粋な順序論的な一般形。
-/
theorem noRecordLevelTie_of_chordRank_injective
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    {anchor : ℕ}
    (hInjective :
      ∀ {a b : ℕ},
        a < m →
        b < m →
        chordRank β m height a = chordRank β m height b →
          a = b) :
    NoRecordLevelTie β m height anchor := by
  intro k W
  apply (isRecordCutAfter_iff).2
  have hW :=
    (isWeakRecordCutAfter_iff
      (β := β) (m := m) (height := height)
      (anchor := anchor) (k := k)).1 W
  refine ⟨hW.1, hW.2.1, ?_⟩
  intro j haj hjk
  have hLe := hW.2.2 j haj hjk
  have hjm : j < m := lt_trans hjk hW.2.1
  have hNe :
      chordRank β m height k ≠ chordRank β m height j := by
    intro hEq
    have hkj := hInjective hW.2.1 hjm hEq
    omega
  exact lt_of_le_of_ne hLe hNe

/--
primitive width では proper cut 上の一般弦順位は単射。

`mod m` に落とすと `m * cutDepth` の項が消え、
`criticalDepth β m` は `m` と互いに素なので unit として消去できる。
-/
theorem chordRank_injective_of_primitive
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    (P : IsPrimitiveWidth β m)
    {a b : ℕ}
    (ha : a < m)
    (hb : b < m)
    (hEq : chordRank β m height a = chordRank β m height b) :
    a = b := by
  have hm : 0 < m := by omega
  let : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have hCast :=
    congrArg (fun z : ℤ => (z : ZMod m)) hEq
  have hMul :
      (((criticalDepth β m * a : ℕ) : ZMod m)) =
        (((criticalDepth β m * b : ℕ) : ZMod m)) := by
    simpa [chordRank, Nat.cast_mul] using hCast
  let U : (ZMod m)ˣ :=
    ZMod.unitOfCoprime (criticalDepth β m)
      (by simpa [IsPrimitiveWidth] using P)
  have hHU :
      ((criticalDepth β m : ℕ) : ZMod m) = (↑U : ZMod m) := by
    simp [U]
    rfl
  have hMul' :
      (↑U : ZMod m) * ((a : ℕ) : ZMod m) =
        (↑U : ZMod m) * ((b : ℕ) : ZMod m) := by
    have hMul0 := hMul
    simp only [Nat.cast_mul] at hMul0
    rw [hHU] at hMul0
    exact hMul0
  have hCancel :=
    congrArg
      (fun z : ZMod m => (↑(U⁻¹) : ZMod m) * z)
      hMul'
  have hAB :
      ((a : ℕ) : ZMod m) = ((b : ℕ) : ZMod m) := by
    simpa [← mul_assoc] using hCancel
  have hVal := congrArg ZMod.val hAB
  simpa [ZMod.val_natCast, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt hb] using hVal

/-- primitive width は任意 anchor に対する record-level tie を排除する。 -/
theorem noRecordLevelTie_of_primitive
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    {anchor : ℕ}
    (P : IsPrimitiveWidth β m) :
    NoRecordLevelTie β m height anchor := by
  apply noRecordLevelTie_of_chordRank_injective
  intro a b ha hb hEq
  exact chordRank_injective_of_primitive P ha hb hEq

/-- 標準 anchor `1` に対する primitive-width 版。 -/
theorem canonical_noRecordLevelTie_of_primitive
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    (P : IsPrimitiveWidth β m) :
    NoRecordLevelTie β m height canonicalAnchor :=
  noRecordLevelTie_of_primitive P

end GenericRecordFerrers
end Experimental2
end Collatz3
