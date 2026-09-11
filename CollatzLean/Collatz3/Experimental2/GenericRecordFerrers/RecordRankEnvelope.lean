import CollatzLean.Collatz3.Experimental2.GenericRecordFerrers.RecordPartition

/-!
# Collatz3 Experimental2: 弦順位の記録包絡線と canonical record cut

`canonicalRecordCuts` は `chordRank` の strict running minimum を有限計算で抽出する。
このファイルでは、その条件を「弦順位の記録包絡線が strict に一段下がる角」として
読むための薄い語彙だけを追加する。

数値としての running-minimum 関数を新しい primitive data にはしない。
角であることを

* anchor より後で、
* terminal より手前にあり、
* その点の弦順位が anchor 以降の全過去順位より strict に小さい

という有限条件で直接表す。

したがって中心定理は定義上の言い換えではあるが、以後
`canonicalRecordCuts` を Young/Ferrers 型の階段包絡線の角として扱うための
安定した公開インターフェースになる。
-/

namespace Collatz3
namespace Experimental2
namespace GenericRecordFerrers

/--
`k` で弦順位の過去最小包絡線が strict に下がること。

包絡線そのものを保存せず、`k` の弦順位が anchor 以降の全過去順位より
strict に小さいことを直接要求する。
-/
def IsStrictRankEnvelopeCorner
    (β : ℕ → ℕ)
    (m : ℕ)
    (height : ℕ → ℕ)
    (anchor k : ℕ) : Prop :=
  anchor < k ∧
    k < m ∧
      ∀ j : ℕ,
        anchor ≤ j →
        j < k →
          chordRank β m height k < chordRank β m height j

/--
strict record cut と、弦順位の記録包絡線の strict corner は exact に同じ条件。
-/
theorem isRecordCutAfter_iff_strictRankEnvelopeCorner
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    {anchor k : ℕ} :
    IsRecordCutAfter β m height anchor k ↔
      IsStrictRankEnvelopeCorner β m height anchor k := by
  simpa [IsStrictRankEnvelopeCorner] using
    (isRecordCutAfter_iff
      (β := β) (m := m) (height := height)
      (anchor := anchor) (k := k))

/--
`canonicalRecordCuts` の membership は、標準 anchor `1` から見た
記録包絡線の strict corner であることと exact に同値。

これにより canonical cut 列を、そのまま包絡線階段の角列として読める。
-/
theorem mem_canonicalRecordCuts_iff_strictRankEnvelopeCorner
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    {k : ℕ} :
    k ∈ canonicalRecordCuts β m height ↔
      IsStrictRankEnvelopeCorner β m height canonicalAnchor k := by
  unfold canonicalRecordCuts
  rw [mem_recordCutsAfter_iff]
  constructor
  · intro H
    exact
      (isRecordCutAfter_iff_strictRankEnvelopeCorner
        (β := β) (m := m) (height := height)
        (anchor := canonicalAnchor) (k := k)).1 H.2
  · intro H
    have R :
        IsRecordCutAfter β m height canonicalAnchor k :=
      (isRecordCutAfter_iff_strictRankEnvelopeCorner
        (β := β) (m := m) (height := height)
        (anchor := canonicalAnchor) (k := k)).2 H
    have hSpec :=
      (isRecordCutAfter_iff
        (β := β) (m := m) (height := height)
        (anchor := canonicalAnchor) (k := k)).1 R
    exact ⟨hSpec.2.1, R⟩

end GenericRecordFerrers
end Experimental2
end Collatz3
