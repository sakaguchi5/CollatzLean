import CollatzLean.Collatz2.CSTMicro.CarryGeometry.SafePrefixCarryClearance

/-!
# Minimal bad first-passage word

A -> B provenance では、選んだ Ferrers chain 上で B より前の endpoint が safe であることを
lossless に保持した。

ここではさらに、bad first-passage word が一つでも存在するなら、同じ length の bad word の
中から Ferrers inversion が最小のものを選ぶ。

この minimal bad word `B` については、

* `B` 自身は first-passage かつ separation failure
* `B` と同じ length
* `ferrersInversion` が `B` より小さい同 length の first-passage word はすべて safe

となる。

したがって「選んだ一つの chain の proper prefix が safe」から一段強く、
`B` より低い Ferrers rank にある同 length の first-passage region 全体が safe になる。
-/

namespace Collatz2
namespace CSTMicro

/--
length `L` における Ferrers inversion 最小の bad first-passage word。

minimality は同じ length の bad first-passage word 全体に対して述べる。
-/
structure MinimalBadFirstPassageAtLength (L : ℕ) where
  word : ParityWord
  length_eq : word.length = L
  firstPassage : IsFirstPassageWord word
  failure : ¬ WordPureSeparation word
  inversion_minimal :
    ∀ v : ParityWord,
      v.length = L →
      IsFirstPassageWord v →
      ¬ WordPureSeparation v →
      ferrersInversion word ≤ ferrersInversion v

namespace MinimalBadFirstPassageAtLength

/-- minimal bad word 自身の Ferrers inversion。 -/
def inversion
    {L : ℕ}
    (B : MinimalBadFirstPassageAtLength L) : ℕ :=
  ferrersInversion B.word

/--
同じ length の bad first-passage word の inversion は minimal bad word 以上。
-/
theorem inversion_le_of_failure
    {L : ℕ}
    (B : MinimalBadFirstPassageAtLength L)
    {v : ParityWord}
    (hLength : v.length = L)
    (hFP : IsFirstPassageWord v)
    (hFailure : ¬ WordPureSeparation v) :
    B.inversion ≤ ferrersInversion v := by
  exact B.inversion_minimal v hLength hFP hFailure

/--
Ferrers inversion が minimal bad word より strict に小さい同 length の
first-passage word は必ず safe。

これが step 6 の global lower-region safety。
-/
theorem safe_of_strictly_lower_inversion
    {L : ℕ}
    (B : MinimalBadFirstPassageAtLength L)
    {v : ParityWord}
    (hLength : v.length = L)
    (hFP : IsFirstPassageWord v)
    (hInv : ferrersInversion v < B.inversion) :
    WordPureSeparation v := by
  by_contra hFailure
  have hMin :
      B.inversion ≤ ferrersInversion v :=
    B.inversion_le_of_failure hLength hFP hFailure
  omega

/--
minimal bad word の任意の first-passage Ferrers predecessor は safe。

一つの adjacent cover で inversion が exact に 1 増えるため、predecessor は
minimal bad inversion より strict に小さい。
-/
theorem predecessor_safe
    {L : ℕ}
    (B : MinimalBadFirstPassageAtLength L)
    {lower : ParityWord}
    (S : FerrersStep lower B.word)
    (hLowerFP : IsFirstPassageWord lower) :
    WordPureSeparation lower := by
  apply B.safe_of_strictly_lower_inversion
  · exact S.length_eq.trans B.length_eq
  · exact hLowerFP
  · have hSucc := S.ferrersInversion_succ
    unfold inversion
    omega

end MinimalBadFirstPassageAtLength

/-! ## 2. bad target から inversion-minimal B を抽出 -/

/--
bad first-passage target が一つあれば、同じ length に Ferrers inversion 最小の
bad first-passage word が存在する。

`Nat.find` は inversion の自然数最小値だけを選び、その最小値を実現する word も
`Nat.find_spec` から同時に回収する。
-/
theorem exists_minimalBadFirstPassageAtLength
    {target : ParityWord}
    (hTargetFP : IsFirstPassageWord target)
    (hTargetFailure : ¬ WordPureSeparation target) :
    Nonempty (MinimalBadFirstPassageAtLength target.length) := by
  classical
  let BadAt : ℕ → Prop := fun n =>
    ∃ v : ParityWord,
      v.length = target.length ∧
      IsFirstPassageWord v ∧
      ¬ WordPureSeparation v ∧
      ferrersInversion v = n
  have hExists : ∃ n : ℕ, BadAt n := by
    refine ⟨ferrersInversion target, target, rfl, hTargetFP, hTargetFailure, rfl⟩
  have hSpec : BadAt (Nat.find hExists) :=
    Nat.find_spec hExists
  rcases hSpec with
    ⟨B, hLength, hBFP, hBFailure, hBInv⟩
  refine
    ⟨{
      word := B
      length_eq := hLength
      firstPassage := hBFP
      failure := hBFailure
      inversion_minimal := ?_
    }⟩
  intro v hVLength hVFP hVFailure
  have hVBad : BadAt (ferrersInversion v) := by
    exact ⟨v, hVLength, hVFP, hVFailure, rfl⟩
  have hMin : Nat.find hExists ≤ ferrersInversion v :=
    Nat.find_min' hExists hVBad
  calc
    ferrersInversion B = Nat.find hExists := hBInv
    _ ≤ ferrersInversion v := hMin

/--
step 5 と step 6 を同時に読むための bridge。

bad target から minimal bad word `B` を取り、`B` より低い inversion の
同 length first-passage word がすべて safe であることを一つの存在定理で返す。
-/
theorem exists_minimalBadFirstPassage_with_lower_region_safe
    {target : ParityWord}
    (hTargetFP : IsFirstPassageWord target)
    (hTargetFailure : ¬ WordPureSeparation target) :
    ∃ B : MinimalBadFirstPassageAtLength target.length,
      ∀ v : ParityWord,
        v.length = target.length →
        IsFirstPassageWord v →
        ferrersInversion v < B.inversion →
        WordPureSeparation v := by
  rcases
      exists_minimalBadFirstPassageAtLength
        hTargetFP hTargetFailure with
    ⟨B⟩
  refine ⟨B, ?_⟩
  intro v hLength hFP hInv
  exact B.safe_of_strictly_lower_inversion hLength hFP hInv

end CSTMicro
end Collatz2
