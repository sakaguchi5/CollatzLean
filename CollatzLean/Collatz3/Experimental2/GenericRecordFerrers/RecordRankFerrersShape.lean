import CollatzLean.Collatz3.Experimental2.GenericRecordFerrers.RecordFerrersRankDrop
import CollatzLean.Collatz3.Combinatorics.YoungFerrers
import Mathlib.Tactic.Linarith

/-!
# Collatz3 Experimental2: 記録包絡線を Ferrers / Young 図形へ上げる

`RecordRankEnvelope` と `RecordFerrersRankDrop` により、完成 `RecordFerrers` では

* `canonicalRecordCuts` が弦順位の過去最小包絡線の strict corner であり、
* canonical block 長 `r` に対応する corner 間の縦落差が

  `m * criticalDepth β r - criticalDepth β m * r`

  である

ことが分かっている。

このファイルでは、その情報を古典的な `FerrersShape` にまとめる。
新しい巨大 structure は作らず、canonical length 列から

1. 各 block の整数値 rank drop、
2. その正の自然数表示、
3. suffix drop の高さを block 長だけ繰り返した列図形

を薄く導く。

完成 `RecordFerrers` では各 canonical block は genuine strict record excursion なので、
各 rank drop は正である。従ってここで作る Ferrers shape は、単なる任意の partition
ではなく、実際の strict rank-envelope corner の落差を符号化する。
-/

namespace Collatz3
namespace Experimental2
namespace GenericRecordFerrers

/--
幅 `m` の RecordFerrers 幾何で、長さ `r` の local critical block が持つ
整数値の弦順位落差。
-/
def rankDropInt
    (β : ℕ → ℕ)
    (m r : ℕ) : ℤ :=
  (m : ℤ) * (criticalDepth β r : ℤ) -
    (criticalDepth β m : ℤ) * (r : ℤ)

/-- rank drop の自然数表示。完成 RecordFerrers の canonical block では正になる。 -/
def rankDropNat
    (β : ℕ → ℕ)
    (m r : ℕ) : ℕ :=
  (rankDropInt β m r).toNat

/-- block 列の全 rank drop の和。corner の高さを suffix sum として読むために使う。 -/
def rankDropIntSum
    (β : ℕ → ℕ)
    (m : ℕ) : List ℕ → ℤ
  | [] => 0
  | r :: rs => rankDropInt β m r + rankDropIntSum β m rs

/-- 自然数化した rank drop の総和。Ferrers 列高そのものを与える。 -/
def rankDropNatSum
    (β : ℕ → ℕ)
    (m : ℕ) : List ℕ → ℕ
  | [] => 0
  | r :: rs => rankDropNat β m r + rankDropNatSum β m rs

/--
length code `rs` から作る記録包絡線の列高。

先頭 block の長さが `r` なら、その `r` 列では全 suffix drop の和を高さにし、
それを過ぎたら tail code を同じ規則で読む。
-/
def rankFerrersColumnHeightFromLengths
    (β : ℕ → ℕ)
    (m : ℕ) : List ℕ → ℕ → ℕ
  | [], _ => 0
  | r :: rs, k =>
      if k < r then
        rankDropNatSum β m (r :: rs)
      else
        rankFerrersColumnHeightFromLengths β m rs (k - r)

/-- code から作る任意の列高は、その code の全 suffix drop 和以下。 -/
theorem rankFerrersColumnHeightFromLengths_le_sum
    (β : ℕ → ℕ)
    (m : ℕ) :
    ∀ (rs : List ℕ) (k : ℕ),
      rankFerrersColumnHeightFromLengths β m rs k ≤
        rankDropNatSum β m rs := by
  intro rs
  induction rs with
  | nil =>
      intro k
      simp [rankFerrersColumnHeightFromLengths, rankDropNatSum]
  | cons r rs ih =>
      intro k
      by_cases hk : k < r
      · simp [rankFerrersColumnHeightFromLengths, rankDropNatSum, hk]
      · have hTail := ih (k - r)
        simp only [rankFerrersColumnHeightFromLengths, hk, ↓reduceIte]
        simp only [rankDropNatSum]
        omega

/--
length code から作る列高は右へ進むほど増えない。
従って任意の code が古典 Ferrers / Young 型の列図形を与える。
-/
theorem rankFerrersColumnHeightFromLengths_antitone
    (β : ℕ → ℕ)
    (m : ℕ)
    (rs : List ℕ) :
    Antitone (rankFerrersColumnHeightFromLengths β m rs) := by
  induction rs with
  | nil =>
      intro a b hab
      simp [rankFerrersColumnHeightFromLengths]
  | cons r rs ih =>
      intro a b hab
      by_cases hb : b < r
      · have ha : a < r := lt_of_le_of_lt hab hb
        simp [rankFerrersColumnHeightFromLengths, ha, hb]
      · by_cases ha : a < r
        · have hTail :=
            rankFerrersColumnHeightFromLengths_le_sum β m rs (b - r)
          simp only [rankFerrersColumnHeightFromLengths, ha, hb, ↓reduceIte]
          simp only [rankDropNatSum]
          omega
        · have hSub : a - r ≤ b - r := Nat.sub_le_sub_right hab r
          have hTail := ih hSub
          simp only [rankFerrersColumnHeightFromLengths, ha, hb, ↓reduceIte]
          exact hTail

/--
任意の length code を幅 `m-1` の古典 Ferrers shape として読む。
canonical RecordFerrers code では長さの総和が exact に `m-1` なので、余分な zero tail はない。
-/
def rankFerrersShapeFromLengths
    (β : ℕ → ℕ)
    (m : ℕ)
    (rs : List ℕ) :
    Combinatorics.FerrersShape (m - 1) :=
  ⟨fun k => rankFerrersColumnHeightFromLengths β m rs k.1,
    by
      intro i j hij
      exact rankFerrersColumnHeightFromLengths_antitone β m rs hij⟩

/--
block 列に沿って、実際の chord rank が endpoint ごとに strict に下がること。
canonical record partition から直接導くための薄い再帰 predicate。
-/
def StrictRankDropsFrom
    (β : ℕ → ℕ)
    (m : ℕ)
    (height : ℕ → ℕ) : ℕ → List ℕ → Prop
  | _a, [] => True
  | a, r :: rs =>
      chordRank β m height (a + r) < chordRank β m height a ∧
        StrictRankDropsFrom β m height (a + r) rs

/--
canonical weak record blocks を cut 差へ変換すると、得られる全 block で
chord rank は endpoint において strict に下がる。
-/
theorem strictRankDropsFrom_blockLengthsFromCuts
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ} :
    ∀ (a : ℕ) (cuts : List ℕ),
      CanonicalWeakBlocksFrom β m height a cuts →
        StrictRankDropsFrom β m height a
          (blockLengthsFromCuts m a cuts)
  | a, [], W => by
      simp only [CanonicalWeakBlocksFrom] at W
      simp only [blockLengthsFromCuts, StrictRankDropsFrom]
      exact ⟨W.end_drop, trivial⟩
  | a, k :: ks, W => by
      simp only [CanonicalWeakBlocksFrom] at W
      simp only [blockLengthsFromCuts, StrictRankDropsFrom]
      have hak : a < k := by
        have := W.1.length_pos
        omega
      have hIndex : a + (k - a) = k :=
        Nat.add_sub_of_le (Nat.le_of_lt hak)
      refine ⟨?_, ?_⟩
      · exact W.1.end_drop
      · rw [hIndex]
        exact strictRankDropsFrom_blockLengthsFromCuts k ks W.2.2

/--
一般 admissible roof path の canonical length 列は、実際の strict rank drop 列でもある。
-/
theorem canonicalRecordLengths_strictRankDrops
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    (U : HasUnitCarry β)
    (A : IsAdmissibleRoofPath β m height)
    (hβ1 : β 1 = 1)
    (hm : 1 < m) :
    StrictRankDropsFrom β m height canonicalAnchor
      (canonicalRecordLengths β m height) := by
  have W := canonicalWeakBlocksFrom_canonicalRecordCuts U A hβ1 hm
  unfold canonicalRecordLengths recordLengthsAfter
  simpa [canonicalRecordCuts] using
    (strictRankDropsFrom_blockLengthsFromCuts
      (β := β) (m := m) (height := height)
      canonicalAnchor (recordCutsAfter β m height canonicalAnchor)
      (by simpa [canonicalRecordCuts] using W))

/-- length code の各整数値 rank drop が正であること。 -/
def PositiveRankDrops
    (β : ℕ → ℕ)
    (m : ℕ) : List ℕ → Prop
  | [] => True
  | r :: rs =>
      0 < rankDropInt β m r ∧ PositiveRankDrops β m rs

/--
strict endpoint drop と exact rank-drop 公式を組み合わせると、code の各 `rankDropInt` は正。
-/
theorem positiveRankDrops_of_strict_and_formula
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ} :
    ∀ (a : ℕ) (rs : List ℕ),
      StrictRankDropsFrom β m height a rs →
      RankEnvelopeDropLawFrom β m height a rs →
        PositiveRankDrops β m rs
  | _a, [], _S, _L => by
      trivial
  | a, r :: rs, S, L => by
      simp only [StrictRankDropsFrom] at S
      simp only [RankEnvelopeDropLawFrom] at L
      simp only [PositiveRankDrops]
      have hEq :
          chordRank β m height a - chordRank β m height (a + r) =
            rankDropInt β m r := by
        simpa [rankDropInt] using L.1
      refine ⟨?_, ?_⟩
      · linarith [S.1, hEq]
      · exact
          positiveRankDrops_of_strict_and_formula
            (a + r) rs S.2 L.2

/--
rank-drop law が terminal まで届くなら、start の chord rank は
length code の全 integer drop の和に等しい。
-/
theorem chordRank_eq_rankDropIntSum_of_terminal
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ} :
    ∀ (a : ℕ) (rs : List ℕ),
      RankEnvelopeDropLawFrom β m height a rs →
      a + rs.sum = m →
        chordRank β m height a = rankDropIntSum β m rs
  | a, [], _L, hEnd => by
      have ha : a = m := by
        simpa using hEnd
      subst a
      simp [rankDropIntSum]
  | a, r :: rs, L, hEnd => by
      simp only [RankEnvelopeDropLawFrom] at L
      have hTailEnd : (a + r) + rs.sum = m := by
        simpa [List.sum_cons, Nat.add_assoc] using hEnd
      have hTail :=
        chordRank_eq_rankDropIntSum_of_terminal
          (a + r) rs L.2 hTailEnd
      have hHead :
          chordRank β m height a - chordRank β m height (a + r) =
            rankDropInt β m r := by
        simpa [rankDropInt] using L.1
      simp only [rankDropIntSum]
      linarith

namespace RecordFerrers

/-- 完成 RecordFerrers の canonical length code では、全 rank drop が正。 -/
theorem positiveRankDrops
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m) :
    PositiveRankDrops β m
      (canonicalRecordLengths β m R.height) := by
  exact
    positiveRankDrops_of_strict_and_formula
      canonicalAnchor
      (canonicalRecordLengths β m R.height)
      (canonicalRecordLengths_strictRankDrops
        R.unitCarry R.admissible R.roof_one R.one_lt_width)
      R.rankEnvelopeDropLaw

/--
完成 RecordFerrers に対応する古典 Ferrers / Young shape。
primitive data は増やさず、`canonicalRecordLengths` だけから構成する。
-/
def rankFerrersShape
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m) :
    Combinatorics.FerrersShape (m - 1) :=
  rankFerrersShapeFromLengths β m
    (canonicalRecordLengths β m R.height)

/-- canonical length code は shape の幅 `m-1` を exact に覆う。 -/
theorem canonicalRecordLengths_sum_width
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m) :
    (canonicalRecordLengths β m R.height).sum = m - 1 :=
  canonicalRecordLengths_sum R.one_lt_width

/--
canonical anchor の実際の chord rank は、canonical length code から計算した
全 rank drop の和に exact に一致する。
-/
theorem canonicalAnchor_chordRank_eq_rankDropIntSum
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m) :
    chordRank β m R.height canonicalAnchor =
      rankDropIntSum β m (canonicalRecordLengths β m R.height) := by
  have hSum := R.canonicalRecordLengths_sum_width
  have hEnd :
      canonicalAnchor +
          (canonicalRecordLengths β m R.height).sum = m := by
    rw [hSum]
    unfold canonicalAnchor
    have hm := R.one_lt_width
    omega
  exact
    chordRank_eq_rankDropIntSum_of_terminal
      canonicalAnchor
      (canonicalRecordLengths β m R.height)
      R.rankEnvelopeDropLaw hEnd

/--
`canonicalRecordLengths` が一致する二つの RecordFerrers は、
この rank-envelope Ferrers shape も exact に一致する。

すなわち、屋根 `β` と幅 `m` を固定したとき、canonical length 列は
rank-envelope Young/Ferrers 図形の完全な符号である。
-/
theorem rankFerrersShape_eq_of_canonicalRecordLengths_eq
    {β : ℕ → ℕ}
    {m : ℕ}
    (R S : RecordFerrers β m)
    (hCode :
      canonicalRecordLengths β m R.height =
        canonicalRecordLengths β m S.height) :
    R.rankFerrersShape = S.rankFerrersShape := by
  unfold rankFerrersShape
  rw [hCode]

/-- 同じ内容を「完全符号」として読む公開 wrapper。 -/
theorem canonicalRecordLengths_complete_for_rankFerrersShape
    {β : ℕ → ℕ}
    {m : ℕ}
    (R S : RecordFerrers β m)
    (hCode :
      canonicalRecordLengths β m R.height =
        canonicalRecordLengths β m S.height) :
    R.rankFerrersShape = S.rankFerrersShape :=
  R.rankFerrersShape_eq_of_canonicalRecordLengths_eq S hCode

end RecordFerrers

end GenericRecordFerrers
end Experimental2
end Collatz3
