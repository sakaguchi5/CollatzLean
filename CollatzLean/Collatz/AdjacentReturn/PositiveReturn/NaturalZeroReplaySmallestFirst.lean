import CollatzLean.Collatz.AdjacentReturn.PositiveReturn.NaturalZeroReplayArithmetic
import CollatzLean.Collatz.Word.SuffixExponentBound
import CollatzLean.Collatz.Canonical.PrependOneCoreZeroObstruction

/-!
# natural j=0 packet から smallest-first obstruction を抽出する

natural predecessor 自身が `FirstCrossing` であることは一般には従わない。
しかし internal descent を排除する必要もない。

contracting word の actual replay が positive return なら、
canonical level 0 の return はさらに大きいので canonical positive である。
従って all-suffix-contracting な canonical-positive word `w` について
最初の `FirstCrossing` prefix `u` を取ると、次の二つしかない。

* `u` の actual endpoint が現在 start より上なら、`u` 自身が canonical positive。
* endpoint が start 以下なら、残り suffix は actual positive となる。
  その suffix は contracting なので canonical positive であり、しかも word length が短い。

後者を length に関して繰り返せば必ず前者へ到達する。
これにより internal descent exclusion を仮定せず、
`SmallestFirstParadoxicalExactObstruction` を直接抽出できる。
-/

namespace Collatz
namespace Word

/--
contracting word の actual replay が strict positive return なら、
canonical level 0 も strict positive return。

contracting replay では replay level を一段上げるごとに
start-end gap が `2 * contractingGap` だけ悪化するため、
上の level でまだ positive なら canonical level は必ず positive。
-/
theorem Contracting.canonicalStart_lt_canonicalEnd_of_runs_positive
    {w : Collatz.Word} {x y : ℕ}
    (hC : w.Contracting)
    (hne : w ≠ [])
    (hrun : Runs w x y)
    (hxy : x < y) :
    w.canonicalStart < w.canonicalEnd := by
  let C : ReplayCoordinate w x y :=
    ReplayCoordinate.ofRuns hrun hne
  have hReplayPositive :
      w.canonicalStart + w.residueModulus * C.quotient <
        w.canonicalEnd + 2 * 3 ^ w.oddSteps * C.quotient := by
    rw [← C.start_eq, ← C.finish_eq]
    exact hxy
  have hBalance := hC.replayGap_balance C.quotient
  omega

/--
canonical-positive な valid `FirstCrossing` は、
そのまま `SmallestFirstParadoxicalExactObstruction` を与える。
-/
theorem FirstCrossing.to_smallestFirstParadoxicalExactObstruction_of_positive
    {w : Collatz.Word}
    (hF : w.FirstCrossing)
    (hvalid : w.Valid)
    (hpos : w.canonicalStart < w.canonicalEnd) :
    SmallestFirstParadoxicalExactObstruction w := by
  have hproper :
      ∀ (m y : ℕ),
        0 < m →
        m < w.length →
        Runs (w.take m) w.canonicalStart y →
          w.canonicalStart < y := by
    intro m y hmPos hmLt hrun
    exact
      hF.canonicalStart_lt_properPrefixBoundary
        hvalid hmPos hmLt hrun
  have hexact :=
    canonicalPositiveReturn_exactObstruction
      hvalid hF.terminalContracting hpos
  exact {
    valid := hvalid
    firstCrossing := hF
    allSuffixesContracting := hF.allSuffixesContracting
    positiveReturn := hpos
    properBoundaryAboveStart := hproper
    exactReturn := hexact
  }

/--
valid・nonempty・all-suffix-contracting・canonical-positive な有限語には、
canonical-positive `FirstCrossing` subword が存在し、従って
`SmallestFirstParadoxicalExactObstruction` が存在する。

最初の `FirstCrossing` prefix が current start 以下へ落ちる場合は、
残り suffix が strict actual positive return になる。
その suffix は contracting なので canonical-positive であり、
長さが真に短い。これを strong induction で繰り返す。
-/
theorem exists_smallestFirstParadoxicalExactObstruction_of_positive_allSuffixesContracting
    {w : Collatz.Word}
    (hvalid : w.Valid)
    (hne : w ≠ [])
    (hAll : w.AllSuffixesContracting)
    (hpos : w.canonicalStart < w.canonicalEnd) :
    ∃ u : Collatz.Word,
      SmallestFirstParadoxicalExactObstruction u := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ z : Collatz.Word,
      z.length = n →
      z.Valid →
      z ≠ [] →
      z.AllSuffixesContracting →
      z.canonicalStart < z.canonicalEnd →
      ∃ u : Collatz.Word,
        SmallestFirstParadoxicalExactObstruction u
  have hP : ∀ n : ℕ, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        dsimp [P]
        intro z hzLen hzValid hzNe hzAll hzPos
        have hzC : z.Contracting :=
          hzAll.whole hzNe
        obtain ⟨p, hpLe, hFirstRaw⟩ :=
          exists_firstCrossing_of_contracting
            hzValid hzNe hzC
        let u := z.take p
        let v := z.drop p
        have hFirst : FirstCrossing u := by
          simpa [u] using hFirstRaw
        have hdecomp : u ++ v = z := by
          simp only [List.take_append_drop, u, v]
        have hcanonicalUV :
            Runs (u ++ v) z.canonicalStart z.canonicalEnd := by
          rw [hdecomp]
          exact hzValid.canonicalRuns
        obtain ⟨y, huRun, hvRun⟩ :=
          hcanonicalUV.split_append
        by_cases hPrefixPositive : z.canonicalStart < y
        · have huPositive :
              canonicalStart u < canonicalEnd u :=
            Contracting.canonicalStart_lt_canonicalEnd_of_runs_positive
              hFirst.terminalContracting
              hFirst.nonempty
              huRun
              hPrefixPositive
          exact
            ⟨u,
              hFirst.to_smallestFirstParadoxicalExactObstruction_of_positive
                huRun.valid huPositive⟩
        · have hyLe : y ≤ z.canonicalStart :=
            Nat.le_of_not_gt hPrefixPositive
          have hyEnd : y < z.canonicalEnd :=
            lt_of_le_of_lt hyLe hzPos
          have hpLt : p < z.length := by
            by_contra hnot
            have hpEq : p = z.length := by
              omega
            have hvNil : v = [] := by
              dsimp [v]
              simp [hpEq]
            rw [hvNil] at hvRun
            cases hvRun
            omega
          have hvNe : v ≠ [] := by
            apply List.ne_nil_of_length_pos
            dsimp [v]
            simp
            omega
          have hvAll : AllSuffixesContracting v := by
            simpa [v] using hzAll.drop p
          have hvC : Contracting v :=
            hvAll.whole hvNe
          have hvPositive :
              canonicalStart v < canonicalEnd v :=
            hvC.canonicalStart_lt_canonicalEnd_of_runs_positive
              hvNe hvRun hyEnd
          have hpPos : 0 < p := by
            by_contra hnot
            have hpZero : p = 0 := by
              omega
            have huNil : u = [] := by
              simp [u, hpZero]
            exact hFirst.nonempty huNil
          have hvLenEq :
              v.length = z.length - p := by
            simp [v]
          have hvLenLtZ : v.length < z.length := by
            rw [hvLenEq]
            omega
          have hvLenLtN : v.length < n := by
            calc
              v.length < z.length := hvLenLtZ
              _ = n := hzLen
          have hrec := ih v.length hvLenLtN
          dsimp [P] at hrec
          exact
            hrec
              v
              rfl
              hvRun.valid
              hvNe
              hvAll
              hvPositive
  have hfinal := hP w.length
  dsimp [P] at hfinal
  exact hfinal w rfl hvalid hne hAll hpos

/--
smallest-first paradoxical obstruction は必ず `1 :: v` 形で、tail は非空。

長さ1なら contracting single step が canonical positive return することになり、
`2^e > 3` と one-step equation に矛盾する。
長さ2以上なら既存 `FirstCrossing.head_eq_one_of_cons_tail` を使う。
-/
theorem SmallestFirstParadoxicalExactObstruction.exists_prependOne_form
    {w : Collatz.Word}
    (O : SmallestFirstParadoxicalExactObstruction w) :
    ∃ v : Collatz.Word,
      v ≠ [] ∧
      w = 1 :: v := by
  cases w with
  | nil =>
      exact False.elim (O.firstCrossing.nonempty rfl)
  | cons e v =>
      have hvNe : v ≠ [] := by
        intro hv
        subst v
        have hC :
            Word.Contracting ([e] : Collatz.Word) :=
          O.firstCrossing.terminalContracting
        have hpow : 4 ≤ 2 ^ e := by
          have hthree : 3 < 2 ^ e := by
            simpa [Word.Contracting, Word.oddSteps, Word.twoSteps] using hC
          omega
        have hreal :=
          Word.canonicalEnd_realizes ([e] : Collatz.Word)
        have hrealOne :
            2 ^ e * Word.canonicalEnd ([e] : Collatz.Word) =
              3 * Word.canonicalStart ([e] : Collatz.Word) + 1 := by
          simpa [
            Word.Realizes,
            Word.oddSteps,
            Word.twoSteps,
            Word.affineConst
          ] using hreal
        have hscaled :
            4 * Word.canonicalEnd ([e] : Collatz.Word) ≤
              2 ^ e * Word.canonicalEnd ([e] : Collatz.Word) :=
          Nat.mul_le_mul_right
            (Word.canonicalEnd ([e] : Collatz.Word)) hpow
        rw [hrealOne] at hscaled
        have hpos :
            Word.canonicalStart ([e] : Collatz.Word) <
              Word.canonicalEnd ([e] : Collatz.Word) :=
          O.positiveReturn
        omega
      have he : e = 1 :=
        FirstCrossing.head_eq_one_of_cons_tail
          O.valid O.firstCrossing hvNe
      subst e
      exact ⟨v, hvNe, rfl⟩

end Word

namespace AdjacentReturn
namespace PositiveReturn
namespace FirstCrossingData.NaturalZeroReplaySignChangeData

/-- natural predecessor word は非空。 -/
theorem predecessor_nonempty
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    D.predecessorWord ≠ [] := by
  rw [D.predecessorWord_eq_cons_tailWord]
  simp

/-- natural predecessor word は valid。 -/
theorem predecessor_valid
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    Word.Valid D.predecessorWord := by
  rw [D.predecessorWord_eq_cons_tailWord]
  intro e he
  simp only [List.mem_cons] at he
  rcases he with rfl | he
  · omega
  · exact D.tail_valid e he

/--
natural j=0 sign-change packet から、internal descent を排除する仮定なしに
smallest-first paradoxical exact obstruction を抽出する。

内部 first-crossing が現在 start 以下へ落ちた場合は、
残り contracting suffix へ移ることで有限長が真に減少する。
-/
theorem exists_smallestFirstParadoxicalExactObstruction
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    ∃ u : Collatz.Word,
      Word.SmallestFirstParadoxicalExactObstruction u := by
  have hpos :
      Word.canonicalStart D.predecessorWord <
        Word.canonicalEnd D.predecessorWord := by
    simpa [predecessorWord] using D.predecessor_positive
  exact
    Word.exists_smallestFirstParadoxicalExactObstruction_of_positive_allSuffixesContracting
      D.predecessor_valid
      D.predecessor_nonempty
      D.predecessor_allSuffixesContracting
      hpos

/--
さらに抽出される obstruction は `1 :: v` 形に取れ、tail は非空。
これで既存 prepend-one / near-resonance 系の有限語対象へ戻せる。
-/
theorem exists_prependOne_smallestFirstParadoxicalExactObstruction
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    ∃ v : Collatz.Word,
      v ≠ [] ∧
      Word.SmallestFirstParadoxicalExactObstruction (1 :: v) := by
  obtain ⟨u, hObs⟩ :=
    D.exists_smallestFirstParadoxicalExactObstruction
  obtain ⟨v, hvNe, hu⟩ :=
    hObs.exists_prependOne_form
  rw [hu] at hObs
  exact ⟨v, hvNe, hObs⟩

end FirstCrossingData.NaturalZeroReplaySignChangeData
end PositiveReturn
end AdjacentReturn
end Collatz
