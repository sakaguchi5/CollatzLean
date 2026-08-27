import CollatzLean.Collatz2.RecordFerrers.Perturbation.P32CanonicalDeletionConfluence
import CollatzLean.Collatz2.RecordFerrers.Lattice.AffineValuationTransport

/-!
# Record–Ferrers 摂動理論 33: Boolean 境界順序の Ferrers 幾何への埋め込み

P31 では内部 Record 境界の保持 pattern 上に Boolean 順序を構成し、
P32 では境界削除の可換性を標準平坦代表の FiberPoint equality へ持ち上げた。

本ファイルでは、P30 の標準平坦代表がこの Boolean 順序を Ferrers inclusion として
exact に実現することを示す。

粗視化後の「第何境界か」は追跡しない。代わりに length skeleton から実 cut 座標列を取り出し、
Bool 列による粗視化が source cut 座標の選択そのものであることを証明する。
各 column の平坦 excess は、その column 以前で最後に保持された cut の
`criticalExcess` として読める。

主結果は次の二点。

* `R.Le S` と、標準平坦代表の Ferrers inclusion は同値。
* Boolean join の標準平坦代表は、ambient Ferrers join と exact に一致する。

したがって P30 の標準平坦 family は Boolean 順序を忠実に実現し、
ambient Ferrers lattice の join に閉じた family になる。
meet 保存はここでは主張しない。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-! ## 1. length skeleton の実 cut 座標 -/

/--
`start` から始まる length skeleton の内部 cut 座標列。
最後の terminal cut は含めない。
-/
def skeletonInternalCuts (start : ℕ) : List ℕ → List ℕ
  | [] => []
  | [_] => []
  | r :: s :: rest =>
      (start + r) :: skeletonInternalCuts (start + r) (s :: rest)

@[simp] theorem skeletonInternalCuts_nil (start : ℕ) :
    skeletonInternalCuts start [] = [] := rfl

@[simp] theorem skeletonInternalCuts_singleton (start r : ℕ) :
    skeletonInternalCuts start [r] = [] := rfl

/-- 内部 cut の個数は block 数より一つ少ない。 -/
theorem skeletonInternalCuts_length
    (start : ℕ)
    (lengths : List ℕ) :
    (skeletonInternalCuts start lengths).length = lengths.length - 1 := by
  induction lengths generalizing start with
  | nil => simp [skeletonInternalCuts]
  | cons r rest ih =>
      cases rest with
      | nil => simp [skeletonInternalCuts]
      | cons s tail =>
          simp only [skeletonInternalCuts, List.length_cons]
          rw [ih (start + r)]
          simp

/--
cut 座標列が `anchor` より右へ strict に増えていくことを表す。
-/
def CutsIncreasingFrom (anchor : ℕ) : List ℕ → Prop
  | [] => True
  | c :: cs => anchor < c ∧ CutsIncreasingFrom c cs

/-- 左端を下げても increasing 性は保たれる。 -/
theorem CutsIncreasingFrom.weaken
    {a b : ℕ}
    {cuts : List ℕ}
    (hab : a ≤ b)
    (h : CutsIncreasingFrom b cuts) :
    CutsIncreasingFrom a cuts := by
  induction cuts generalizing a b with
  | nil => trivial
  | cons c cs ih =>
      simp only [CutsIncreasingFrom] at h ⊢
      exact ⟨lt_of_le_of_lt hab h.1, h.2⟩

/-- increasing cut 列の全要素は最初の anchor より右にある。 -/
theorem CutsIncreasingFrom.all_gt
    {anchor : ℕ}
    {cuts : List ℕ}
    (h : CutsIncreasingFrom anchor cuts) :
    ∀ c ∈ cuts, anchor < c := by
  induction cuts generalizing anchor with
  | nil =>
      intro c hc
      simp at hc
  | cons d ds ih =>
      simp only [CutsIncreasingFrom] at h
      intro c hc
      simp only [List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact h.1
      · exact lt_trans h.1 (ih h.2 c hc)

/-- positive length skeleton の内部 cut は strict に増える。 -/
theorem skeletonInternalCuts_increasing
    (start : ℕ)
    {lengths : List ℕ}
    (hPos : ∀ r ∈ lengths, 0 < r) :
    CutsIncreasingFrom start (skeletonInternalCuts start lengths) := by
  induction lengths generalizing start with
  | nil => trivial
  | cons r rest ih =>
      cases rest with
      | nil => trivial
      | cons s tail =>
          have hrPos : 0 < r := hPos r (by simp)
          have hRestPos : ∀ x ∈ (s :: tail), 0 < x := by
            intro x hx
            exact hPos x (by simp [hx])
          simp only [skeletonInternalCuts, CutsIncreasingFrom]
          exact ⟨by omega, ih (start + r) hRestPos⟩

/-! ## 2. Bool 列で cut 座標を選ぶ -/

/-- Bool 列の `true` の位置だけ cut 座標を残す。 -/
def selectCutsByFlags : List ℕ → List Bool → List ℕ
  | [], _ => []
  | _ :: _, [] => []
  | c :: cs, b :: bs =>
      if b then c :: selectCutsByFlags cs bs
      else selectCutsByFlags cs bs

/-- 選択後の cut も元 anchor より右にある。 -/
theorem selectCutsByFlags_all_gt
    {anchor : ℕ}
    {cuts : List ℕ}
    (hInc : CutsIncreasingFrom anchor cuts)
    (flags : List Bool) :
    ∀ c ∈ selectCutsByFlags cuts flags, anchor < c := by
  intro c hc
  induction cuts generalizing anchor flags with
  | nil =>
      simp [selectCutsByFlags] at hc
  | cons d ds ih =>
      cases flags with
      | nil => simp [selectCutsByFlags] at hc
      | cons b bs =>
          simp only [CutsIncreasingFrom] at hInc
          cases b with
          | false =>
              simp only [selectCutsByFlags, Bool.false_eq_true, ite_false] at hc
              exact lt_trans hInc.1 (ih hInc.2 bs hc)
          | true =>
              simp only [selectCutsByFlags, ite_true, List.mem_cons] at hc
              rcases hc with rfl | hc
              · exact hInc.1
              · exact lt_trans hInc.1 (ih hInc.2 bs hc)

/-- 先頭 length を後ろへ吸収しても、それより後ろの内部 cut 座標は変わらない。 -/
theorem skeletonInternalCuts_mergeHeadLength
    (start r : ℕ)
    {xs : List ℕ}
    (hxs : xs ≠ []) :
    skeletonInternalCuts start (mergeHeadLength r xs) =
      skeletonInternalCuts (start + r) xs := by
  cases xs with
  | nil => exact (hxs rfl).elim
  | cons s rest =>
      cases rest with
      | nil => simp [mergeHeadLength, skeletonInternalCuts]
      | cons t tail =>
          simp [mergeHeadLength, skeletonInternalCuts, Nat.add_assoc]

/-- nonempty tail を先頭に付けたとき、最初の内部 cut を一つ追加する。 -/
theorem skeletonInternalCuts_cons_of_nonempty
    (start r : ℕ)
    {xs : List ℕ}
    (hxs : xs ≠ []) :
    skeletonInternalCuts start (r :: xs) =
      (start + r) :: skeletonInternalCuts (start + r) xs := by
  cases xs with
  | nil => exact (hxs rfl).elim
  | cons s rest => rfl

/--
Bool 粗視化後の内部 cut 座標列は、source の内部 cut 座標から
`true` の位置だけを選んだものと exact に一致する。
-/
theorem skeletonInternalCuts_coarsenByFlags
    (start : ℕ)
    (lengths : List ℕ)
    (flags : List Bool)
    (hFlags : flags.length = lengths.length - 1) :
    skeletonInternalCuts start (coarsenByFlags lengths flags) =
      selectCutsByFlags (skeletonInternalCuts start lengths) flags := by
  induction lengths generalizing start flags with
  | nil =>
      have hNil : flags = [] := by
        apply List.eq_nil_of_length_eq_zero
        simpa using hFlags
      subst flags
      simp [coarsenByFlags, skeletonInternalCuts, selectCutsByFlags]
  | cons r rest ih =>
      cases rest with
      | nil =>
          have hNil : flags = [] := by
            apply List.eq_nil_of_length_eq_zero
            simpa using hFlags
          subst flags
          simp [coarsenByFlags, skeletonInternalCuts, selectCutsByFlags]
      | cons s tail =>
          cases flags with
          | nil =>
              simp only [List.length_nil, List.length_cons] at hFlags
              omega
          | cons b bs =>
              have hBs : bs.length = (s :: tail).length - 1 := by
                simp only [List.length_cons] at hFlags ⊢
                omega
              have hIH := ih (start + r) bs hBs
              have hTailNe :
                  coarsenByFlags (s :: tail) bs ≠ [] :=
                coarsenByFlags_nonempty (by simp) bs
              cases b with
              | true =>
                  rw [coarsenByFlags_cons_true r (by simp : (s :: tail) ≠ []) bs]
                  rw [skeletonInternalCuts_cons_of_nonempty
                    start r hTailNe]
                  simp only [skeletonInternalCuts, selectCutsByFlags, ite_true]
                  rw [hIH]
              | false =>
                  rw [coarsenByFlags_cons_false r (by simp : (s :: tail) ≠ []) bs]
                  rw [skeletonInternalCuts_mergeHeadLength
                    start r hTailNe]
                  simp only [skeletonInternalCuts, selectCutsByFlags,
                    Bool.false_eq_true, ite_false]
                  exact hIH

/-! ## 3. ある column 以前で最後に残った cut -/

/--
`j` 以下に現れる最後の cut 座標。該当 cut がなければ `anchor`。
cut 列を最後まで走査するため、選択済み部分列との相性がよい。
-/
def lastCutAt (anchor j : ℕ) : List ℕ → ℕ
  | [] => anchor
  | c :: cs =>
      if c ≤ j then lastCutAt c j cs
      else lastCutAt anchor j cs

/-- 全 cut が `j` より右なら最後の cut は元 anchor のまま。 -/
theorem lastCutAt_eq_anchor_of_all_gt
    (anchor j : ℕ)
    {cuts : List ℕ}
    (h : ∀ c ∈ cuts, j < c) :
    lastCutAt anchor j cuts = anchor := by
  induction cuts generalizing anchor with
  | nil => rfl
  | cons c cs ih =>
      have hc : j < c := h c (by simp)
      have hcs : ∀ d ∈ cs, j < d := by
        intro d hd
        exact h d (by simp [hd])
      simp only [lastCutAt, ite_eq_right (not_le.mpr hc)]
      exact ih anchor hcs

/--
平坦 skeleton の excess は、その column 以前で最後に現れた内部 cut の
critical excess である。
-/
theorem flatExcessForSkeleton_eq_lastCut
    (start : ℕ)
    {lengths : List ℕ}
    (hPos : ∀ r ∈ lengths, 0 < r)
    {j : ℕ}
    (hsj : start ≤ j)
    (hjEnd : j < start + lengths.sum) :
    flatExcessForSkeleton start lengths j =
      criticalExcess
        (lastCutAt start j (skeletonInternalCuts start lengths)) := by
  induction lengths generalizing start j with
  | nil =>
      simp only [List.sum_nil, Nat.add_zero] at hjEnd
      omega
  | cons r rest ih =>
      have hrPos : 0 < r := hPos r (by simp)
      cases rest with
      | nil =>
          have hjHead : j < start + r := by
            simpa using hjEnd
          rw [flatExcessForSkeleton_of_head start r [] hsj hjHead]
          simp [skeletonInternalCuts, lastCutAt]
      | cons s tail =>
          have hRestPos : ∀ x ∈ (s :: tail), 0 < x := by
            intro x hx
            exact hPos x (by simp [hx])
          by_cases hjHead : j < start + r
          · rw [flatExcessForSkeleton_of_head
              start r (s :: tail) hsj hjHead]
            have hIncTail :=
              skeletonInternalCuts_increasing
                (start + r) hRestPos
            have hAll :
                ∀ c ∈ skeletonInternalCuts (start + r) (s :: tail),
                  j < c := by
              intro c hc
              have hGt := CutsIncreasingFrom.all_gt hIncTail c hc
              exact lt_trans hjHead hGt
            simp only [skeletonInternalCuts, lastCutAt,
              ite_eq_right (not_le.mpr hjHead)]
            rw [lastCutAt_eq_anchor_of_all_gt
              start j hAll]
          · have hHeadLe : start + r ≤ j := by omega
            rw [flatExcessForSkeleton_of_after_head
              start r (s :: tail) hHeadLe]
            simp only [skeletonInternalCuts, lastCutAt,
              ite_eq_left hHeadLe]
            apply ih (start + r) hRestPos hHeadLe
            simp only [List.sum_cons] at hjEnd ⊢
            omega

/-- source length の先頭吸収は総和を保つ。 -/
theorem mergeHeadLength_sum
    (r : ℕ)
    (xs : List ℕ) :
    (mergeHeadLength r xs).sum = r + xs.sum := by
  cases xs <;> simp [mergeHeadLength, Nat.add_assoc]

/-- Bool 粗視化は length の総和を保つ。 -/
theorem coarsenByFlags_sum
    (lengths : List ℕ)
    (flags : List Bool) :
    (coarsenByFlags lengths flags).sum = lengths.sum := by
  induction lengths generalizing flags with
  | nil => simp [coarsenByFlags]
  | cons r rest ih =>
      cases rest with
      | nil => simp [coarsenByFlags]
      | cons s tail =>
          cases flags with
          | nil => simp [coarsenByFlags]
          | cons b bs =>
              cases b with
              | true =>
                  simp only [coarsenByFlags, List.sum_cons]
                  rw [ih bs]
                  simp
              | false =>
                  simp only [coarsenByFlags]
                  rw [mergeHeadLength_sum]
                  rw [ih bs]
                  simp only [List.sum_cons]

/--
P30 標準平坦代表の正の proper cut における excess を、
source cut の保持 pattern だけで読む。
-/
theorem canonicalFlatRepresentative_excessAt_eq_lastRetainedCut
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    {j : ℕ}
    (hjPos : 0 < j)
    (hjp : j < P.oddCount) :
    (canonicalFlatPoint P hPrimitive hReduced u D R).excessAt j =
      criticalExcess
        (lastCutAt 1 j
          (selectCutsByFlags
            (skeletonInternalCuts 1 D.lengths)
            (retainedFlags R))) := by
  unfold canonicalFlatPoint
  rw [canonicalFlatRepresentative_excessAt
    P hPrimitive hReduced u D R hjp]
  have hj1 : 1 ≤ j := by omega
  have hPos :
      ∀ r ∈ coarsenedLengthsFor D R, 0 < r := by
    unfold coarsenedLengthsFor
    exact coarsenByFlags_all_pos (retainedFlags R) D.lengths_pos
  have hEndSource := D.chain.start_add_sum_eq_terminal
  have hEnd :
      1 + (coarsenedLengthsFor D R).sum = P.oddCount := by
    unfold coarsenedLengthsFor
    rw [coarsenByFlags_sum]
    exact hEndSource
  rw [flatExcessForSkeleton_eq_lastCut 1 hPos hj1 (by omega)]
  unfold coarsenedLengthsFor
  rw [skeletonInternalCuts_coarsenByFlags
    1 D.lengths (retainedFlags R) (retainedFlags_length R)]

/-! ## 4. Bool 列の包含と join -/

/-- Bool 列の pointwise 包含。 -/
def BoolListLe : List Bool → List Bool → Prop
  | [], [] => True
  | a :: as, b :: bs => (a = true → b = true) ∧ BoolListLe as bs
  | _, _ => False

/-- 三本目が前二本の pointwise OR であること。 -/
def BoolListJoin : List Bool → List Bool → List Bool → Prop
  | [], [], [] => True
  | a :: as, b :: bs, c :: cs =>
      c = (a || b) ∧ BoolListJoin as bs cs
  | _, _, _ => False

/-- function 上の Boolean 包含は `List.ofFn` 上の包含へ移る。 -/
theorem boolListLe_ofFn :
    ∀ (n : ℕ) (R S : Fin n → Bool),
      (∀ i, R i = true → S i = true) →
      BoolListLe (List.ofFn R) (List.ofFn S) := by
  intro n
  induction n with
  | zero =>
      intro R S h
      simp [BoolListLe]
  | succ n ih =>
      intro R S h
      rw [List.ofFn_succ, List.ofFn_succ]
      simp only [BoolListLe]
      constructor
      · exact h 0
      · apply ih
        intro i hi
        exact h i.succ hi

/-- `List.ofFn` は pointwise OR を Bool 列の join として読む。 -/
theorem boolListJoin_ofFn :
    ∀ (n : ℕ) (R S : Fin n → Bool),
      BoolListJoin
        (List.ofFn R)
        (List.ofFn S)
        (List.ofFn (fun i => R i || S i)) := by
  intro n
  induction n with
  | zero =>
      intro R S
      simp [BoolListJoin]
  | succ n ih =>
      intro R S
      rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ]
      simp only [BoolListJoin]
      exact ⟨True.intro, ih (fun i => R i.succ) (fun i => S i.succ)⟩

/-- pattern 包含は retained Bool 列の包含になる。 -/
theorem retainedFlags_le
    {p H : ℕ}
    {u : FiberPoint p H}
    {D : RecordDecomposition u 1}
    {R S : RetainedBoundaryPattern D}
    (hRS : R.Le S) :
    BoolListLe (retainedFlags R) (retainedFlags S) := by
  unfold retainedFlags
  exact boolListLe_ofFn _ R S hRS

/-- retainedJoin の Bool 列は pointwise OR。 -/
theorem retainedFlags_join
    {p H : ℕ}
    {u : FiberPoint p H}
    {D : RecordDecomposition u 1}
    (R S : RetainedBoundaryPattern D) :
    BoolListJoin
      (retainedFlags R)
      (retainedFlags S)
      (retainedFlags (retainedJoin R S)) := by
  unfold retainedFlags retainedJoin
  exact boolListJoin_ofFn _ R S

/-! ## 5. 最後に残る cut の単調性と join -/

/--
同じ increasing cut 列で Bool 列を増やすと、最後に残る cut は右へしか動かない。
-/
theorem lastCutAt_select_mono
    {a b j : ℕ}
    {cuts : List ℕ}
    {f g : List Bool}
    (hab : a ≤ b)
    (hInc : CutsIncreasingFrom b cuts)
    (hf : f.length = cuts.length)
    (hg : g.length = cuts.length)
    (hfg : BoolListLe f g) :
    lastCutAt a j (selectCutsByFlags cuts f) ≤
      lastCutAt b j (selectCutsByFlags cuts g) := by
  induction cuts generalizing a b f g with
  | nil =>
      have hf0 : f = [] := List.eq_nil_of_length_eq_zero (by simpa using hf)
      have hg0 : g = [] := List.eq_nil_of_length_eq_zero (by simpa using hg)
      subst f
      subst g
      simpa [selectCutsByFlags, lastCutAt] using hab
  | cons c cs ih =>
      cases f with
      | nil => simp at hf
      | cons rf rs =>
          cases g with
          | nil => simp at hg
          | cons sf ss =>
              simp only [List.length_cons] at hf hg
              have hrsLen : rs.length = cs.length := by omega
              have hssLen : ss.length = cs.length := by omega
              simp only [BoolListLe] at hfg
              simp only [CutsIncreasingFrom] at hInc
              have hIncB : CutsIncreasingFrom b cs :=
                CutsIncreasingFrom.weaken (Nat.le_of_lt hInc.1) hInc.2
              by_cases hcj : c ≤ j
              · cases rf <;> cases sf
                · simp only [selectCutsByFlags, Bool.false_eq_true, ite_false]
                  exact ih hab hIncB hrsLen hssLen hfg.2
                · simp only [selectCutsByFlags, Bool.false_eq_true, ite_false,
                    ite_true, lastCutAt, ite_eq_left hcj]
                  exact ih (by omega) hInc.2 hrsLen hssLen hfg.2
                · exfalso
                  have := hfg.1 rfl
                  simp at this
                · simp only [selectCutsByFlags, ite_true, lastCutAt, ite_eq_left hcj]
                  exact ih le_rfl hInc.2 hrsLen hssLen hfg.2
              · have hjc : j < c := by omega
                cases rf <;> cases sf <;>
                  simp only [selectCutsByFlags, Bool.false_eq_true, ite_false,
                    ite_true, lastCutAt, ite_eq_right hcj]
                · exact ih hab hIncB hrsLen hssLen hfg.2
                · exact ih hab hIncB hrsLen hssLen hfg.2
                · exfalso
                  have := hfg.1 rfl
                  simp at this
                · exact ih hab hIncB hrsLen hssLen hfg.2

/-- critical excess は max と可換。 -/
theorem criticalExcess_max (a b : ℕ) :
    criticalExcess (max a b) =
      max (criticalExcess a) (criticalExcess b) := by
  rcases le_total a b with hab | hba
  · rw [max_eq_right hab, max_eq_right (criticalExcess_mono hab)]
  · rw [max_eq_left hba, max_eq_left (criticalExcess_mono hba)]

/--
pointwise OR で cut を残すと、最後に残る cut は二つの last cut の max になる。
-/
theorem lastCutAt_select_join
    {a b m j : ℕ}
    {cuts : List ℕ}
    {f g h : List Bool}
    (hm : m = max a b)
    (hInc : CutsIncreasingFrom m cuts)
    (hf : f.length = cuts.length)
    (hg : g.length = cuts.length)
    (hh : h.length = cuts.length)
    (hJoin : BoolListJoin f g h) :
    lastCutAt m j (selectCutsByFlags cuts h) =
      max
        (lastCutAt a j (selectCutsByFlags cuts f))
        (lastCutAt b j (selectCutsByFlags cuts g)) := by
  subst m
  induction cuts generalizing a b f g h with
  | nil =>
      have hf0 : f = [] := List.eq_nil_of_length_eq_zero (by simpa using hf)
      have hg0 : g = [] := List.eq_nil_of_length_eq_zero (by simpa using hg)
      have hh0 : h = [] := List.eq_nil_of_length_eq_zero (by simpa using hh)
      subst f
      subst g
      subst h
      simp [selectCutsByFlags, lastCutAt]
  | cons c cs ih =>
      cases f with
      | nil => simp at hf
      | cons rf rs =>
          cases g with
          | nil => simp at hg
          | cons sf ss =>
              cases h with
              | nil => simp at hh
              | cons tf ts =>
                  simp only [List.length_cons] at hf hg hh
                  have hrsLen : rs.length = cs.length := by
                    omega
                  have hssLen : ss.length = cs.length := by
                    omega
                  have htsLen : ts.length = cs.length := by
                    omega
                  simp only [BoolListJoin] at hJoin
                  simp only [CutsIncreasingFrom] at hInc
                  /-
                  帰納仮定の引数順をここで一度だけ吸収する。
                  以下の各 Boolean case では anchor だけ指定すればよい。
                  -/
                  have hTailJoin
                      (a' b' : ℕ)
                      (hInc' : CutsIncreasingFrom (max a' b') cs) :
                      lastCutAt (max a' b') j
                          (selectCutsByFlags cs ts) =
                        max
                          (lastCutAt a' j
                            (selectCutsByFlags cs rs))
                          (lastCutAt b' j
                            (selectCutsByFlags cs ss)) := by
                    apply ih
                      (a := a')
                      (b := b')
                      (f := rs)
                      (g := ss)
                      (h := ts)
                        hrsLen
                        hssLen
                        htsLen
                        hJoin.2
                        hInc'
                  /-
                  元の anchor `max a b` のまま tail へ降りる場合に使う increasing 性。
                  -/
                  have hTailIncMax :
                      CutsIncreasingFrom (max a b) cs :=
                    CutsIncreasingFrom.weaken
                      (Nat.le_of_lt hInc.1)
                      hInc.2
                  by_cases hcj : c ≤ j
                  · /- c が j 以前：c を保持した側では last cut が c へ進む。 -/
                    cases rf <;> cases sf
                    · /- false / false -/
                      have htf : tf = false := by
                        simpa using hJoin.1
                      subst tf
                      simp only [
                        selectCutsByFlags,
                        Bool.false_eq_true,
                        ite_false
                      ]
                      exact hTailJoin a b hTailIncMax
                    · /- false / true -/
                      have htt : tf = true := by
                        simpa using hJoin.1
                      subst tf
                      have hac : a < c := by
                        exact
                          lt_of_le_of_lt
                            (le_max_left _ _)
                            hInc.1
                      simp only [
                        selectCutsByFlags,
                        Bool.false_eq_true,
                        ite_false,
                        ite_true,
                        lastCutAt,
                        ite_eq_left hcj
                      ]
                      have hMaxAC : max a c = c :=
                        max_eq_right (Nat.le_of_lt hac)
                      have hIncAC :
                          CutsIncreasingFrom (max a c) cs := by
                        rw [hMaxAC]
                        exact hInc.2
                      simpa [hMaxAC] using
                        hTailJoin a c hIncAC
                    · /- true / false -/
                      have htt : tf = true := by
                        simpa using hJoin.1
                      subst tf
                      have hbc : b < c := by
                        exact
                          lt_of_le_of_lt
                            (le_max_right _ _)
                            hInc.1
                      simp only [
                        selectCutsByFlags,
                        Bool.false_eq_true,
                        ite_false,
                        ite_true,
                        lastCutAt,
                        ite_eq_left hcj
                      ]
                      have hMaxCB : max c b = c :=
                        max_eq_left (Nat.le_of_lt hbc)
                      have hIncCB :
                          CutsIncreasingFrom (max c b) cs := by
                        rw [hMaxCB]
                        exact hInc.2
                      simpa [hMaxCB] using
                        hTailJoin c b hIncCB
                    · /- true / true -/
                      have htt : tf = true := by
                        simpa using hJoin.1
                      subst tf
                      simp only [
                        selectCutsByFlags,
                        ite_true,
                        lastCutAt,
                        ite_eq_left hcj
                      ]
                      have hIncCC :
                          CutsIncreasingFrom (max c c) cs := by
                        simpa using hInc.2
                      simpa using
                        hTailJoin c c hIncCC
                  · /-
                    c > j：
                    c を保持していても `lastCutAt` は c へ進まない。
                    したがって4通りすべて元の anchor `a,b` のまま tail に降りる。
                    -/
                    cases rf <;> cases sf
                    · /- false / false -/
                      have htf : tf = false := by
                        simpa using hJoin.1
                      subst tf
                      simp only [
                        selectCutsByFlags,
                        Bool.false_eq_true,
                        ite_false
                      ]
                      exact hTailJoin a b hTailIncMax
                    · /- false / true -/
                      have htt : tf = true := by
                        simpa using hJoin.1
                      subst tf
                      simp only [
                        selectCutsByFlags,
                        Bool.false_eq_true,
                        ite_false,
                        ite_true,
                        lastCutAt,
                        ite_eq_right hcj
                      ]
                      exact hTailJoin a b hTailIncMax
                    · /- true / false -/
                      have htt : tf = true := by
                        simpa using hJoin.1
                      subst tf
                      simp only [
                        selectCutsByFlags,
                        Bool.false_eq_true,
                        ite_false,
                        ite_true,
                        lastCutAt,
                        ite_eq_right hcj
                      ]
                      exact hTailJoin a b hTailIncMax
                    · /- true / true -/
                      have htt : tf = true := by
                        simpa using hJoin.1
                      subst tf
                      simp only [
                        selectCutsByFlags,
                        ite_true,
                        lastCutAt,
                        ite_eq_right hcj
                      ]
                      exact hTailJoin a b hTailIncMax

/-! ## 6. Boolean 順序 = Ferrers inclusion -/

/-- Boolean 順序は標準平坦代表の Ferrers inclusion を保つ。 -/
theorem canonicalFlatPoint_ferrersLe_of_retainedLe
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {R S : RetainedBoundaryPattern D}
    (hRS : R.Le S) :
    FiberPoint.FerrersLe
      (canonicalFlatPoint P hPrimitive hReduced u D R)
      (canonicalFlatPoint P hPrimitive hReduced u D S) := by
  intro i
  change
    (canonicalFlatPoint P hPrimitive hReduced u D R).excessAt i.1 ≤
      (canonicalFlatPoint P hPrimitive hReduced u D S).excessAt i.1
  by_cases hi0 : i.1 = 0
  · rw [hi0]
    simp
  · have hiPos : 0 < i.1 := Nat.pos_of_ne_zero hi0
    rw [canonicalFlatRepresentative_excessAt_eq_lastRetainedCut
      P hPrimitive hReduced u D R hiPos i.isLt]
    rw [canonicalFlatRepresentative_excessAt_eq_lastRetainedCut
      P hPrimitive hReduced u D S hiPos i.isLt]
    apply criticalExcess_mono
    have hCutsInc :
        CutsIncreasingFrom 1 (skeletonInternalCuts 1 D.lengths) :=
      skeletonInternalCuts_increasing 1 D.lengths_pos
    have hFlagsR :
        (retainedFlags R).length =
          (skeletonInternalCuts 1 D.lengths).length := by
      rw [retainedFlags_length, skeletonInternalCuts_length]
    have hFlagsS :
        (retainedFlags S).length =
          (skeletonInternalCuts 1 D.lengths).length := by
      rw [retainedFlags_length, skeletonInternalCuts_length]
    exact lastCutAt_select_mono
      le_rfl hCutsInc hFlagsR hFlagsS (retainedFlags_le hRS)

/--
Boolean join の標準平坦 profile は ambient Ferrers join と exact に一致する。
-/
theorem canonicalFlatPoint_retainedJoin_shape
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R S : RetainedBoundaryPattern D) :
    (canonicalFlatPoint P hPrimitive hReduced u D
      (retainedJoin R S)).toFerrersShape =
      FerrersShape.join
        (canonicalFlatPoint P hPrimitive hReduced u D R).toFerrersShape
        (canonicalFlatPoint P hPrimitive hReduced u D S).toFerrersShape := by
  apply FerrersShape.ext
  intro i
  change
    (canonicalFlatPoint P hPrimitive hReduced u D
      (retainedJoin R S)).excessAt i.1 =
      max
        ((canonicalFlatPoint P hPrimitive hReduced u D R).excessAt i.1)
        ((canonicalFlatPoint P hPrimitive hReduced u D S).excessAt i.1)
  by_cases hi0 : i.1 = 0
  · rw [hi0]
    simp
  · have hiPos : 0 < i.1 := Nat.pos_of_ne_zero hi0
    rw [canonicalFlatRepresentative_excessAt_eq_lastRetainedCut
      P hPrimitive hReduced u D (retainedJoin R S) hiPos i.isLt]
    rw [canonicalFlatRepresentative_excessAt_eq_lastRetainedCut
      P hPrimitive hReduced u D R hiPos i.isLt]
    rw [canonicalFlatRepresentative_excessAt_eq_lastRetainedCut
      P hPrimitive hReduced u D S hiPos i.isLt]
    rw [← criticalExcess_max]
    congr 1
    have hCutsInc :
        CutsIncreasingFrom 1 (skeletonInternalCuts 1 D.lengths) :=
      skeletonInternalCuts_increasing 1 D.lengths_pos
    have hLenR :
        (retainedFlags R).length =
          (skeletonInternalCuts 1 D.lengths).length := by
      rw [retainedFlags_length, skeletonInternalCuts_length]
    have hLenS :
        (retainedFlags S).length =
          (skeletonInternalCuts 1 D.lengths).length := by
      rw [retainedFlags_length, skeletonInternalCuts_length]
    have hLenJ :
        (retainedFlags (retainedJoin R S)).length =
          (skeletonInternalCuts 1 D.lengths).length := by
      rw [retainedFlags_length, skeletonInternalCuts_length]
    exact lastCutAt_select_join
      (a := 1) (b := 1) (m := 1) (j := i.1)
      (cuts := skeletonInternalCuts 1 D.lengths)
      (f := retainedFlags R)
      (g := retainedFlags S)
      (h := retainedFlags (retainedJoin R S))
      (by simp)
      hCutsInc hLenR hLenS hLenJ (retainedFlags_join R S)

/-- Ferrers inclusion があれば Boolean 境界順序も戻る。 -/
theorem retainedLe_of_canonicalFlatPoint_ferrersLe
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {R S : RetainedBoundaryPattern D}
    (hRS : FiberPoint.FerrersLe
      (canonicalFlatPoint P hPrimitive hReduced u D R)
      (canonicalFlatPoint P hPrimitive hReduced u D S)) :
    R.Le S := by
  have hJoinShape :
      (canonicalFlatPoint P hPrimitive hReduced u D
        (retainedJoin R S)).toFerrersShape =
        (canonicalFlatPoint P hPrimitive hReduced u D S).toFerrersShape := by
    rw [canonicalFlatPoint_retainedJoin_shape
      P hPrimitive hReduced u D R S]
    apply FerrersShape.ext
    intro i
    simp only [FerrersShape.join_column]
    exact max_eq_right (hRS i)
  have hPoint :
      canonicalFlatPoint P hPrimitive hReduced u D (retainedJoin R S) =
        canonicalFlatPoint P hPrimitive hReduced u D S :=
    FiberPoint.toFerrersShape_injective hJoinShape
  have hPattern : retainedJoin R S = S :=
    canonicalFlatPoint_injective
      P hPrimitive hReduced u D hPoint
  have hRJoin := RetainedBoundaryPattern.left_le_join R S
  rw [hPattern] at hRJoin
  exact hRJoin

/--
## 主定理 1: Boolean 境界順序と Ferrers inclusion は exact に同値。
-/
theorem retainedLe_iff_canonicalFlatPoint_ferrersLe
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R S : RetainedBoundaryPattern D) :
    R.Le S ↔
      FiberPoint.FerrersLe
        (canonicalFlatPoint P hPrimitive hReduced u D R)
        (canonicalFlatPoint P hPrimitive hReduced u D S) := by
  constructor
  · exact canonicalFlatPoint_ferrersLe_of_retainedLe
      P hPrimitive hReduced u D
  · exact retainedLe_of_canonicalFlatPoint_ferrersLe
      P hPrimitive hReduced u D

/-- strict Boolean 境界増加は strict Ferrers 増加として見える。 -/
theorem canonicalFlatPoint_strict_of_retained_lt
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {R S : RetainedBoundaryPattern D}
    (hRS : R.Le S)
    (hne : R ≠ S) :
    FiberPoint.FerrersLe
      (canonicalFlatPoint P hPrimitive hReduced u D R)
      (canonicalFlatPoint P hPrimitive hReduced u D S) ∧
    canonicalFlatPoint P hPrimitive hReduced u D R ≠
      canonicalFlatPoint P hPrimitive hReduced u D S := by
  refine ⟨canonicalFlatPoint_ferrersLe_of_retainedLe
    P hPrimitive hReduced u D hRS, ?_⟩
  intro hPoint
  exact hne (canonicalFlatPoint_injective
    P hPrimitive hReduced u D hPoint)

/--
## 主定理 2: Boolean join は ambient Ferrers join として実現される。

これは標準平坦 family が Ferrers join に閉じることを表す。
-/
theorem canonicalFlatPoint_preserves_join
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R S : RetainedBoundaryPattern D) :
    (canonicalFlatPoint P hPrimitive hReduced u D
      (retainedJoin R S)).toFerrersShape =
      FerrersShape.join
        (canonicalFlatPoint P hPrimitive hReduced u D R).toFerrersShape
        (canonicalFlatPoint P hPrimitive hReduced u D S).toFerrersShape :=
  canonicalFlatPoint_retainedJoin_shape
    P hPrimitive hReduced u D R S


/-! ## 7. Boolean meet defect と submodularity -/

/--
Boolean meet の標準平坦代表は、ambient Ferrers meet 以下にある。
P33 では join は exact に保存されるが、meet 側にはこの one-sided defect が残る。
-/
theorem canonicalFlatPoint_retainedMeet_shape_le
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R S : RetainedBoundaryPattern D) :
    FerrersShape.Le
      (canonicalFlatPoint P hPrimitive hReduced u D
        (retainedMeet R S)).toFerrersShape
      (FerrersShape.meet
        (canonicalFlatPoint P hPrimitive hReduced u D R).toFerrersShape
        (canonicalFlatPoint P hPrimitive hReduced u D S).toFerrersShape) := by
  have hR :=
    canonicalFlatPoint_ferrersLe_of_retainedLe
      P hPrimitive hReduced u D
      (RetainedBoundaryPattern.meet_le_left R S)
  have hS :=
    canonicalFlatPoint_ferrersLe_of_retainedLe
      P hPrimitive hReduced u D
      (RetainedBoundaryPattern.meet_le_right R S)
  intro i
  simp only [FerrersShape.meet_column]
  exact le_min (hR i) (hS i)

/--
標準平坦 Boolean family 上の weighted area は submodular。
差は Boolean meet と ambient Ferrers meet のずれだけから生じる。
-/
theorem canonicalFlatPoint_weightedArea_submodular
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R S : RetainedBoundaryPattern D) :
    weightedArea
        (canonicalFlatPoint P hPrimitive hReduced u D
          (retainedMeet R S)).toFerrersShape +
      weightedArea
        (canonicalFlatPoint P hPrimitive hReduced u D
          (retainedJoin R S)).toFerrersShape ≤
    weightedArea
        (canonicalFlatPoint P hPrimitive hReduced u D R).toFerrersShape +
      weightedArea
        (canonicalFlatPoint P hPrimitive hReduced u D S).toFerrersShape := by
  have hMeet :=
    canonicalFlatPoint_retainedMeet_shape_le
      P hPrimitive hReduced u D R S
  have hAreaMeet := weightedArea_mono hMeet
  have hJoin :=
    canonicalFlatPoint_preserves_join
      P hPrimitive hReduced u D R S
  calc
    weightedArea
          (canonicalFlatPoint P hPrimitive hReduced u D
            (retainedMeet R S)).toFerrersShape +
        weightedArea
          (canonicalFlatPoint P hPrimitive hReduced u D
            (retainedJoin R S)).toFerrersShape
        =
      weightedArea
          (canonicalFlatPoint P hPrimitive hReduced u D
            (retainedMeet R S)).toFerrersShape +
        weightedArea
          (FerrersShape.join
            (canonicalFlatPoint P hPrimitive hReduced u D R).toFerrersShape
            (canonicalFlatPoint P hPrimitive hReduced u D S).toFerrersShape) := by
          rw [hJoin]
    _ ≤
      weightedArea
          (FerrersShape.meet
            (canonicalFlatPoint P hPrimitive hReduced u D R).toFerrersShape
            (canonicalFlatPoint P hPrimitive hReduced u D S).toFerrersShape) +
        weightedArea
          (FerrersShape.join
            (canonicalFlatPoint P hPrimitive hReduced u D R).toFerrersShape
            (canonicalFlatPoint P hPrimitive hReduced u D S).toFerrersShape) := by
          exact Nat.add_le_add_right hAreaMeet _
    _ =
      weightedArea
          (canonicalFlatPoint P hPrimitive hReduced u D R).toFerrersShape +
        weightedArea
          (canonicalFlatPoint P hPrimitive hReduced u D S).toFerrersShape := by
          exact weightedArea_meet_add_join _ _

/-- affineConst も同じ Boolean family 上で submodular。 -/
theorem canonicalFlatPoint_affineConst_submodular
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R S : RetainedBoundaryPattern D) :
    affineConst
        (canonicalFlatPoint P hPrimitive hReduced u D
          (retainedMeet R S)).word +
      affineConst
        (canonicalFlatPoint P hPrimitive hReduced u D
          (retainedJoin R S)).word ≤
    affineConst
        (canonicalFlatPoint P hPrimitive hReduced u D R).word +
      affineConst
        (canonicalFlatPoint P hPrimitive hReduced u D S).word := by
  have hArea :=
    canonicalFlatPoint_weightedArea_submodular
      P hPrimitive hReduced u D R S
  rw [affineConst_eq_base_add_weightedArea,
      affineConst_eq_base_add_weightedArea,
      affineConst_eq_base_add_weightedArea,
      affineConst_eq_base_add_weightedArea]
  omega

end RecordFerrers
end Collatz2
