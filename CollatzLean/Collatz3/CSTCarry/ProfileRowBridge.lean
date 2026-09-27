import CollatzLean.Collatz3.CSTCarry.FinalWrap26
import CollatzLean.Collatz3.Critical.WordProfileEquiv
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pairwise

/-!
# Collatz3 CSTCarry: Critical.Profile から actual Ferrers row への exact bridge

`CriticalCarryRows` は前段で、actual first-passage Ferrers rows が満たすべき
最小条件だけを抽象 predicate として切り出した。

このファイルではその未接続部分を閉じる。

幅 `m` の admissible profile `h` に対し、critical index `r<m` の row を

  boundary = beattyIndex r
  actual   = checkpoint h r

と定める。

row list は carry recurrence の向きに合わせて terminal 側から initial 側へ、
すなわち `r=m-1,...,0` の順に並べる。

admissibility だけから

* `r <= checkpoint h r`,
* checkpoint は `r` とともに strict に増加、
* 従って逆順 row list の actual depth は strict に下降、

が出るため、この canonical row list は `CriticalCarryRows m` を満たす。

ここには RecordFerrers / best-upper / primitive などの追加仮定は入れない。
-/

namespace Collatz3
namespace CSTCarry

open Critical

/-- profile の critical index `r` に対応する Ferrers row。 -/
def profileFerrersRow
    {m : ℕ}
    (h : Profile m)
    (r : Fin m) : FerrersRow :=
  { boundary := beattyIndex r.1
    actual := checkpoint h r
    actual_le_boundary := by
      unfold checkpoint
      exact Nat.sub_le _ _ }

@[simp] theorem profileFerrersRow_boundary
    {m : ℕ}
    (h : Profile m)
    (r : Fin m) :
    (profileFerrersRow h r).boundary = beattyIndex r.1 :=
  rfl

@[simp] theorem profileFerrersRow_actual
    {m : ℕ}
    (h : Profile m)
    (r : Fin m) :
    (profileFerrersRow h r).actual = checkpoint h r :=
  rfl

/--
profile rows を carry recurrence が読む向き `m-1,...,0` に並べた canonical list。
-/
def profileCarryRows
    {m : ℕ}
    (h : Profile m) : List FerrersRow :=
  (List.ofFn (fun r : Fin m => profileFerrersRow h r)).reverse

@[simp] theorem profileCarryRows_length
    {m : ℕ}
    (h : Profile m) :
    (profileCarryRows h).length = m := by
  simp [profileCarryRows]

/-- admissibility から index 自身が checkpoint 以下になる。 -/
theorem index_le_checkpoint_of_admissible
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    {r : ℕ}
    (hr : r < m) :
    r ≤ checkpoint h ⟨r, hr⟩ := by
  revert hr
  induction r with
  | zero =>
      intro hr
      omega
  | succ r ih =>
      intro hr
      have hrPrev : r < m := by omega
      have hPrev := ih hrPrev
      have hStep :
          checkpoint h ⟨r, by omega⟩ <
            checkpoint h ⟨r + 1, hr⟩ :=
        A.checkpoint_strict hr
      omega

/-- admissible checkpoint 列は任意の二 index 間でも strict に増加する。 -/
theorem checkpoint_lt_checkpoint_of_lt
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    {i j : ℕ}
    (hij : i < j)
    (hj : j < m) :
    checkpoint h ⟨i, by omega⟩ < checkpoint h ⟨j, hj⟩ := by
  revert i
  induction j with
  | zero =>
      intro i hij
      omega
  | succ j ih =>
      intro i hij
      by_cases hEq : i = j
      · subst i
        exact A.checkpoint_strict hj
      · have hij' : i < j := by omega
        have hLeft := ih (by omega) (i := i) hij'
        have hStep :
            checkpoint h ⟨j, by omega⟩ <
              checkpoint h ⟨j + 1, hj⟩ :=
          A.checkpoint_strict hj
        exact lt_trans hLeft hStep

/-- profile row の actual depth は対応する critical index 以上。 -/
theorem profileFerrersRow_index_le_actual
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    (r : Fin m) :
    r.1 ≤ (profileFerrersRow h r).actual := by
  simpa using index_le_checkpoint_of_admissible A r.2

/-- index が増えれば canonical profile row の actual depth も strict に増える。 -/
theorem profileFerrersRow_actual_strict
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    {i j : Fin m}
    (hij : i < j) :
    (profileFerrersRow h i).actual <
      (profileFerrersRow h j).actual := by
  exact checkpoint_lt_checkpoint_of_lt A hij j.2

/--
Fin-indexed row familyが pointwise critical envelope を満たせば、
逆順 `List.ofFn` は `CriticalRowEnvelope` を満たす。
-/
theorem criticalRowEnvelope_reverse_ofFn
    {m : ℕ}
    (row : Fin m → FerrersRow)
    (hBoundary : ∀ r : Fin m, (row r).boundary ≤ beattyIndex r.1)
    (hActual : ∀ r : Fin m, r.1 ≤ (row r).actual) :
    CriticalRowEnvelope m (List.ofFn row).reverse := by
  induction m with
  | zero =>
      simp [CriticalRowEnvelope]
  | succ m ih =>
      simp only [
        List.ofFn_succ',
        List.concat_eq_append,
        List.reverse_concat'
      ]
      simp only [CriticalRowEnvelope]
      refine ⟨?_, ?_, ?_⟩
      · simpa using hBoundary (Fin.last m)
      · simpa using hActual (Fin.last m)
      · apply ih
        · intro r
          simpa using hBoundary r.castSucc
        · intro r
          simpa using hActual r.castSucc

/-- pairwise な下降関係は `ActualStrictDescending` を含意する。 -/
theorem actualStrictDescending_of_pairwise
    {rows : List FerrersRow}
    (hPair : rows.Pairwise (fun R Q => Q.actual < R.actual)) :
    ActualStrictDescending rows := by
  induction rows with
  | nil => trivial
  | cons R Rs ih =>
      cases Rs with
      | nil => trivial
      | cons Q Qs =>
          simp only [List.pairwise_cons] at hPair
          simp only [ActualStrictDescending]
          refine ⟨hPair.1 Q (by simp), ?_⟩
          apply ih
          simpa only [List.pairwise_cons] using hPair.2

/--
actual depth が index とともに strict に増える Fin family を逆順に読むと、
`ActualStrictDescending` になる。
-/
theorem actualStrictDescending_reverse_ofFn
    {m : ℕ}
    (row : Fin m → FerrersRow)
    (hStrict : ∀ ⦃i j : Fin m⦄, i < j → (row i).actual < (row j).actual) :
    ActualStrictDescending (List.ofFn row).reverse := by
  apply actualStrictDescending_of_pairwise
  rw [List.pairwise_reverse]
  have hAsc :
      (List.ofFn row).Pairwise (fun R Q => R.actual < Q.actual) := by
    rw [List.pairwise_ofFn]
    intro i j hij
    exact hStrict hij
  simpa only using hAsc

/--
admissible profile から作る canonical row list は exact に critical envelope を満たす。
-/
theorem criticalRowEnvelope_profileCarryRows
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h) :
    CriticalRowEnvelope m (profileCarryRows h) := by
  unfold profileCarryRows
  apply criticalRowEnvelope_reverse_ofFn
  · intro r
    simp
  · intro r
    exact profileFerrersRow_index_le_actual A r

/--
admissible profile から作る canonical row list の actual depth は
terminal-to-initial 順に strict に下降する。
-/
theorem actualStrictDescending_profileCarryRows
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h) :
    ActualStrictDescending (profileCarryRows h) := by
  unfold profileCarryRows
  apply actualStrictDescending_reverse_ofFn
  intro i j hij
  exact profileFerrersRow_actual_strict A hij

/--
## Profile -> CriticalCarryRows bridge

これが前段で未接続だった中心 bridge。
任意の admissible critical profile は、canonical に構成した row list 上で
`CriticalCarryRows` を満たす。
-/
theorem criticalCarryRows_profileCarryRows
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h) :
    CriticalCarryRows m (profileCarryRows h) := by
  exact ⟨criticalRowEnvelope_profileCarryRows A,
    actualStrictDescending_profileCarryRows A⟩

/-- admissible profile subtype から canonical CSTCarry row list を読む。 -/
def admissibleProfileCarryRows
    {m : ℕ}
    (H : AdmissibleProfile m) : List FerrersRow :=
  profileCarryRows H.1

@[simp] theorem admissibleProfileCarryRows_length
    {m : ℕ}
    (H : AdmissibleProfile m) :
    (admissibleProfileCarryRows H).length = m := by
  simp [admissibleProfileCarryRows]

/-- subtype 版の `Profile -> CriticalCarryRows` bridge。 -/
theorem criticalCarryRows_admissibleProfileCarryRows
    {m : ℕ}
    (H : AdmissibleProfile m) :
    CriticalCarryRows m (admissibleProfileCarryRows H) := by
  exact criticalCarryRows_profileCarryRows H.2

/--
`profileOfWord` から作る row の actual depth は、元 critical word の
prefix two-depth と exact に一致する。

これにより `checkpoint` が単なる補助量ではなく、実際に row の odd-prefix depth を
読んでいることを明示する。
-/
theorem profileFerrersRow_profileOfWord_actual_eq_prefixTwoDepth
    {m : ℕ}
    {w : Word}
    (C : IsCriticalWord m w)
    (r : Fin m) :
    (profileFerrersRow (profileOfWord (m := m) w) r).actual =
      Word.prefixTwoDepth w r.1 := by
  have hLe := C.prefixTwoDepth_le_beatty (k := r.1) r.2
  simp only [profileFerrersRow_actual, checkpoint, profileOfWord]
  omega

/-- critical exponent word から canonical profile rows を作る。 -/
def criticalWordCarryRows
    {m : ℕ}
    {w : Word}
    (_C : IsCriticalWord m w) : List FerrersRow :=
  profileCarryRows (profileOfWord (m := m) w)

/--
critical exponent word は `profileOfWord` を経由して `CriticalCarryRows` を生成する。
positive-width 仮定は不要。
-/
theorem criticalCarryRows_criticalWordCarryRows
    {m : ℕ}
    {w : Word}
    (C : IsCriticalWord m w) :
    CriticalCarryRows m (criticalWordCarryRows C) := by
  exact criticalCarryRows_profileCarryRows (admissible_profileOfWord C)

namespace CarryRealizes

/--
`CriticalCarryRows` を外部仮定せず、admissible profile から canonical に作った rows へ
`P <= 26` の final-wrap 排除を直接適用する。

残る仮定は、この rows 上で三進 carry recurrence `CarryRealizes` が実現されることだけ。
-/
theorem final_lt_modulus_of_profileCarryRows_le_26
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    {digits : List ℕ}
    {F : ℕ}
    (hCarry : CarryRealizes
      (2 ^ criticalTwoDepth m) (profileCarryRows h) 0 digits F)
    (hm2 : 2 ≤ m)
    (hm26 : m ≤ 26) :
    F < 2 ^ criticalTwoDepth m := by
  exact hCarry.final_lt_modulus_of_criticalRows_le_26
    (criticalCarryRows_profileCarryRows A) hm2 hm26

end CarryRealizes

end CSTCarry
end Collatz3
