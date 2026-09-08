import CollatzLean.Collatz3.Critical.RecordSkeleton
import CollatzLean.Collatz3.Critical.BestUpperWidth
import CollatzLean.Collatz3.Critical.WordProfileEquiv

/-!
# Collatz3: full Record--Ferrers local critical geometry

`CriticalRecordSkeleton` は global chord rank と roof-return だけを持つ。
このファイルで初めて、その各 block が local critical first-passage shape になる層を作る。

thin definition として保存するのは次だけである。

1. critical record skeleton,
2. width-only best-upper 性,
3. 最後の terminal block の local minimal depth。

interior block の minimal depthと、全 block の proper-prefix Beatty bound は theorem として導く。
primitive 性はここには保存しない。primitive は weak RecordView から strict skeleton を作る
前半の橋で使う語彙である。
-/

namespace Collatz3
namespace Critical

/-- cut `a` から `j` 進んだ局所 two-depth。 -/
def localDepth
    {m : ℕ}
    (h : Profile m)
    (a j : ℕ) : ℕ :=
  profileHeight h (a + j) - profileHeight h a

@[simp] theorem localDepth_zero
    {m : ℕ}
    (h : Profile m)
    (a : ℕ) :
    localDepth h a 0 = 0 := by
  simp [localDepth]

/-- admissible profile の height path は `a` から `a+j` まで weak monotone。 -/
theorem profileHeight_le_add
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    (a j : ℕ)
    (hEnd : a + j ≤ m) :
    profileHeight h a ≤ profileHeight h (a + j) := by
  revert hEnd
  induction j with
  | zero =>
      intro hEnd
      simp
  | succ j ih =>
      intro hEnd
      have hPrev : a + j ≤ m := by omega
      have hStepIndex : a + j < m := by omega
      have hIH := ih hPrev
      have hStep := profileHeight_lt_succ A hStepIndex
      have hStep' :
          profileHeight h (a + j) <
            profileHeight h (a + Nat.succ j) := by
        simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hStep
      exact le_trans hIH (Nat.le_of_lt hStep')

/-- local depth を start height と足すと global height に戻る。 -/
theorem profileHeight_add_localDepth
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    {a j : ℕ}
    (hEnd : a + j ≤ m) :
    profileHeight h a + localDepth h a j =
      profileHeight h (a + j) := by
  have hMono :
      profileHeight h a ≤ profileHeight h (a + j) :=
    profileHeight_le_add A a j hEnd
  have hSub := Nat.sub_add_cancel hMono
  simpa [localDepth, Nat.add_comm] using hSub

/--
chord rank の cut shift は local depth だけで書ける。

`rank(a+j)-rank(a) = H_m*j - m*localDepth(a,j)`。
-/
theorem profileChordRank_add_sub
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    {a j : ℕ}
    (hEnd : a + j ≤ m) :
    profileChordRank h (a + j) - profileChordRank h a =
      (criticalTwoDepth m : ℤ) * (j : ℤ) -
        (m : ℤ) * (localDepth h a j : ℤ) := by
  have hDepth :=
    profileHeight_add_localDepth A hEnd
  have hCutStart :
      cutDepth h a = profileHeight h a := by
    rfl
  have hCutEnd :
      cutDepth h (a + j) =
        profileHeight h (a + j) := by
    rfl
  have hDepthZ :
      (profileHeight h a : ℤ) +
          (localDepth h a j : ℤ) =
        (profileHeight h (a + j) : ℤ) := by
    exact_mod_cast hDepth
  unfold profileChordRank
  rw [hCutStart, hCutEnd]
  rw [← hDepthZ]
  push_cast
  ring

/-- record block interior では local depth が whole chord より strict に下。 -/
theorem localDepth_below_chord_of_recordInterior
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    {a r j : ℕ}
    (B : Combinatorics.IsRecordBlock (profileChordRank h) a r)
    (hEnd : a + r ≤ m)
    (hjPos : 0 < j)
    (hjLt : j < r) :
    m * localDepth h a j < criticalTwoDepth m * j := by
  have hWithin : a + j ≤ m := by omega
  have hDiff := profileChordRank_add_sub A hWithin
  have hRank := B.interior hjPos hjLt
  have hPos :
      0 < profileChordRank h (a + j) - profileChordRank h a :=
    sub_pos.mpr hRank
  rw [hDiff] at hPos
  have hPos' :
      (m : ℤ) * (localDepth h a j : ℤ) <
        (criticalTwoDepth m : ℤ) * (j : ℤ) := by
    linarith
  exact_mod_cast hPos'

/-- record block endpoint では local depth が whole chord より strict に上。 -/
theorem chord_below_localDepth_of_recordEnd
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    {a r : ℕ}
    (B : Combinatorics.IsRecordBlock (profileChordRank h) a r)
    (hEnd : a + r ≤ m) :
    criticalTwoDepth m * r < m * localDepth h a r := by
  have hDiff := profileChordRank_add_sub A hEnd
  have hRank := B.end_drop
  have hNeg :
      profileChordRank h (a + r) - profileChordRank h a < 0 :=
    sub_neg.mpr hRank
  rw [hDiff] at hNeg
  have hNeg' :
      (criticalTwoDepth m : ℤ) * (r : ℤ) <
        (m : ℤ) * (localDepth h a r : ℤ) := by
    linarith
  exact_mod_cast hNeg'

/--
best-upper width の record block interior は local Beatty roof 以下。
これが global strict excursion から local first-passage を導く中心 bridge。
-/
theorem localDepth_le_beatty_of_bestUpper
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    (Best : IsBestUpperWidth m)
    {a r j : ℕ}
    (B : Combinatorics.IsRecordBlock (profileChordRank h) a r)
    (hEnd : a + r ≤ m)
    (hjPos : 0 < j)
    (hjLt : j < r) :
    localDepth h a j ≤ beattyIndex j := by
  have hm : 0 < m := by
    have hr := B.length_pos
    omega
  have hjM : j < m := by omega
  have hBelow :=
    localDepth_below_chord_of_recordInterior A B hEnd hjPos hjLt
  exact Best.depth_le_beatty_of_strict_below hm hjPos hjM hBelow

/--
interior block が roof から roof へ strict record drop するなら、
その local terminal depth は自動的に minimal critical depth `H_r` になる。

従って interior carry `1` は structure field ではなく derived theorem である。
-/
theorem interior_localDepth_eq_criticalTwoDepth
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    {a r : ℕ}
    (B : Combinatorics.IsRecordBlock (profileChordRank h) a r)
    (hStartRoof : IsRoofCut h a)
    (hEndRoof : IsRoofCut h (a + r)) :
    localDepth h a r = criticalTwoDepth r := by
  have hEndLe : a + r ≤ m := Nat.le_of_lt hEndRoof.lt_width
  have hDepthAdd := profileHeight_add_localDepth A hEndLe
  have hStartHeight := hStartRoof.height_eq
  have hEndHeight := hEndRoof.height_eq
  have hLocalBeatty :
      beattyIndex a + localDepth h a r = beattyIndex (a + r) := by
    simpa [hStartHeight, hEndHeight] using hDepthAdd
  have hCarry := beattyIndex_add_eq a r
  have hCarryCases := beattyCarry_eq_zero_or_one a r
  have hAbove := chord_below_localDepth_of_recordEnd A B hEndLe
  have hm : 0 < m :=
    lt_trans hStartRoof.1 hStartRoof.2.1
  have hLower := beattyIndex_below_criticalChord hm B.length_pos
  rcases hCarryCases with hZero | hOne
  · have hDepthEq : localDepth h a r = beattyIndex r := by
      rw [hZero, Nat.add_zero] at hCarry
      omega
    rw [hDepthEq] at hAbove
    omega
  · have hDepthEq : localDepth h a r = beattyIndex r + 1 := by
      rw [hOne] at hCarry
      omega
    simpa [criticalTwoDepth] using hDepthEq

/-- 一つの local block が critical first-passage profile geometry を満たす。 -/
def IsLocalCriticalBlock
    {m : ℕ}
    (h : Profile m)
    (a r : ℕ) : Prop :=
  0 < r ∧
    a + r ≤ m ∧
    localDepth h a r = criticalTwoDepth r ∧
    ∀ j : ℕ,
      0 < j →
      j < r →
      localDepth h a j ≤ beattyIndex j

/-- 最後の block だけに必要な minimal-depth input。 -/
def TerminalMinimalFrom
    {m : ℕ}
    (h : Profile m) : ℕ → List ℕ → Prop
  | _a, [] => False
  | a, [r] => localDepth h a r = criticalTwoDepth r
  | a, r :: s :: rs => TerminalMinimalFrom h (a + r) (s :: rs)

/-- 全 block が local critical geometry を満たすという派生 predicate。 -/
def LocalCriticalBlocksFrom
    {m : ℕ}
    (h : Profile m) : ℕ → List ℕ → Prop
  | _a, [] => True
  | a, r :: rs =>
      IsLocalCriticalBlock h a r ∧
        LocalCriticalBlocksFrom h (a + r) rs

/--
record skeleton + best-upper + 最終 minimal depth から、全 block の local criticality を導く。
interior minimal depth は `interior_localDepth_eq_criticalTwoDepth` から自動で出る。
-/
theorem localCriticalBlocksFrom_of_record
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    (Best : IsBestUpperWidth m) :
    ∀ (a : ℕ) (rs : List ℕ),
      IsRoofCut h a →
      RoofRecordSkeleton.RealizesBlocksFrom h a rs →
      TerminalMinimalFrom h a rs →
      LocalCriticalBlocksFrom h a rs
  | _a, [], _hRoof, hFalse, _hTerminal => False.elim hFalse
  | a, [r], hRoof, hOne, hTerminal => by
      have hEnd : a + r ≤ m := Nat.le_of_eq hOne.2
      refine ⟨?_, by trivial⟩
      refine ⟨hOne.1.length_pos, hEnd, hTerminal, ?_⟩
      intro j hjPos hjLt
      exact localDepth_le_beatty_of_bestUpper
        A Best hOne.1 hEnd hjPos hjLt
  | a, r :: s :: rs, hRoof, hMany, hTerminal => by
      have hEndRoof : IsRoofCut h (a + r) := hMany.2.1
      have hEnd : a + r ≤ m := Nat.le_of_lt hEndRoof.lt_width
      have hMinimal : localDepth h a r = criticalTwoDepth r :=
        interior_localDepth_eq_criticalTwoDepth A hMany.1 hRoof hEndRoof
      refine ⟨?_, ?_⟩
      · refine ⟨hMany.1.length_pos, hEnd, hMinimal, ?_⟩
        intro j hjPos hjLt
        exact localDepth_le_beatty_of_bestUpper
          A Best hMany.1 hEnd hjPos hjLt
      · exact localCriticalBlocksFrom_of_record
          A Best
          (a + r) (s :: rs)
          hEndRoof hMany.2.2 hTerminal

/--
full Record--Ferrers packet。

local block 列そのものを data として重複保存せず、critical record skeleton と
width arithmetic から local critical geometry を導く。
terminal block の minimal depth だけは現段階では独立 input とする。
-/
structure RecordFerrers (m : ℕ) where
  record : CriticalRecordSkeleton m
  bestUpper : IsBestUpperWidth m
  terminalMinimal : TerminalMinimalFrom
    record.profile.1 initialRoofAnchor record.skeleton.lengths

namespace RecordFerrers

/-- underlying critical record skeleton を忘却する。 -/
def forgetRecordSkeleton
    {m : ℕ}
    (R : RecordFerrers m) : CriticalRecordSkeleton m :=
  R.record

/-- underlying admissible profile。 -/
def profile
    {m : ℕ}
    (R : RecordFerrers m) : AdmissibleProfile m :=
  R.record.profile

/-- full Record--Ferrers 幅は 2 以上。 -/
theorem one_lt_width
    {m : ℕ}
    (R : RecordFerrers m) :
    1 < m :=
  R.record.one_lt_width

/-- 全 skeleton block は local critical geometry を満たす。 -/
theorem localCriticalBlocks
    {m : ℕ}
    (R : RecordFerrers m) :
    LocalCriticalBlocksFrom
      R.record.profile.1 initialRoofAnchor R.record.skeleton.lengths := by
  exact localCriticalBlocksFrom_of_record
    R.record.profile.2 R.bestUpper
    initialRoofAnchor R.record.skeleton.lengths
    R.record.realizes.anchor_roof
    R.record.realizes.2
    R.terminalMinimal

end RecordFerrers

/-- local profile geometry から読む exponent word。 -/
def localWord
    {m : ℕ}
    (h : Profile m)
    (a r : ℕ) : Word :=
  wordFromHeight (fun j => localDepth h a j) r

/-- admissible profile の local depth path は block 範囲内で strict に増加する。 -/
theorem localDepth_lt_succ
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    {a r j : ℕ}
    (hEnd : a + r ≤ m)
    (hj : j < r) :
    localDepth h a j < localDepth h a (j + 1) := by
  have hBaseJ :
      profileHeight h a ≤ profileHeight h (a + j) :=
    profileHeight_le_add A a j (by omega)
  have hBaseNext :
      profileHeight h a ≤ profileHeight h (a + (j + 1)) :=
    profileHeight_le_add A a (j + 1) (by omega)
  have hStepIndex : a + j < m := by omega
  have hStep := profileHeight_lt_succ A hStepIndex
  have hStep' :
      profileHeight h (a + j) < profileHeight h (a + (j + 1)) := by
    simpa [Nat.add_assoc] using hStep
  have hJ := Nat.sub_add_cancel hBaseJ
  have hNext := Nat.sub_add_cancel hBaseNext
  unfold localDepth
  omega

/-- local critical geometry は genuine `IsCriticalWord` を生成する。 -/
theorem isCriticalWord_localWord
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    {a r : ℕ}
    (B : IsLocalCriticalBlock h a r) :
    IsCriticalWord r (localWord h a r) := by
  have hStep :
      ∀ j : ℕ, j < r →
        localDepth h a j < localDepth h a (j + 1) := by
    intro j hj
    exact localDepth_lt_succ A B.2.1 hj
  refine ⟨?_, oddSteps_wordFromHeight _ _, ?_, ?_⟩
  · exact valid_wordFromHeight (fun j => localDepth h a j) r hStep
  · calc
      Word.twoSteps (localWord h a r)
          = localDepth h a r := by
              exact twoSteps_wordFromHeight
                (fun j => localDepth h a j) r
                (localDepth_zero h a) hStep
      _ = criticalTwoDepth r := B.2.2.1
  · intro k hk
    have hPrefix := prefixTwoDepth_wordFromHeight
      (fun j => localDepth h a j) r
      (localDepth_zero h a) hStep
      (Nat.le_of_lt hk)
    change
      Word.prefixTwoDepth
          (wordFromHeight (fun j => localDepth h a j) r) k
        ≤ beattyIndex k
    rw [hPrefix]
    by_cases hk0 : k = 0
    · subst k
      simp [localDepth]
    · exact B.2.2.2 k (Nat.pos_of_ne_zero hk0) hk
end Critical
end Collatz3
