import CollatzLean.Collatz2.CSTMicro.FirstFailureExtraction
import CollatzLean.Collatz2.CSTMicro.FerrersBoundarySturmian

/-!
# General CST: A boundary -> B first-failure provenance

既存 `FirstFailureEdge` は safe -> failure の adjacent edge だけを保持するため、
その edge がどの Ferrers boundary から来たかという provenance を忘れている。

このファイルでは boundary から first failure 直前までを
`SafeFerrersChain` として保持する。

重要なのは `SafeFerrersChain` が単なる `FerrersChain` ではなく、
chain 上の各 endpoint が `WordPureSeparation` を満たすことを型として保持する点である。
これにより

  critical/Ferrers boundary (A-safe)
      -> safe
      -> ...
      -> safe lower
      -> failure upper
      -> ...
      -> bad target

という A -> B の由来を lossless に残す。
-/

namespace Collatz2
namespace CSTMicro

/-! ## 1. endpoint ごとの safety を保持する Ferrers chain -/

/--
全 endpoint が `WordPureSeparation` を満たす Ferrers chain。

`refl` でも start 自身の safety を保持し、`step` では新 endpoint の safety を
追加する。そのため boundary から lower までの「まだ failure が起きていない」
という情報をそのまま data として持てる。
-/
inductive SafeFerrersChain : ParityWord → ParityWord → Type
  | refl (v : ParityWord)
      (hSafe : WordPureSeparation v) :
      SafeFerrersChain v v
  | step {u v w : ParityWord}
      (C : SafeFerrersChain u v)
      (S : FerrersStep v w)
      (hSafe : WordPureSeparation w) :
      SafeFerrersChain u w

namespace SafeFerrersChain

/-- safety proof を忘れた通常の Ferrers chain は存在する。 -/
theorem nonempty_ferrersChain
    {start finish : ParityWord}
    (C : SafeFerrersChain start finish) :
    Nonempty (FerrersChain start finish) := by
  induction C with
  | refl _hSafe =>
      exact ⟨FerrersChain.refl _⟩
  | step C S _hSafe ih =>
      rcases ih with ⟨D⟩
      exact ⟨FerrersChain.step D S⟩

/--
safety proof だけを忘れ、同じ step 列をそのまま通常の Ferrers chain へ写す。

`Classical.choice` を介さず、`SafeFerrersChain` の constructor history を
structural recursion でそのまま `FerrersChain` へ移す。
-/
def toFerrersChain :
    {start finish : ParityWord} →
      SafeFerrersChain start finish →
        FerrersChain start finish
  | _, _, .refl v _hSafe =>
      FerrersChain.refl v
  | _, _, .step C S _hSafe =>
      FerrersChain.step (toFerrersChain C) S

/--
`SafeFerrersChain` に現れる全 step が述語 `P` を満たすことを順序を保って表す。

endpoint safety は `SafeFerrersChain` 自身が保持しているため、ここでは step-level の
追加条件だけを lossless に畳み込む。後段で「以前の全 carry が clearance 未満」などを
全 intermediate step に対して述べるための共通 API とする。
-/
def AllSteps
    (P : ∀ {lower upper : ParityWord}, FerrersStep lower upper → Prop)
    {start finish : ParityWord}
    (C : SafeFerrersChain start finish) : Prop :=
  match C with
  | .refl _ _ => True
  | .step C S _ => AllSteps P C ∧ P S

@[simp] theorem allSteps_refl
    (P : ∀ {lower upper : ParityWord}, FerrersStep lower upper → Prop)
    (v : ParityWord)
    (hSafe : WordPureSeparation v) :
    AllSteps P (SafeFerrersChain.refl v hSafe) := by
  simp [AllSteps]

@[simp] theorem allSteps_step
    (P : ∀ {lower upper : ParityWord}, FerrersStep lower upper → Prop)
    {u v w : ParityWord}
    (C : SafeFerrersChain u v)
    (S : FerrersStep v w)
    (hSafe : WordPureSeparation w) :
    AllSteps P (SafeFerrersChain.step C S hSafe) ↔
      AllSteps P C ∧ P S := by
  rfl

/-- safe chain の start は safe。 -/
theorem start_safe
    {start finish : ParityWord}
    (C : SafeFerrersChain start finish) :
    WordPureSeparation start := by
  induction C with
  | refl hSafe =>
      exact hSafe
  | step _ _ _ ih =>
      exact ih

/-- safe chain の finish も safe。 -/
theorem finish_safe
    {start finish : ParityWord}
    (C : SafeFerrersChain start finish) :
    WordPureSeparation finish := by
  induction C with
  | refl hSafe =>
      exact hSafe
  | step _ _ hSafe _ih =>
      exact hSafe

/-- safe chain でも underlying Ferrers chain と同様に first-passage を保存する。 -/
theorem preserves_firstPassage
    {start finish : ParityWord}
    (C : SafeFerrersChain start finish)
    (hStart : IsFirstPassageWord start) :
    IsFirstPassageWord finish := by
  exact C.toFerrersChain.preserves_firstPassage hStart

end SafeFerrersChain

/-! ## 2. Ferrers chain の endpoint invariants -/

namespace FerrersChain

/-- Ferrers chain は length を保存する。 -/
theorem length_eq
    {start finish : ParityWord}
    (C : FerrersChain start finish) :
    start.length = finish.length := by
  induction C with
  | refl =>
      rfl
  | step C S ih =>
      exact ih.trans S.length_eq

/-- Ferrers chain は endpoint odd count を保存する。 -/
theorem oddCount_eq
    {start finish : ParityWord}
    (C : FerrersChain start finish) :
    oddCount start = oddCount finish := by
  induction C with
  | refl =>
      rfl
  | step C S ih =>
      exact ih.trans S.oddCount_eq

/--
start が safe な Ferrers chain は、

* finish まで全部 safe、または
* safe prefix の直後に初めて failure edge があり、その後に suffix が残る

のどちらかに分解できる。

後者では prefix 自体が `SafeFerrersChain` なので、抽出された edge より前に
failure が存在しないことが data として保証される。
-/
theorem safe_or_exists_safePrefix_failure
    {start finish : ParityWord}
    (C : FerrersChain start finish)
    (hStartSafe : WordPureSeparation start) :
    Nonempty (SafeFerrersChain start finish) ∨
      ∃ lower upper : ParityWord,
        Nonempty (SafeFerrersChain start lower) ∧
        Nonempty (FerrersStep lower upper) ∧
        ¬ WordPureSeparation upper ∧
        Nonempty (FerrersChain upper finish) := by
  revert hStartSafe
  induction C with
  | refl =>
      intro hSafe
      exact Or.inl ⟨SafeFerrersChain.refl _ hSafe⟩
  | @step v w C S ih =>
      intro hUSafe
      rcases ih hUSafe with hSafePrefix | hFailure
      · rcases hSafePrefix with ⟨SC⟩
        by_cases hWSafe : WordPureSeparation w
        · exact
            Or.inl ⟨SafeFerrersChain.step SC S hWSafe⟩
        · exact
            Or.inr
              ⟨v, w, ⟨SC⟩, ⟨S⟩, hWSafe,
               ⟨FerrersChain.refl w⟩⟩
      · rcases hFailure with
          ⟨lower, upper, hPrefix, T, hUpperFail, hSuffix⟩
        rcases hSuffix with ⟨D⟩
        exact
          Or.inr
            ⟨lower, upper, hPrefix, T, hUpperFail,
              ⟨FerrersChain.step D S⟩⟩

end FerrersChain

/-! ## 3. A boundary から B first failure までの provenance packet -/

/--
一つの bad target に対する A -> B provenance。

`safePrefixChain` が boundary から `lower` まで全て safe であることを保持し、
`failureStep` の upper で初めて failure する。
`failureSuffixChain` はその first failure から元の bad target までの残り chain。
-/
structure FirstFailureProvenance (target : ParityWord) where
  boundary : ParityWord
  lower : ParityWord
  upper : ParityWord
  boundary_isBoundary : IsFerrersBoundary boundary
  target_firstPassage : IsFirstPassageWord target
  target_failure : ¬ WordPureSeparation target
  safePrefixChain : SafeFerrersChain boundary lower
  failureStep : FerrersStep lower upper
  upper_failure : ¬ WordPureSeparation upper
  failureSuffixChain : FerrersChain upper target

namespace FirstFailureProvenance

/-- provenance の safe prefix endpoint は safe。 -/
theorem lower_safe
    {target : ParityWord}
    (P : FirstFailureProvenance target) :
    WordPureSeparation P.lower :=
  P.safePrefixChain.finish_safe

/-- provenance の lower は boundary から first-passage を継承する。 -/
theorem lower_firstPassage
    {target : ParityWord}
    (P : FirstFailureProvenance target) :
    IsFirstPassageWord P.lower := by
  exact
    P.safePrefixChain.preserves_firstPassage
      P.boundary_isBoundary.1

/-- failure upper も first-passage。 -/
theorem upper_firstPassage
    {target : ParityWord}
    (P : FirstFailureProvenance target) :
    IsFirstPassageWord P.upper := by
  exact
    P.failureStep.preserves_firstPassage
      P.lower_firstPassage

/-- provenance の distinguished edge を既存 `FirstFailureEdge` API へ忘却する。 -/
def toFirstFailureEdge
    {target : ParityWord}
    (P : FirstFailureProvenance target) :
    FirstFailureEdge := {
  lower := P.lower
  upper := P.upper
  step := P.failureStep
  lower_firstPassage := P.lower_firstPassage
  upper_firstPassage := P.upper_firstPassage
  lower_safe := P.lower_safe
  upper_failure := P.upper_failure
}

/-- distinguished first failure edge は既存 theorem により carry。 -/
theorem failure_hasCarry
    {target : ParityWord}
    (P : FirstFailureProvenance target) :
    P.failureStep.edge.HasCarry := by
  exact P.toFirstFailureEdge.hasCarry

/-- boundary と target は同じ length。 -/
theorem boundary_length_eq_target_length
    {target : ParityWord}
    (P : FirstFailureProvenance target) :
    P.boundary.length = target.length := by
  calc
    P.boundary.length = P.lower.length :=
      P.safePrefixChain.toFerrersChain.length_eq
    _ = P.upper.length :=
      P.failureStep.length_eq
    _ = target.length :=
      P.failureSuffixChain.length_eq

/-- boundary と target は同じ endpoint odd count。 -/
theorem boundary_oddCount_eq_target_oddCount
    {target : ParityWord}
    (P : FirstFailureProvenance target) :
    oddCount P.boundary = oddCount target := by
  calc
    oddCount P.boundary = oddCount P.lower :=
      P.safePrefixChain.toFerrersChain.oddCount_eq
    _ = oddCount P.upper :=
      P.failureStep.oddCount_eq
    _ = oddCount target :=
      P.failureSuffixChain.oddCount_eq

/-- provenance の boundary は target length に対応する explicit critical word。 -/
theorem boundary_eq_criticalBoundaryWord_targetLength
    {target : ParityWord}
    (P : FirstFailureProvenance target) :
    P.boundary = criticalBoundaryWord target.length := by
  calc
    P.boundary =
        criticalBoundaryWord P.boundary.length :=
      ferrersBoundary_eq_criticalBoundaryWord
        P.boundary_isBoundary
    _ = criticalBoundaryWord target.length := by
      rw [P.boundary_length_eq_target_length]

end FirstFailureProvenance

/-! ## 4. bad target から provenance を canonical に抽出 -/

/--
全 Ferrers boundary が safe なら、任意の bad first-passage target は
A boundary から B first failure までの provenance を持つ。
-/
theorem exists_firstFailureProvenance_from_bad_word
    {target : ParityWord}
    (hTargetFP : IsFirstPassageWord target)
    (hTargetFail : ¬ WordPureSeparation target)
    (hBoundarySafe :
      ∀ boundary : ParityWord,
        IsFerrersBoundary boundary →
          WordPureSeparation boundary) :
    Nonempty (FirstFailureProvenance target) := by
  rcases exists_ferrersBoundary_chain hTargetFP with
    ⟨boundary, hBoundary, ⟨C⟩⟩
  have hBoundarySafe' : WordPureSeparation boundary :=
    hBoundarySafe boundary hBoundary
  rcases
      C.safe_or_exists_safePrefix_failure hBoundarySafe' with
    hAllSafe | hFailure
  · rcases hAllSafe with ⟨SC⟩
    exact False.elim (hTargetFail SC.finish_safe)
  · rcases hFailure with
      ⟨lower, upper,
        ⟨safePrefixChain⟩,
        ⟨failureStep⟩,
        hUpperFail,
        ⟨failureSuffixChain⟩⟩
    exact
      ⟨{
        boundary := boundary
        lower := lower
        upper := upper
        boundary_isBoundary := hBoundary
        target_firstPassage := hTargetFP
        target_failure := hTargetFail
        safePrefixChain := safePrefixChain
        failureStep := failureStep
        upper_failure := hUpperFail
        failureSuffixChain := failureSuffixChain
      }⟩

/--
MicroObject の CST failure から、boundary provenance を保持した first failure を抽出する。
-/
theorem exists_firstFailureProvenance_of_cst_failure
    (M : MicroObject)
    (hFail : ¬ M.CSTHolds)
    (hBoundarySafe :
      ∀ boundary : ParityWord,
        IsFerrersBoundary boundary →
          WordPureSeparation boundary) :
    Nonempty (FirstFailureProvenance M.path.word) := by
  exact
    exists_firstFailureProvenance_from_bad_word
      M.path.isFirstPassageWord
      (M.wordPureSeparation_failure_of_cst_failure hFail)
      hBoundarySafe

end CSTMicro
end Collatz2
