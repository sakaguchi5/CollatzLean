import CollatzLean.Collatz3.Semantics.FirstPassage
import CollatzLean.Collatz3.Critical.ProfileExtraction
import CollatzLean.Collatz3.Ferrers.RecordPartition

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# Collatz3 Bridge: canonical record lengths の非単射性

`canonicalRecordLengths` は deterministic な record partition を与えるが、
full critical profile や exponent word の完全符号ではない。

ここでは actual odd-only Collatz 軌道から得る具体例 `95` と `175` を固定する。

* `95` の first-passage word は `[1,1,1,1,4]`、
* `175` の first-passage word は `[1,1,1,2,3]`。

両者から抽出される critical profile は異なるが、canonical record cut はともに空で、
従って `canonicalRecordLengths = [4]` となる。

したがって

`Profile 5 -> canonicalRecordLengths`

は非単射である。

これは `cuts <-> lengths` の有限データ inverse を否定しない。
失われる情報は `profile -> initialRecordCuts` の段階にある。
-/

namespace Collatz3
namespace Bridge
namespace RecordPartitionNoninjective

open Critical

/-- 初期値 `95` の最初の critical first-passage exponent word。 -/
abbrev word95 : Word := [1, 1, 1, 1, 4]

/-- 初期値 `175` の最初の critical first-passage exponent word。 -/
abbrev word175 : Word := [1, 1, 1, 2, 3]

/-- `95` の actual critical word から導く profile。 -/
def profile95 :=
  Critical.profileFromWord word95

/-- `175` の actual critical word から導く profile。 -/
def profile175 :=
  Critical.profileFromWord word175

/-- 小さい Beatty index を power bounds だけから確定する補助定理。 -/
private theorem beattyIndex_eq_of_pow_bounds
    {m q : ℕ}
    (hLower : 2 ^ q < 3 ^ m)
    (hUpper : 3 ^ m ≤ 2 ^ (q + 1)) :
    Critical.beattyIndex m = q := by
  apply Nat.le_antisymm
  · exact Critical.beattyIndex_le_of_upper hUpper
  · by_contra h
    have hLt : Critical.beattyIndex m < q := by omega
    have hExp : Critical.beattyIndex m + 1 ≤ q := by omega
    have hPow :
        2 ^ (Critical.beattyIndex m + 1) ≤ 2 ^ q :=
      Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hExp
    have hContr : 3 ^ m ≤ 2 ^ q :=
      le_trans (Critical.beattyIndex_upper m) hPow
    omega

private theorem beattyIndex_two : Critical.beattyIndex 2 = 3 := by
  exact beattyIndex_eq_of_pow_bounds (by norm_num) (by norm_num)

private theorem beattyIndex_three : Critical.beattyIndex 3 = 4 := by
  exact beattyIndex_eq_of_pow_bounds (by norm_num) (by norm_num)

private theorem beattyIndex_four : Critical.beattyIndex 4 = 6 := by
  exact beattyIndex_eq_of_pow_bounds (by norm_num) (by norm_num)

private theorem beattyIndex_five : Critical.beattyIndex 5 = 7 := by
  exact beattyIndex_eq_of_pow_bounds (by norm_num) (by norm_num)

private theorem oddStep_95_143 : OddStep 1 95 143 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  exact ⟨71, by norm_num⟩

private theorem oddStep_143_215 : OddStep 1 143 215 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  exact ⟨107, by norm_num⟩

private theorem oddStep_215_323 : OddStep 1 215 323 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  exact ⟨161, by norm_num⟩

private theorem oddStep_323_485 : OddStep 1 323 485 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  exact ⟨242, by norm_num⟩

private theorem oddStep_485_91 : OddStep 4 485 91 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  exact ⟨45, by norm_num⟩

private theorem oddStep_175_263 : OddStep 1 175 263 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  exact ⟨131, by norm_num⟩

private theorem oddStep_263_395 : OddStep 1 263 395 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  exact ⟨197, by norm_num⟩

private theorem oddStep_395_593 : OddStep 1 395 593 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  exact ⟨296, by norm_num⟩

private theorem oddStep_593_445 : OddStep 2 593 445 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  exact ⟨222, by norm_num⟩

private theorem oddStep_445_167 : OddStep 3 445 167 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  exact ⟨83, by norm_num⟩

/-- `95` は exponent word `[1,1,1,1,4]` を actual に実行して `91` へ到達する。 -/
theorem runs95 : Runs word95 95 91 := by
  change Runs [1, 1, 1, 1, 4] 95 91
  exact
    Runs.cons oddStep_95_143
      (Runs.cons oddStep_143_215
        (Runs.cons oddStep_215_323
          (Runs.cons oddStep_323_485
            (Runs.cons oddStep_485_91 (Runs.nil 91)))))

/-- `175` は exponent word `[1,1,1,2,3]` を actual に実行して `167` へ到達する。 -/
theorem runs175 : Runs word175 175 167 := by
  change Runs [1, 1, 1, 2, 3] 175 167
  exact
    Runs.cons oddStep_175_263
      (Runs.cons oddStep_263_395
        (Runs.cons oddStep_395_593
          (Runs.cons oddStep_593_445
            (Runs.cons oddStep_445_167 (Runs.nil 167)))))

/-- `95` の5-step word は critical boundary を初めて越える。 -/
theorem word95_criticalFirstPassage :
    Word.CriticalFirstPassage word95 := by
  constructor
  · norm_num [word95, Word.twoSteps, Word.oddSteps,
      Critical.criticalTwoDepth, beattyIndex_five]
  · intro k hk
    norm_num [word95, Word.oddSteps] at hk
    interval_cases k <;>
      norm_num [word95, Word.prefixTwoDepth, Word.twoSteps,
        Critical.beattyIndex_zero, Critical.beattyIndex_one,
        beattyIndex_two, beattyIndex_three, beattyIndex_four]

/-- `175` の5-step word も critical boundary を初めて越える。 -/
theorem word175_criticalFirstPassage :
    Word.CriticalFirstPassage word175 := by
  constructor
  · norm_num [word175, Word.twoSteps, Word.oddSteps,
      Critical.criticalTwoDepth, beattyIndex_five]
  · intro k hk
    norm_num [word175, Word.oddSteps] at hk
    interval_cases k <;>
      norm_num [word175, Word.prefixTwoDepth, Word.twoSteps,
        Critical.beattyIndex_zero, Critical.beattyIndex_one,
        beattyIndex_two, beattyIndex_three, beattyIndex_four]

/-- `95` は actual critical first-passage の具体例。 -/
theorem actualFirstPassage95 : ActualFirstPassage word95 95 91 :=
  ⟨runs95, word95_criticalFirstPassage⟩

/-- `175` も actual critical first-passage の具体例。 -/
theorem actualFirstPassage175 : ActualFirstPassage word175 175 167 :=
  ⟨runs175, word175_criticalFirstPassage⟩

/-- `95` の word から抽出した profile は `[0,0,1,1,2]`。 -/
theorem profileFromWord_word95_eq :
    Critical.profileFromWord word95 = profile95 := by
  funext k
  fin_cases k <;>
    norm_num [Critical.profileFromWord, profile95, word95,
      Word.prefixTwoDepth, Word.twoSteps,
      Critical.beattyIndex_zero, Critical.beattyIndex_one,
      beattyIndex_two, beattyIndex_three, beattyIndex_four]

/-- `175` の word から抽出した profile は `[0,0,1,1,1]`。 -/
theorem profileFromWord_word175_eq :
    Critical.profileFromWord word175 = profile175 := by
  funext k
  fin_cases k <;>
    norm_num [Critical.profileFromWord, profile175, word175,
      Word.prefixTwoDepth, Word.twoSteps,
      Critical.beattyIndex_zero, Critical.beattyIndex_one,
      beattyIndex_two, beattyIndex_three, beattyIndex_four]

/--
`95` と `175` から抽出される full critical profile は異なる。

違いは column `4` ですでに現れる。
`95` 側では prefix two-depth が `4`、
`175` 側では prefix two-depth が `5` なので、
`beattyIndex 4 = 6` から profile depth はそれぞれ `2`, `1` になる。
-/
theorem profile95_ne_profile175 :
    profile95 ≠ profile175 := by
  intro h
  have h4 :=
    congrFun h (⟨4, by decide⟩ : Fin 5)
  norm_num [
    profile95,
    profile175,
    Critical.profileFromWord,
    word95,
    word175,
    Word.prefixTwoDepth,
    Word.twoSteps,
    beattyIndex_four
  ] at h4


/-
以下の rank 計算も profile を独立した有限表として保存せず、
actual word から導いた `profileFromWord` を直接評価する。
-/

private theorem profile95_rank_one :
    Critical.profileChordRank profile95 1 = 3 := by
  norm_num [
    Critical.profileChordRank,
    Critical.cutDepth,
    Critical.checkpoint,
    Critical.criticalTwoDepth,
    profile95,
    Critical.profileFromWord,
    word95,
    Word.prefixTwoDepth,
    Word.twoSteps,
    Critical.beattyIndex_one,
    beattyIndex_five
  ]

private theorem profile95_rank_two :
    Critical.profileChordRank profile95 2 = 6 := by
  norm_num [
    Critical.profileChordRank,
    Critical.cutDepth,
    Critical.checkpoint,
    Critical.criticalTwoDepth,
    profile95,
    Critical.profileFromWord,
    word95,
    Word.prefixTwoDepth,
    Word.twoSteps,
    beattyIndex_two,
    beattyIndex_five
  ]

private theorem profile95_rank_three :
    Critical.profileChordRank profile95 3 = 9 := by
  norm_num [
    Critical.profileChordRank,
    Critical.cutDepth,
    Critical.checkpoint,
    Critical.criticalTwoDepth,
    profile95,
    Critical.profileFromWord,
    word95,
    Word.prefixTwoDepth,
    Word.twoSteps,
    beattyIndex_three,
    beattyIndex_five
  ]

private theorem profile95_rank_four :
    Critical.profileChordRank profile95 4 = 12 := by
  norm_num [
    Critical.profileChordRank,
    Critical.cutDepth,
    Critical.checkpoint,
    Critical.criticalTwoDepth,
    profile95,
    Critical.profileFromWord,
    word95,
    Word.prefixTwoDepth,
    Word.twoSteps,
    beattyIndex_four,
    beattyIndex_five
  ]

private theorem profile175_rank_one :
    Critical.profileChordRank profile175 1 = 3 := by
  norm_num [
    Critical.profileChordRank,
    Critical.cutDepth,
    Critical.checkpoint,
    Critical.criticalTwoDepth,
    profile175,
    Critical.profileFromWord,
    word175,
    Word.prefixTwoDepth,
    Word.twoSteps,
    Critical.beattyIndex_one,
    beattyIndex_five
  ]

private theorem profile175_rank_two :
    Critical.profileChordRank profile175 2 = 6 := by
  norm_num [
    Critical.profileChordRank,
    Critical.cutDepth,
    Critical.checkpoint,
    Critical.criticalTwoDepth,
    profile175,
    Critical.profileFromWord,
    word175,
    Word.prefixTwoDepth,
    Word.twoSteps,
    beattyIndex_two,
    beattyIndex_five
  ]

private theorem profile175_rank_three :
    Critical.profileChordRank profile175 3 = 9 := by
  norm_num [
    Critical.profileChordRank,
    Critical.cutDepth,
    Critical.checkpoint,
    Critical.criticalTwoDepth,
    profile175,
    Critical.profileFromWord,
    word175,
    Word.prefixTwoDepth,
    Word.twoSteps,
    beattyIndex_three,
    beattyIndex_five
  ]

private theorem profile175_rank_four :
    Critical.profileChordRank profile175 4 = 7 := by
  norm_num [
    Critical.profileChordRank,
    Critical.cutDepth,
    Critical.checkpoint,
    Critical.criticalTwoDepth,
    profile175,
    Critical.profileFromWord,
    word175,
    Word.prefixTwoDepth,
    Word.twoSteps,
    beattyIndex_four,
    beattyIndex_five
  ]

/--
`95` から抽出した profile には、
canonical anchor `1` より後の strict record cut が存在しない。
-/
theorem initialRecordCuts_profile95_eq_nil :
    Ferrers.initialRecordCuts profile95 = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro k hk
  have hk' :
      k ∈ Ferrers.recordCutsAfter
        profile95 Critical.initialRoofAnchor := by
    simpa [Ferrers.initialRecordCuts] using hk
  have hSpec :=
    (Ferrers.mem_recordCutsAfter_iff).1 hk'
  have hRec :
      Ferrers.IsRecordCutAfter
        profile95 Critical.initialRoofAnchor k :=
    hSpec.2
  have hkLower : 1 < k := by
    simpa [Critical.initialRoofAnchor] using hRec.1
  have hkUpper : k < 5 :=
    hRec.2.1
  have hRank :
      Critical.profileChordRank profile95 k <
        Critical.profileChordRank profile95 1 := by
    exact
      hRec.2.2
        ⟨1, by omega⟩
        (by simp [Critical.initialRoofAnchor])
  interval_cases k <;>
    norm_num [
      profile95_rank_one,
      profile95_rank_two,
      profile95_rank_three,
      profile95_rank_four
    ] at hRank

/--
`175` から抽出した profile にも、
canonical anchor `1` より後の strict record cut が存在しない。
-/
theorem initialRecordCuts_profile175_eq_nil :
    Ferrers.initialRecordCuts profile175 = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro k hk
  have hk' :
      k ∈ Ferrers.recordCutsAfter
        profile175 Critical.initialRoofAnchor := by
    simpa [Ferrers.initialRecordCuts] using hk
  have hSpec :=
    (Ferrers.mem_recordCutsAfter_iff).1 hk'
  have hRec :
      Ferrers.IsRecordCutAfter
        profile175 Critical.initialRoofAnchor k :=
    hSpec.2
  have hkLower : 1 < k := by
    simpa [Critical.initialRoofAnchor] using hRec.1
  have hkUpper : k < 5 :=
    hRec.2.1
  have hRank :
      Critical.profileChordRank profile175 k <
        Critical.profileChordRank profile175 1 := by
    exact
      hRec.2.2
        ⟨1, by omega⟩
        (by simp [Critical.initialRoofAnchor])
  interval_cases k <;>
    norm_num [
      profile175_rank_one,
      profile175_rank_two,
      profile175_rank_three,
      profile175_rank_four
    ] at hRank

/--
`95` から抽出した profile の canonical record lengths は `[4]`。

profile そのものから word を逆復元するのではなく、
`initialRecordCuts = []` から block partition を計算しているだけである。
-/
@[simp] theorem canonicalRecordLengths_profile95 :
    Ferrers.canonicalRecordLengths profile95 = [4] := by
  norm_num [
    Ferrers.canonicalRecordLengths,
    initialRecordCuts_profile95_eq_nil,
    Ferrers.blockLengthsFromCuts,
    Critical.initialRoofAnchor
  ]

/--
`175` から抽出した profile の canonical record lengths も `[4]`。
-/
@[simp] theorem canonicalRecordLengths_profile175 :
    Ferrers.canonicalRecordLengths profile175 = [4] := by
  norm_num [
    Ferrers.canonicalRecordLengths,
    initialRecordCuts_profile175_eq_nil,
    Ferrers.blockLengthsFromCuts,
    Critical.initialRoofAnchor
  ]

/--
`canonicalRecordLengths : Profile 5 → List ℕ` は非単射。

actual critical first-passage から得られる異なる二つの profile が、
同一の canonical record lengths `[4]` へ写る。
-/
theorem canonicalRecordLengths_not_injective :
    ¬ Function.Injective
      (fun h : Critical.Profile 5 =>
        Ferrers.canonicalRecordLengths h) := by
  intro hInjective
  apply profile95_ne_profile175
  apply hInjective
  change
    Ferrers.canonicalRecordLengths profile95 =
      Ferrers.canonicalRecordLengths profile175
  rw [
    canonicalRecordLengths_profile95,
    canonicalRecordLengths_profile175
  ]


/--
初期値 `95` と `175` からの actual critical first-passage が、
異なる full profile を持ちながら同じ canonical record lengths を持つ具体的反例。

非単射性は人工的な Profile の例ではなく、
actual Collatz 軌道から直接生じる。
-/
theorem actual_95_175_noninjective_counterexample :
    ActualFirstPassage word95 95 91 ∧
      ActualFirstPassage word175 175 167 ∧
      Critical.profileFromWord word95 ≠
        Critical.profileFromWord word175 ∧
      Ferrers.canonicalRecordLengths
          (Critical.profileFromWord word95) =
        Ferrers.canonicalRecordLengths
          (Critical.profileFromWord word175) := by
  refine
    ⟨actualFirstPassage95,
      actualFirstPassage175,
      ?_,
      ?_⟩
  · change profile95 ≠ profile175
    exact profile95_ne_profile175
  · change
      Ferrers.canonicalRecordLengths profile95 =
        Ferrers.canonicalRecordLengths profile175
    rw [
      canonicalRecordLengths_profile95,
      canonicalRecordLengths_profile175
    ]


end RecordPartitionNoninjective
end Bridge
end Collatz3
