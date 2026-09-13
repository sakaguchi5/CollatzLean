import CollatzLean.Collatz3.Bridge.InfiniteSurvivorDefect
import CollatzLean.Collatz3.Bridge.CriticalAdmissibleParity

/-!
# Collatz3 Bridge: finite survivor prefix の canonical critical completion

positive physical depth `n` の survivor composition `S` を、その block 数 `m` を保ったまま
最後の block だけ延長し、total depth を

`criticalTwoDepth m = beattyIndex m + 1`

まで到達させる。

proper block endpoint は一切変わらないので、完成後は幅 `m` の `CriticalWord` になる。
さらに restricted partition 座標は元 survivor prefix の

`D_k - k`

に exact に一致し、復元 profile depth は

`beattyIndex k - D_k`

すなわち survivor の roof defect そのものになる。
-/

namespace Collatz3
namespace Bridge

/-- positive composition では `k` block 分の depth は少なくとも `k`。 -/
theorem le_sizeUpTo_of_le_length
    {n : ℕ}
    (c : ParityComposition n)
    {k : ℕ}
    (hk : k ≤ c.length) :
    k ≤ c.sizeUpTo k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hklt : k < c.length := by omega
      have ih' : k ≤ c.sizeUpTo k := ih (by omega)
      rw [c.sizeUpTo_succ hklt]
      have hb : 1 ≤ c.blocks[k] := c.one_le_blocks' hklt
      omega

/-- survivor terminal power inequality から `n ≤ beattyIndex m` を回収する。 -/
theorem survivor_depth_le_beatty_length
    {n : ℕ}
    (S : SurvivorParityCode n) :
    n ≤ Critical.beattyIndex S.1.length := by
  have hPow :
      2 ^ Word.prefixTwoDepth S.1.blocks S.1.length ≤
        3 ^ S.1.length := by
    simpa using S.2.terminal_safe
  have hDepth :=
    Critical.prefixDepth_le_beatty_of_powerCoefficient hPow
  simpa using hDepth

/-- critical terminal までに追加する最後の zero-run depth。 -/
def survivorCriticalExtraDepth
    {n : ℕ}
    (S : SurvivorParityCode n) : ℕ :=
  Critical.criticalTwoDepth S.1.length - n

/-- completion extra depth は正。 -/
theorem survivorCriticalExtraDepth_pos
    {n : ℕ}
    (S : SurvivorParityCode n) :
    0 < survivorCriticalExtraDepth S := by
  have hLe := survivor_depth_le_beatty_length S
  unfold survivorCriticalExtraDepth Critical.criticalTwoDepth
  omega

/-- 最後の block だけ critical terminal まで延長した block list。 -/
def survivorCriticalCompletionBlocks
    {n : ℕ}
    (hn : 0 < n)
    (S : SurvivorParityCode n) : List ℕ :=
  S.1.blocks.dropLast ++
    [parityLastBlock hn S.1 + survivorCriticalExtraDepth S]

/-- completion は block 数を保存する。 -/
theorem survivorCriticalCompletionBlocks_length
    {n : ℕ}
    (hn : 0 < n)
    (S : SurvivorParityCode n) :
    (survivorCriticalCompletionBlocks hn S).length = S.1.length := by
  let hne := parityComposition_blocks_ne_nil hn S.1
  have hLen := congrArg List.length (List.dropLast_append_getLast hne)
  unfold survivorCriticalCompletionBlocks parityLastBlock
  simpa using hLen

/-- completion の各 block は正。 -/
theorem survivorCriticalCompletionBlocks_pos
    {n : ℕ}
    (hn : 0 < n)
    (S : SurvivorParityCode n) :
    ∀ e ∈ survivorCriticalCompletionBlocks hn S, 0 < e := by
  intro e he
  rw [survivorCriticalCompletionBlocks, List.mem_append] at he
  rcases he with he | he
  · apply S.1.blocks_pos
    let hne := parityComposition_blocks_ne_nil hn S.1
    rw [← List.dropLast_append_getLast hne]
    simp [he]
  · simp only [List.mem_singleton] at he
    subst e
    have hLast := parityLastBlock_pos hn S.1
    exact Nat.add_pos_left hLast _

/-- completion block sum は critical terminal depth。 -/
theorem survivorCriticalCompletionBlocks_sum
    {n : ℕ}
    (hn : 0 < n)
    (S : SurvivorParityCode n) :
    (survivorCriticalCompletionBlocks hn S).sum =
      Critical.criticalTwoDepth S.1.length := by
  let hne := parityComposition_blocks_ne_nil hn S.1
  let a := S.1.blocks.getLast hne
  have hSplit : S.1.blocks.dropLast.sum + a = n := by
    have h := congrArg List.sum (List.dropLast_append_getLast hne)
    simpa [a, List.sum_append, S.1.blocks_sum] using h
  have hLe := survivor_depth_le_beatty_length S
  unfold survivorCriticalCompletionBlocks survivorCriticalExtraDepth parityLastBlock
  simp only [List.sum_append, List.sum_singleton]
  change S.1.blocks.dropLast.sum +
      (a + (Critical.criticalTwoDepth S.1.length - n)) = _
  rw [← Nat.add_assoc, hSplit]
  have hnCrit : n ≤ Critical.criticalTwoDepth S.1.length := by
    unfold Critical.criticalTwoDepth
    omega
  exact Nat.add_sub_of_le hnCrit

/-- completion を parity composition として束ねる。 -/
def survivorCriticalCompletionComposition
    {n : ℕ}
    (hn : 0 < n)
    (S : SurvivorParityCode n) :
    ParityComposition (Critical.criticalTwoDepth S.1.length) :=
  ⟨survivorCriticalCompletionBlocks hn S,
    by
      intro e he
      exact survivorCriticalCompletionBlocks_pos hn S e he,
    survivorCriticalCompletionBlocks_sum hn S⟩

/-- proper block prefix の depth は completion 前後で変わらない。 -/
theorem survivorCriticalCompletion_sizeUpTo
    {n : ℕ}
    (hn : 0 < n)
    (S : SurvivorParityCode n)
    {k : ℕ}
    (hk : k < S.1.length) :
    (survivorCriticalCompletionComposition hn S).sizeUpTo k =
      S.1.sizeUpTo k := by
  let hne := parityComposition_blocks_ne_nil hn S.1
  have hLen := congrArg List.length (List.dropLast_append_getLast hne)
  have hkDrop : k ≤ S.1.blocks.dropLast.length := by
    have hLen' : S.1.blocks.dropLast.length + 1 = S.1.blocks.length := by
      simpa using hLen
    change k < S.1.blocks.length at hk
    omega
  unfold Composition.sizeUpTo survivorCriticalCompletionComposition
  dsimp
  unfold survivorCriticalCompletionBlocks
  rw [List.take_append_of_le_length hkDrop]
  have hTake : S.1.blocks.dropLast.take k = S.1.blocks.take k := by
    rw [List.dropLast_eq_take, List.take_take]
    have hk' : k ≤ S.1.blocks.length - 1 := by
      change k < S.1.blocks.length at hk
      omega
    rw [Nat.min_eq_left hk']
  rw [hTake]

/-- completion は幅 `m = length S` の admissible critical parity code。 -/
def survivorCriticalCompletionParityCode
    {n : ℕ}
    (hn : 0 < n)
    (S : SurvivorParityCode n) :
    AdmissibleParityCode S.1.length := by
  let C := survivorCriticalCompletionComposition hn S
  refine ⟨C, ?_⟩
  constructor
  · exact survivorCriticalCompletionBlocks_length hn S
  · intro k hk
    rw [survivorCriticalCompletion_sizeUpTo hn S hk]
    have hPow := S.2.proper_safe hk
    exact
      Critical.prefixDepth_le_beatty_of_powerCoefficient
        (w := S.1.blocks) (k := k) (by simpa using hPow)

/-- finite survivor prefix の canonical critical completion word。 -/
def survivorCriticalCompletionWord
    {n : ℕ}
    (hn : 0 < n)
    (S : SurvivorParityCode n) :
    Critical.CriticalWord S.1.length :=
  admissibleParityCodeToCriticalWord
    (survivorCriticalCompletionParityCode hn S)

/-- positive physical depth では completion width も正。 -/
theorem survivorCriticalCompletion_width_pos
    {n : ℕ}
    (hn : 0 < n)
    (S : SurvivorParityCode n) :
    0 < S.1.length :=
  S.1.length_pos_of_pos hn

/-- completion word の proper prefix depth は元 survivor prefix と一致。 -/
theorem survivorCriticalCompletionWord_prefixTwoDepth
    {n : ℕ}
    (hn : 0 < n)
    (S : SurvivorParityCode n)
    {k : ℕ}
    (hk : k < S.1.length) :
    Word.prefixTwoDepth (survivorCriticalCompletionWord hn S).1 k =
      S.1.sizeUpTo k := by
  change
    (survivorCriticalCompletionComposition hn S).sizeUpTo k =
      S.1.sizeUpTo k
  exact survivorCriticalCompletion_sizeUpTo hn S hk

/-- completion から得る restricted critical partition。 -/
def survivorCriticalCompletionPartition
    {n : ℕ}
    (hn : 0 < n)
    (S : SurvivorParityCode n) :
    RestrictedCriticalPartition S.1.length :=
  criticalWordEquivRestrictedCriticalPartition
    S.1.length (survivorCriticalCompletion_width_pos hn S)
    (survivorCriticalCompletionWord hn S)

/--
completion partition の forward excess 座標は元 prefix の `D_k-k`。
-/
theorem survivorCriticalCompletionPartition_coordinate
    {n : ℕ}
    (hn : 0 < n)
    (S : SurvivorParityCode n)
    (k : Fin S.1.length) :
    (survivorCriticalCompletionPartition hn S).1 k =
      S.1.sizeUpTo k.1 - k.1 := by
  rw [survivorCriticalCompletionPartition]
  rw [restrictedCriticalPartition_criticalWord_coordinate
    (survivorCriticalCompletion_width_pos hn S)]
  rw [survivorCriticalCompletionWord_prefixTwoDepth hn S k.2]

/-- finite survivor prefix の proper column defect。 -/
def survivorPrefixDefect
    {n : ℕ}
    (S : SurvivorParityCode n)
    (k : Fin S.1.length) : ℕ :=
  Critical.beattyIndex k.1 - S.1.sizeUpTo k.1

/--
completion partition から復元する profile depth は survivor roof defect そのもの。
-/
theorem survivorCriticalCompletion_profile_eq_defect
    {n : ℕ}
    (hn : 0 < n)
    (S : SurvivorParityCode n)
    (k : Fin S.1.length) :
    RestrictedCriticalPartition.profile
        (survivorCriticalCompletionPartition hn S) k =
      survivorPrefixDefect S k := by
  unfold RestrictedCriticalPartition.profile survivorPrefixDefect
  rw [survivorCriticalCompletionPartition_coordinate hn S k]
  have hkLe : k.1 ≤ S.1.sizeUpTo k.1 :=
    le_sizeUpTo_of_le_length S.1 (Nat.le_of_lt k.2)
  omega

end Bridge
end Collatz3
