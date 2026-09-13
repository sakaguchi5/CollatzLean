import CollatzLean.Collatz3.Bridge.FullFirstCrossingPartition
import CollatzLean.Collatz3.Bridge.ValidEndpointRuns

/-!
# Collatz3 Bridge: full first-crossing actual trajectory の完全分類

pure shape 側では既に

`FullFirstCrossingWord m ≃ RestrictedCriticalPartition m × ℕ`

を得た。ここでは valid word の canonical lift がすべて actual `Runs` になることを使い、
actual trajectory 全体を

`Σ P : RestrictedCriticalPartition m, ℕ × ℕ`

で完全分類する。

最初の自然数は terminal overshoot、二番目は canonical lift index である。
-/

namespace Collatz3
namespace Bridge

/--
幅 `m` の full first-crossing actual trajectory。
primitive data は full word、start/end、`Runs` だけ。
-/
abbrev ActualFullFirstCrossingTrajectory (m : ℕ) :=
  {t : Critical.FullFirstCrossingWord m × (ℕ × ℕ) //
    Runs t.1.1 t.2.1 t.2.2}

namespace ActualFullFirstCrossingTrajectory

/-- trajectory の full first-crossing word。 -/
def word
    {m : ℕ}
    (T : ActualFullFirstCrossingTrajectory m) :
    Critical.FullFirstCrossingWord m :=
  T.1.1

/-- trajectory の start。 -/
def start
    {m : ℕ}
    (T : ActualFullFirstCrossingTrajectory m) : ℕ :=
  T.1.2.1

/-- trajectory の endpoint。 -/
def endpoint
    {m : ℕ}
    (T : ActualFullFirstCrossingTrajectory m) : ℕ :=
  T.1.2.2

/-- trajectory は actual run。 -/
theorem run
    {m : ℕ}
    (T : ActualFullFirstCrossingTrajectory m) :
    Runs (word T).1 (start T) (endpoint T) :=
  T.2

/-- trajectory の finite Young partition。 -/
def partition
    {m : ℕ}
    (hm : 0 < m)
    (T : ActualFullFirstCrossingTrajectory m) :
    RestrictedCriticalPartition m :=
  (fullFirstCrossingWordEquivPartitionExtra m hm (word T)).1

/-- trajectory の terminal overshoot。 -/
def extraDepth
    {m : ℕ}
    (hm : 0 < m)
    (T : ActualFullFirstCrossingTrajectory m) : ℕ :=
  (fullFirstCrossingWordEquivPartitionExtra m hm (word T)).2

/-- partition と overshoot から trajectory の word が exact に戻る。 -/
theorem word_eq_fullWordOfPartitionExtra
    {m : ℕ}
    (hm : 0 < m)
    (T : ActualFullFirstCrossingTrajectory m) :
    word T = fullWordOfPartitionExtra hm (partition hm T) (extraDepth hm T) := by
  have h :=
    (fullFirstCrossingWordEquivPartitionExtra m hm).symm_apply_apply (word T)
  exact h.symm

end ActualFullFirstCrossingTrajectory

/-- `(P,s,k)` に対応する actual start。 -/
def fullLiftedStart
    {m : ℕ}
    (hm : 0 < m)
    (P : RestrictedCriticalPartition m)
    (s k : ℕ) : ℕ :=
  let W := fullWordOfPartitionExtra hm P s
  Word.canonicalStart W.1 + Word.oddEndpointModulus W.1 * k

/-- `(P,s,k)` に対応する actual endpoint。 -/
def fullLiftedEnd
    {m : ℕ}
    (hm : 0 < m)
    (P : RestrictedCriticalPartition m)
    (s k : ℕ) : ℕ :=
  let W := fullWordOfPartitionExtra hm P s
  Word.canonicalEnd W.1 + 2 * (3 ^ m) * k

/-- partition / overshoot / lift の各 code は actual run を実現する。 -/
theorem runs_fullLifted
    {m : ℕ}
    (hm : 0 < m)
    (P : RestrictedCriticalPartition m)
    (s k : ℕ) :
    Runs (fullWordOfPartitionExtra hm P s).1
      (fullLiftedStart hm P s k)
      (fullLiftedEnd hm P s k) := by
  let W := fullWordOfPartitionExtra hm P s
  have hRun :=
    Runs.canonicalLift
      W.2.valid
      (Critical.FullFirstCrossingWord.nonempty hm W)
      k
  have hPow : 3 ^ Word.oddSteps W.1 = 3 ^ m := by
    exact congrArg (fun n : ℕ => 3 ^ n) W.2.oddSteps_eq
  change
    Runs W.1
      (Word.canonicalStart W.1 + Word.oddEndpointModulus W.1 * k)
      (Word.canonicalEnd W.1 + 2 * (3 ^ m) * k)
  simpa only [hPow] using hRun

/-- code `(P,s,k)` から actual trajectory を作る。 -/
def actualFullTrajectoryOfCode
    {m : ℕ}
    (hm : 0 < m)
    (P : RestrictedCriticalPartition m)
    (s k : ℕ) :
    ActualFullFirstCrossingTrajectory m :=
  ⟨(fullWordOfPartitionExtra hm P s,
      (fullLiftedStart hm P s k, fullLiftedEnd hm P s k)),
    runs_fullLifted hm P s k⟩

@[simp] theorem word_actualFullTrajectoryOfCode
    {m : ℕ}
    (hm : 0 < m)
    (P : RestrictedCriticalPartition m)
    (s k : ℕ) :
    ActualFullFirstCrossingTrajectory.word
      (actualFullTrajectoryOfCode hm P s k) =
      fullWordOfPartitionExtra hm P s :=
  rfl

@[simp] theorem partition_actualFullTrajectoryOfCode
    {m : ℕ}
    (hm : 0 < m)
    (P : RestrictedCriticalPartition m)
    (s k : ℕ) :
    ActualFullFirstCrossingTrajectory.partition hm
      (actualFullTrajectoryOfCode hm P s k) = P := by
  unfold ActualFullFirstCrossingTrajectory.partition
  rw [word_actualFullTrajectoryOfCode]
  exact partition_fullWordOfPartitionExtra hm P s

@[simp] theorem extraDepth_actualFullTrajectoryOfCode
    {m : ℕ}
    (hm : 0 < m)
    (P : RestrictedCriticalPartition m)
    (s k : ℕ) :
    ActualFullFirstCrossingTrajectory.extraDepth hm
      (actualFullTrajectoryOfCode hm P s k) = s := by
  unfold ActualFullFirstCrossingTrajectory.extraDepth
  rw [word_actualFullTrajectoryOfCode]
  exact terminalExtraDepth_fullWordOfPartitionExtra hm P s

@[simp] theorem start_actualFullTrajectoryOfCode
    {m : ℕ}
    (hm : 0 < m)
    (P : RestrictedCriticalPartition m)
    (s k : ℕ) :
    ActualFullFirstCrossingTrajectory.start
      (actualFullTrajectoryOfCode hm P s k) =
      fullLiftedStart hm P s k :=
  rfl

@[simp] theorem endpoint_actualFullTrajectoryOfCode
    {m : ℕ}
    (hm : 0 < m)
    (P : RestrictedCriticalPartition m)
    (s k : ℕ) :
    ActualFullFirstCrossingTrajectory.endpoint
      (actualFullTrajectoryOfCode hm P s k) =
      fullLiftedEnd hm P s k :=
  rfl

namespace ActualFullFirstCrossingTrajectory

/-- 任意の full actual trajectory は一意な canonical lift index を持つ。 -/
theorem existsUnique_liftIndex
    {m : ℕ}
    (hm : 0 < m)
    (T : ActualFullFirstCrossingTrajectory m) :
    ∃! k : ℕ,
      start T = fullLiftedStart hm (partition hm T) (extraDepth hm T) k ∧
      endpoint T = fullLiftedEnd hm (partition hm T) (extraDepth hm T) k := by
  let W := word T
  have hLift :=
    (Runs.iff_exists_canonicalLift_of_valid_nonempty
      W.2.valid (Critical.FullFirstCrossingWord.nonempty hm W)).1 T.run
  rcases hLift with ⟨k, hx, hy⟩
  have hWord :
      fullWordOfPartitionExtra hm (partition hm T) (extraDepth hm T) = W := by
    exact (word_eq_fullWordOfPartitionExtra hm T).symm
  have hx' :
      start T = fullLiftedStart hm (partition hm T) (extraDepth hm T) k := by
    unfold fullLiftedStart
    rw [hWord]
    exact hx
  have hy' :
      endpoint T = fullLiftedEnd hm (partition hm T) (extraDepth hm T) k := by
    unfold fullLiftedEnd
    rw [hWord]
    have hPow : 3 ^ Word.oddSteps W.1 = 3 ^ m := by
      exact congrArg (fun n : ℕ => 3 ^ n) W.2.oddSteps_eq
    simpa only [hPow] using hy
  refine ⟨k, ⟨hx', hy'⟩, ?_⟩
  intro l hl
  have hEq :
      fullLiftedStart hm (partition hm T) (extraDepth hm T) k =
        fullLiftedStart hm (partition hm T) (extraDepth hm T) l :=
    hx'.symm.trans hl.1
  unfold fullLiftedStart at hEq
  let V := fullWordOfPartitionExtra hm (partition hm T) (extraDepth hm T)
  have hMul :
      Word.oddEndpointModulus V.1 * k =
        Word.oddEndpointModulus V.1 * l :=
    Nat.add_left_cancel hEq
  exact (Nat.mul_left_cancel (Word.oddEndpointModulus_pos V.1) hMul).symm

/-- trajectory の一意な canonical lift index。 -/
noncomputable def liftIndex
    {m : ℕ}
    (hm : 0 < m)
    (T : ActualFullFirstCrossingTrajectory m) : ℕ :=
  Classical.choose (existsUnique_liftIndex hm T).exists

/-- 選ばれた lift index は exact start/end formulas を満たす。 -/
theorem liftIndex_spec
    {m : ℕ}
    (hm : 0 < m)
    (T : ActualFullFirstCrossingTrajectory m) :
    start T = fullLiftedStart hm (partition hm T) (extraDepth hm T) (liftIndex hm T) ∧
    endpoint T = fullLiftedEnd hm (partition hm T) (extraDepth hm T) (liftIndex hm T) := by
  exact Classical.choose_spec (existsUnique_liftIndex hm T).exists

/-- formula を満たす index は選ばれた lift index と一致。 -/
theorem liftIndex_eq_of_spec
    {m : ℕ}
    (hm : 0 < m)
    (T : ActualFullFirstCrossingTrajectory m)
    {k : ℕ}
    (hk :
      start T = fullLiftedStart hm (partition hm T) (extraDepth hm T) k ∧
      endpoint T = fullLiftedEnd hm (partition hm T) (extraDepth hm T) k) :
    liftIndex hm T = k := by
  exact (existsUnique_liftIndex hm T).unique (liftIndex_spec hm T) hk

end ActualFullFirstCrossingTrajectory

/-- ordinary product 版の完全分類。 -/
noncomputable def actualFullTrajectoryEquivPartitionExtraLiftProd
    (m : ℕ)
    (hm : 0 < m) :
    ActualFullFirstCrossingTrajectory m ≃
      ((RestrictedCriticalPartition m × ℕ) × ℕ) where
  toFun T :=
    ((ActualFullFirstCrossingTrajectory.partition hm T,
        ActualFullFirstCrossingTrajectory.extraDepth hm T),
      ActualFullFirstCrossingTrajectory.liftIndex hm T)
  invFun code :=
    actualFullTrajectoryOfCode hm code.1.1 code.1.2 code.2
  left_inv T := by
    apply Subtype.ext
    apply Prod.ext
    · change
        fullWordOfPartitionExtra hm
            (ActualFullFirstCrossingTrajectory.partition hm T)
            (ActualFullFirstCrossingTrajectory.extraDepth hm T) =
          ActualFullFirstCrossingTrajectory.word T
      exact (ActualFullFirstCrossingTrajectory.word_eq_fullWordOfPartitionExtra hm T).symm
    · apply Prod.ext
      · change
          fullLiftedStart hm
              (ActualFullFirstCrossingTrajectory.partition hm T)
              (ActualFullFirstCrossingTrajectory.extraDepth hm T)
              (ActualFullFirstCrossingTrajectory.liftIndex hm T) =
            ActualFullFirstCrossingTrajectory.start T
        exact (ActualFullFirstCrossingTrajectory.liftIndex_spec hm T).1.symm
      · change
          fullLiftedEnd hm
              (ActualFullFirstCrossingTrajectory.partition hm T)
              (ActualFullFirstCrossingTrajectory.extraDepth hm T)
              (ActualFullFirstCrossingTrajectory.liftIndex hm T) =
            ActualFullFirstCrossingTrajectory.endpoint T
        exact (ActualFullFirstCrossingTrajectory.liftIndex_spec hm T).2.symm
  right_inv code := by
    rcases code with ⟨⟨P, s⟩, k⟩
    apply Prod.ext
    · apply Prod.ext
      · exact partition_actualFullTrajectoryOfCode hm P s k
      · exact extraDepth_actualFullTrajectoryOfCode hm P s k
    · apply ActualFullFirstCrossingTrajectory.liftIndex_eq_of_spec hm
      constructor <;>
        simp [partition_actualFullTrajectoryOfCode,
          extraDepth_actualFullTrajectoryOfCode]

/-- product と requested sigma code `Σ P, ℕ × ℕ` の自明な同値。 -/
def partitionExtraLiftProdEquivSigma
    (m : ℕ) :
    ((RestrictedCriticalPartition m × ℕ) × ℕ) ≃
      (Σ _P : RestrictedCriticalPartition m, ℕ × ℕ) where
  toFun code := ⟨code.1.1, (code.1.2, code.2)⟩
  invFun code := ((code.1, code.2.1), code.2.2)
  left_inv code := by
    rcases code with ⟨⟨P, s⟩, k⟩
    rfl
  right_inv code := by
    rcases code with ⟨P, ⟨s, k⟩⟩
    rfl

/--
full actual first-crossing trajectory の完全座標。

`P` が finite Young shape、`s` が terminal overshoot、`k` が actual lift index。
-/
noncomputable def actualFullTrajectoryEquivRestrictedPartitionSigma
    (m : ℕ)
    (hm : 0 < m) :
    ActualFullFirstCrossingTrajectory m ≃
      (Σ _P : RestrictedCriticalPartition m, ℕ × ℕ) :=
  (actualFullTrajectoryEquivPartitionExtraLiftProd m hm).trans
    (partitionExtraLiftProdEquivSigma m)

end Bridge
end Collatz3
