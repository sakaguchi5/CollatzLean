import CollatzLean.Collatz3.Bridge.CriticalActualFiber

/-!
# Collatz3 Bridge: actual critical trajectory の完全分類

固定幅 `m > 0` の actual critical trajectory を

`restricted partition × lift index`

で完全分類する。

数学的には

`ActualCriticalTrajectory m ≃ Σ P : RestrictedCriticalPartition m, ℕ`

であり、右辺の `P` が有限 Young shape、`k : ℕ` がその上の無限 actual fiber を表す。

さらに start だけを忘れずに見ると、幅 `m` の actual critical starts は
相異なる `criticalPartitionCount m` 本の合同類

`R(P) + criticalStartModulus m * k`

の和集合として記述される。
-/

namespace Collatz3
namespace Bridge

/--
幅 `m` の actual critical trajectory。

新しい数学データは足さず、既存 `CriticalWord m`、start/end、`Runs` の
薄い subtype として持つ。
-/
abbrev ActualCriticalTrajectory (m : ℕ) :=
  {t : Critical.CriticalWord m × (ℕ × ℕ) //
    Runs t.1.1 t.2.1 t.2.2}

namespace ActualCriticalTrajectory

/-- trajectory が持つ critical word。 -/
def word
    {m : ℕ}
    (T : ActualCriticalTrajectory m) :
    Critical.CriticalWord m :=
  T.1.1

/-- trajectory の start。 -/
def start
    {m : ℕ}
    (T : ActualCriticalTrajectory m) : ℕ :=
  T.1.2.1

/-- trajectory の endpoint。 -/
def endpoint
    {m : ℕ}
    (T : ActualCriticalTrajectory m) : ℕ :=
  T.1.2.2

/-- trajectory は actual run。 -/
theorem run
    {m : ℕ}
    (T : ActualCriticalTrajectory m) :
    Runs (word T).1 (start T) (endpoint T) :=
  T.2

/-- trajectory は既存 `ActualFirstPassage` を実現する。 -/
theorem actualFirstPassage
    {m : ℕ}
    (T : ActualCriticalTrajectory m) :
    ActualFirstPassage (word T).1 (start T) (endpoint T) := by
  exact ⟨T.run, criticalWord_criticalFirstPassage (word T)⟩

/-- trajectory の finite base partition。 -/
def partition
    {m : ℕ}
    (hm : 0 < m)
    (T : ActualCriticalTrajectory m) :
    RestrictedCriticalPartition m :=
  criticalWordEquivRestrictedCriticalPartition m hm (word T)

@[simp] theorem wordOfPartition_partition
    {m : ℕ}
    (hm : 0 < m)
    (T : ActualCriticalTrajectory m) :
    criticalWordOfPartition m hm (partition hm T) = word T := by
  exact criticalWordOfPartition_partition hm (word T)

/-- partition と lift index から actual trajectory を作る。 -/
def ofPartitionLift
    {m : ℕ}
    (hm : 0 < m)
    (P : RestrictedCriticalPartition m)
    (k : ℕ) :
    ActualCriticalTrajectory m :=
  ⟨
    (criticalWordOfPartition m hm P,
      (liftedCriticalStart hm P k,
        liftedCriticalEnd hm P k)),
    runs_liftedCritical hm P k
  ⟩

@[simp] theorem partition_ofPartitionLift
    {m : ℕ}
    (hm : 0 < m)
    (P : RestrictedCriticalPartition m)
    (k : ℕ) :
    partition hm (ofPartitionLift hm P k) = P := by
  exact partition_criticalWordOfPartition hm P

@[simp] theorem start_ofPartitionLift
    {m : ℕ}
    (hm : 0 < m)
    (P : RestrictedCriticalPartition m)
    (k : ℕ) :
    start (ofPartitionLift hm P k) = liftedCriticalStart hm P k :=
  rfl

@[simp] theorem endpoint_ofPartitionLift
    {m : ℕ}
    (hm : 0 < m)
    (P : RestrictedCriticalPartition m)
    (k : ℕ) :
    endpoint (ofPartitionLift hm P k) = liftedCriticalEnd hm P k :=
  rfl

/--
任意の actual critical trajectory は、その partition 上の一意な lift index を持つ。
-/
theorem existsUnique_liftIndex
    {m : ℕ}
    (hm : 0 < m)
    (T : ActualCriticalTrajectory m) :
    ∃! k : ℕ,
      start T = liftedCriticalStart hm (partition hm T) k ∧
      endpoint T = liftedCriticalEnd hm (partition hm T) k := by
  let W := word T
  let P := partition hm T
  have hLift :=
    (Runs.iff_exists_canonicalLift_of_valid_nonempty
      W.2.valid (criticalWord_nonempty hm W)).1 T.run
  rcases hLift with ⟨k, hx, hy⟩
  have hWord : criticalWordOfPartition m hm P = W := by
    dsimp [P, W]
    exact wordOfPartition_partition hm T
  have hx' :
      start T = liftedCriticalStart hm P k := by
    unfold liftedCriticalStart
    rw [hWord]
    rw [← oddEndpointModulus_eq_criticalStartModulus W]
    exact hx
  have hy' :
      endpoint T = liftedCriticalEnd hm P k := by
    unfold liftedCriticalEnd
    rw [hWord]
    have hPow :
        3 ^ Word.oddSteps W.1 = 3 ^ m := by
      exact congrArg (fun n : ℕ => 3 ^ n) W.2.oddSteps_eq
    simpa only [hPow] using hy
  refine ⟨k, ⟨hx', hy'⟩, ?_⟩
  intro l hl
  have hEq :
      liftedCriticalStart hm P k =
        liftedCriticalStart hm P l :=
    hx'.symm.trans hl.1
  unfold liftedCriticalStart at hEq
  have hMul : criticalStartModulus m * k = criticalStartModulus m * l :=
    Nat.add_left_cancel hEq
  exact (Nat.mul_left_cancel (criticalStartModulus_pos m) hMul).symm

/-- trajectory に対応する一意な lift index。 -/
noncomputable def liftIndex
    {m : ℕ}
    (hm : 0 < m)
    (T : ActualCriticalTrajectory m) : ℕ :=
  Classical.choose (existsUnique_liftIndex hm T).exists

/-- 選ばれた lift index は start/end の exact formulas を満たす。 -/
theorem liftIndex_spec
    {m : ℕ}
    (hm : 0 < m)
    (T : ActualCriticalTrajectory m) :
    start T = liftedCriticalStart hm (partition hm T) (liftIndex hm T) ∧
    endpoint T = liftedCriticalEnd hm (partition hm T) (liftIndex hm T) := by
  exact Classical.choose_spec (existsUnique_liftIndex hm T).exists

/-- formula を満たす index は選ばれた lift index と一致する。 -/
theorem liftIndex_eq_of_spec
    {m : ℕ}
    (hm : 0 < m)
    (T : ActualCriticalTrajectory m)
    {k : ℕ}
    (hk :
      start T = liftedCriticalStart hm (partition hm T) k ∧
      endpoint T = liftedCriticalEnd hm (partition hm T) k) :
    liftIndex hm T = k := by
  exact
    (existsUnique_liftIndex hm T).unique
      (liftIndex_spec hm T) hk

end ActualCriticalTrajectory

/--
まず ordinary product として
`ActualCriticalTrajectory m ≃ RestrictedCriticalPartition m × ℕ`
を作る。
-/
noncomputable def actualCriticalTrajectoryEquivPartitionLiftProd
    (m : ℕ)
    (hm : 0 < m) :
    ActualCriticalTrajectory m ≃
      (RestrictedCriticalPartition m × ℕ) where
  toFun T :=
    (ActualCriticalTrajectory.partition hm T,
      ActualCriticalTrajectory.liftIndex hm T)
  invFun code :=
    ActualCriticalTrajectory.ofPartitionLift hm code.1 code.2
  left_inv T := by
    apply Subtype.ext
    apply Prod.ext
    · change
        criticalWordOfPartition m hm
            (ActualCriticalTrajectory.partition hm T) =
          ActualCriticalTrajectory.word T
      exact ActualCriticalTrajectory.wordOfPartition_partition hm T
    · apply Prod.ext
      · change
          liftedCriticalStart hm
              (ActualCriticalTrajectory.partition hm T)
              (ActualCriticalTrajectory.liftIndex hm T) =
            ActualCriticalTrajectory.start T
        exact (ActualCriticalTrajectory.liftIndex_spec hm T).1.symm
      · change
          liftedCriticalEnd hm
              (ActualCriticalTrajectory.partition hm T)
              (ActualCriticalTrajectory.liftIndex hm T) =
            ActualCriticalTrajectory.endpoint T
        exact (ActualCriticalTrajectory.liftIndex_spec hm T).2.symm
  right_inv code := by
    rcases code with ⟨P, k⟩
    apply Prod.ext
    · exact
        ActualCriticalTrajectory.partition_ofPartitionLift hm P k
    · apply ActualCriticalTrajectory.liftIndex_eq_of_spec hm
      constructor
      · rw [ActualCriticalTrajectory.partition_ofPartitionLift hm P k]
        rfl
      · rw [ActualCriticalTrajectory.partition_ofPartitionLift hm P k]
        rfl

/-- constant fiber の product と dependent sum `Σ P, ℕ` の自明な同値。 -/
def partitionLiftProdEquivSigma
    (m : ℕ) :
    (RestrictedCriticalPartition m × ℕ) ≃
      (Σ _P : RestrictedCriticalPartition m, ℕ) where
  toFun code := ⟨code.1, code.2⟩
  invFun code := (code.1, code.2)
  left_inv code := by
    rcases code with ⟨P, k⟩
    rfl
  right_inv code := by
    rcases code with ⟨P, k⟩
    rfl

/--
固定幅の actual critical trajectory の完全分類。

`ActualCriticalTrajectory m ≃ Σ P : RestrictedCriticalPartition m, ℕ`

有限 Young shape `P` と一本の lift index `k` が trajectory の完全座標になる。
-/
noncomputable def actualCriticalTrajectoryEquivRestrictedPartitionSigma
    (m : ℕ)
    (hm : 0 < m) :
    ActualCriticalTrajectory m ≃
      (Σ _P : RestrictedCriticalPartition m, ℕ) :=
  (actualCriticalTrajectoryEquivPartitionLiftProd m hm).trans
    (partitionLiftProdEquivSigma m)

/-- 幅 `m` の actual critical start であるという薄い述語。 -/
def IsActualCriticalStart
    (m x : ℕ) : Prop :=
  ∃ W : Critical.CriticalWord m,
    ∃ y : ℕ,
      Runs W.1 x y

/--
幅 `m > 0` の actual critical starts は、restricted partition ごとの
pairwise disjoint arithmetic fiber の和集合と exact に一致する。
-/
theorem isActualCriticalStart_iff_exists_partition_lift
    {m x : ℕ}
    (hm : 0 < m) :
    IsActualCriticalStart m x ↔
      ∃ P : RestrictedCriticalPartition m,
        ∃ k : ℕ,
          x = liftedCriticalStart hm P k := by
  constructor
  · rintro ⟨W, y, hRun⟩
    let T : ActualCriticalTrajectory m :=
      ⟨(W, (x, y)), hRun⟩
    refine
      ⟨ActualCriticalTrajectory.partition hm T,
        ActualCriticalTrajectory.liftIndex hm T, ?_⟩
    exact (ActualCriticalTrajectory.liftIndex_spec hm T).1
  · rintro ⟨P, k, hx⟩
    refine
      ⟨criticalWordOfPartition m hm P,
        liftedCriticalEnd hm P k, ?_⟩
    rw [hx]
    exact runs_liftedCritical hm P k

/--
異なる base partition が生成する start 集合は互いに素。
これは「幅 `m` の actual starts は相異なる合同類の族」という直接形。
-/
theorem actualCriticalStart_fibers_disjoint
    {m : ℕ}
    (hm : 0 < m)
    {P Q : RestrictedCriticalPartition m}
    (hPQ : P ≠ Q) :
    ∀ k l : ℕ,
      liftedCriticalStart hm P k ≠
        liftedCriticalStart hm Q l := by
  intro k l
  exact liftedCriticalStart_ne_of_partition_ne hm hPQ k l

end Bridge
end Collatz3
