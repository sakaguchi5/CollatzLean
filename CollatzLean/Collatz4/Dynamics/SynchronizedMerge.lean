import CollatzLean.Collatz4.Dynamics.ThreePowerFamily

/-!
# Collatz4.Dynamics.SynchronizedMerge

開始時刻の異なる累積 Collatz 軌道を、同じ絶対時刻で比較するための一般層。

`accumulatedAt start time A` は、時刻 `start` に値 `A` から出発した軌道を
時刻 `time` まで進めた値を表す。

この語彙を使うと、例えば `3^n-1` と `3^m-1` から始まる候補が途中時刻で
合流したなら、共通終端時刻でも必ず同じ値になることを一つの一般定理で扱える。

M=7 の `2179 -> 97` のような圧縮は、この層の特殊化として構成する。
-/

namespace Collatz4.Dynamics

/--
時刻 `start` に自然数 `A` から出発した累積軌道を、絶対時刻 `time` で読む。

`time < start` では自然数減算が 0 に飽和するため、通常は `start ≤ time` の
条件と組み合わせて使う。
-/
def accumulatedAt (start time A : ℕ) : ℕ :=
  accumulatedRun (time - start) A

/-- 開始時刻そのものでは、まだ初期値 `A` にいる。 -/
@[simp] theorem accumulatedAt_start (start A : ℕ) :
    accumulatedAt start start A = A := by
  simp [accumulatedAt]

/--
開始時刻以後では、絶対時刻を 1 増やすことは `accumulatedStep` を 1 回進めることと同じ。
-/
theorem accumulatedAt_succ
    {start time A : ℕ}
    (hstart : start ≤ time) :
    accumulatedAt start (time + 1) A =
      accumulatedStep (accumulatedAt start time A) := by
  unfold accumulatedAt
  have hsub : time + 1 - start = (time - start) + 1 := by
    omega
  rw [hsub, accumulatedRun_succ_last]

/--
異なる開始時刻の二軌道が共通時刻 `s` で一致したなら、
それ以後の任意の共通時刻 `T` でも一致する。
-/
theorem accumulatedAt_eq_of_merge_at
    {startX startY s T x y : ℕ}
    (hXs : startX ≤ s)
    (hYs : startY ≤ s)
    (hsT : s ≤ T)
    (hmerge : accumulatedAt startX s x = accumulatedAt startY s y) :
    accumulatedAt startX T x = accumulatedAt startY T y := by
  unfold accumulatedAt at hmerge ⊢
  have hx : T - startX = (s - startX) + (T - s) := by
    omega
  have hy : T - startY = (s - startY) + (T - s) := by
    omega
  rw [hx, hy, accumulatedRun_add, accumulatedRun_add, hmerge]

/--
二つの時刻付き軌道が、時刻 `T` までのどこかで同期合流すること。

合流時刻 `s` 自体も witness として保持するので、後で代表軌道への圧縮証明に使える。
-/
def SynchronizedMergesBy
    (T startX x startY y : ℕ) : Prop :=
  ∃ s : ℕ,
    startX ≤ s ∧ startY ≤ s ∧ s ≤ T ∧
      accumulatedAt startX s x = accumulatedAt startY s y

/-- 同じ時刻付き軌道は、任意の終端時刻 `T` までに自分自身と同期合流する。 -/
theorem synchronizedMergesBy_refl
    {T start x : ℕ}
    (hstart : start ≤ T) :
    SynchronizedMergesBy T start x start x := by
  refine ⟨start, le_rfl, le_rfl, hstart, ?_⟩
  rfl

/-- 同期合流は左右を入れ替えても成り立つ。 -/
theorem synchronizedMergesBy_symm
    {T startX x startY y : ℕ}
    (h : SynchronizedMergesBy T startX x startY y) :
    SynchronizedMergesBy T startY y startX x := by
  rcases h with ⟨s, hXs, hYs, hsT, hxy⟩
  exact ⟨s, hYs, hXs, hsT, hxy.symm⟩

/--
時刻 `T` までに同期合流していれば、時刻 `T` での値は必ず一致する。

代表軌道へ圧縮した後、代表だけを終端まで計算すればよいことの基本定理。
-/
theorem accumulatedAt_eq_of_synchronizedMergesBy
    {T startX x startY y : ℕ}
    (h : SynchronizedMergesBy T startX x startY y) :
    accumulatedAt startX T x = accumulatedAt startY T y := by
  rcases h with ⟨s, hXs, hYs, hsT, hmerge⟩
  exact accumulatedAt_eq_of_merge_at hXs hYs hsT hmerge

/-- `3^n-1` を時刻 `n` から開始する標準候補軌道。 -/
def threePowerAt (n time : ℕ) : ℕ :=
  accumulatedAt n time (3 ^ n - 1)

/--
`3^n-1` 候補二本が時刻 `s` で合流したなら、その後の共通時刻 `T` でも一致する。
-/
theorem threePowerAt_eq_of_merge_at
    {n m s T : ℕ}
    (hns : n ≤ s)
    (hms : m ≤ s)
    (hsT : s ≤ T)
    (hmerge : threePowerAt n s = threePowerAt m s) :
    threePowerAt n T = threePowerAt m T := by
  exact accumulatedAt_eq_of_merge_at hns hms hsT hmerge

/-- `3^n-1` 候補同士の「時刻 T までの同期合流」。 -/
def ThreePowerMergesBy (T n m : ℕ) : Prop :=
  SynchronizedMergesBy T n (3 ^ n - 1) m (3 ^ m - 1)

/--
`3^n-1` の二候補が時刻 `T` までに同期合流すれば、時刻 `T` の終点は同じ。
-/
theorem threePowerAt_eq_of_mergesBy
    {T n m : ℕ}
    (h : ThreePowerMergesBy T n m) :
    threePowerAt n T = threePowerAt m T := by
  exact accumulatedAt_eq_of_synchronizedMergesBy h

/--
奇数指数 `2k+1` の候補は、次の偶数指数 `2k+2` の候補へ 1 段で合流する。
したがって `2k+2` 以後の任意の共通時刻で両者は同じ値を持つ。
-/
theorem threePowerAt_odd_eq_next
    (k time : ℕ)
    (h : 2 * k + 2 ≤ time) :
    threePowerAt (2 * k + 1) time =
      threePowerAt (2 * k + 2) time := by
  unfold threePowerAt accumulatedAt
  have hsub :
      time - (2 * k + 1) = (time - (2 * k + 2)) + 1 := by
    omega
  rw [hsub]
  exact accumulatedRun_threePow_odd_merge k (time - (2 * k + 2))

/--
上の局所合流を `ThreePowerMergesBy` の形で公開する。
代表圧縮側ではこちらを直接 certificate として使える。
-/
theorem threePower_odd_mergesBy_next
    (k T : ℕ)
    (hT : 2 * k + 2 ≤ T) :
    ThreePowerMergesBy T (2 * k + 1) (2 * k + 2) := by
  refine ⟨2 * k + 2, ?_, le_rfl, hT, ?_⟩
  · omega
  · unfold accumulatedAt
    have hleft : (2 * k + 2) - (2 * k + 1) = 1 := by omega
    have hright : (2 * k + 2) - (2 * k + 2) = 0 := by omega
    rw [hleft, hright]
    simp only [accumulatedRun_succ, accumulatedRun_zero]
    exact accumulatedStep_threePow_sub_one_odd k

end Collatz4.Dynamics
