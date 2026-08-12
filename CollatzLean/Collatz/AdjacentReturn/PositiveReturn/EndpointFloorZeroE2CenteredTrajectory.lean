import CollatzLean.Collatz.AdjacentReturn.PositiveReturn.EndpointFloorZeroE2ZeroDecoder

/-!
# E2 quotient-zero survivor の pure centered trajectory reduction

`E2ZeroSurvivorData` に残る数学を有限語・canonical residue・budget から切り離し、
自然数列だけの問題へ圧縮する。

長さ `m`、return coordinate `n`、terminal endpoint `T` に対して

* `prefixExponent k` : inner word の先頭 `k` 文字の cumulative exponent
* `suffixExponent r` : inner word の末尾 `r` 文字の cumulative exponent
* `backwardExponent r` : suffix を `r` から `r+1` へ一文字左へ伸ばす exponent
* `halfGap r` : suffix start `x_r = T + 2 * halfGap r`

を保持する。

最終的に残る条件は pure arithmetic で、

* `m > 6*n`
* `h_0 = 0`, `h_r > 0`
* `T + 5 = 16*h_m + 18*n`
* 全 proper prefix expanding
* 全 nonempty suffix contracting
* whole `[1,2] ++ u` は terminal contracting
* exponent 累積の prefix/suffix compatibility
* centered backward recurrence

だけである。

したがって `NoE2ZeroCenteredTrajectory` を証明すれば
`NoE2ZeroSurvivor`、従って E2 inner quotient-zero branch を排除できる。
-/

namespace Collatz
namespace AdjacentReturn
namespace PositiveReturn
namespace EndpointFloorZero

private theorem exists_drop_eq_cons_drop_succ
    {α : Type*}
    (w : List α) {k : ℕ}
    (hk : k < w.length) :
    ∃ a : α, w.drop k = a :: w.drop (k + 1) := by
  induction w generalizing k with
  | nil =>
      simp at hk
  | cons a w ih =>
      cases k with
      | zero =>
          exact ⟨a, by simp⟩
      | succ k =>
          have hk' : k < w.length := by
            simpa using hk
          obtain ⟨b, hb⟩ := ih hk'
          refine ⟨b, ?_⟩
          simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hb

namespace E2BranchData

/--
inner suffix を `r` 文字から `r+1` 文字へ一文字左へ伸ばす exponent は存在し、正。
-/
theorem exists_zeroSuffixWord_succ_exponent
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E2BranchData v boundary n d u)
    {r : ℕ}
    (hr : r < u.length) :
    ∃ e : ℕ,
      0 < e ∧
      B.zeroSuffixWord (r + 1) =
        e :: B.zeroSuffixWord r := by
  let k := u.length - (r + 1)
  have hk : k < u.length := by
    dsimp [k]
    omega
  obtain ⟨e, heDrop⟩ :=
    exists_drop_eq_cons_drop_succ u hk
  have hkSucc : k + 1 = u.length - r := by
    dsimp [k]
    omega
  have heMemDrop : e ∈ u.drop k := by
    rw [heDrop]
    simp
  have heMem : e ∈ u := by
    have hdecomp : u.take k ++ u.drop k = u :=
      List.take_append_drop k u
    rw [← hdecomp]
    exact List.mem_append.mpr (Or.inr heMemDrop)
  have hePos : 0 < e :=
    B.inner_valid e heMem
  refine ⟨e, hePos, ?_⟩
  dsimp [zeroSuffixWord]
  change
    u.drop (u.length - (r + 1)) =
      e :: u.drop (u.length - r)
  change u.drop k = e :: u.drop (u.length - r)
  rw [← hkSucc]
  exact heDrop

/--
backward index `r` の一文字 exponent。
範囲外では0に固定する。
-/
noncomputable def zeroBackwardExponent
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E2BranchData v boundary n d u)
    (r : ℕ) : ℕ :=
  if hr : r < u.length then
    Nat.find (B.exists_zeroSuffixWord_succ_exponent hr)
  else
    0

/-- backward exponent は正で、実際に suffix を一文字伸ばす。 -/
theorem zeroBackwardExponent_spec
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E2BranchData v boundary n d u)
    {r : ℕ}
    (hr : r < u.length) :
    0 < B.zeroBackwardExponent r ∧
      B.zeroSuffixWord (r + 1) =
        B.zeroBackwardExponent r :: B.zeroSuffixWord r := by
  unfold zeroBackwardExponent
  rw [dif_pos hr]
  exact Nat.find_spec (B.exists_zeroSuffixWord_succ_exponent hr)

/-- suffix cumulative exponent の一段 recurrence。 -/
theorem zeroSuffixExponent_succ
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E2BranchData v boundary n d u)
    {r : ℕ}
    (hr : r < u.length) :
    B.zeroSuffixExponent (r + 1) =
      B.zeroBackwardExponent r + B.zeroSuffixExponent r := by
  have hword := (B.zeroBackwardExponent_spec hr).2
  dsimp [zeroSuffixExponent]
  rw [hword]
  exact Word.twoSteps_cons _ _

/-- inner prefix `k` 文字の cumulative exponent。 -/
def zeroPrefixExponent
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (_B : E2BranchData v boundary n d u)
    (k : ℕ) : ℕ :=
  Word.twoSteps (u.take k)

/-- prefix と complementary suffix の exponent は total exponent へ exact に分解する。 -/
theorem zeroExponent_split
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E2BranchData v boundary n d u)
    {k : ℕ}
    (hk : k ≤ u.length) :
    B.zeroPrefixExponent k +
        B.zeroSuffixExponent (u.length - k) =
      B.zeroSuffixExponent u.length := by
  have hidx :
      u.length - (u.length - k) = k := by
    omega
  have hdecomp :
      u.take k ++ u.drop k = u :=
    List.take_append_drop k u
  have htwo := congrArg Word.twoSteps hdecomp
  rw [Word.twoSteps_append] at htwo
  dsimp [zeroPrefixExponent, zeroSuffixExponent, zeroSuffixWord]
  rw [hidx]
  simpa using htwo

/-- inner prefix `k` 文字を whole `[1,2]` の後へ置いた proper prefix は expanding。 -/
theorem zeroPrefix_expanding
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E2BranchData v boundary n d u)
    {k : ℕ}
    (hk : k < u.length) :
    2 ^ (3 + B.zeroPrefixExponent k) <
      3 ^ (k + 2) := by
  have hwholeLen :
      k + 2 < (1 :: v).length := by
    rw [B.tail_eq]
    simp only [List.length_cons]
    omega
  have hExp :=
    B.packet.paradoxical.firstCrossing.properExpanding
      (k + 2) (by omega) hwholeLen
  rw [B.tail_eq] at hExp
  have htake :
      (1 :: 2 :: u).take (k + 2) =
        1 :: 2 :: u.take k := by
    rw [show k + 2 = Nat.succ (Nat.succ k) by omega]
    simp
  rw [htake] at hExp
  have htakeLen :
      (u.take k).length = k :=
    List.length_take_of_le (Nat.le_of_lt hk)
  simpa [
    Word.Expanding,
    Word.oddSteps,
    Word.twoSteps,
    zeroPrefixExponent,
    htakeLen,
    Nat.add_assoc,
    Nat.add_comm,
    Nat.add_left_comm
  ] using hExp

/-- whole `[1,2] ++ u` の terminal contracting を pure exponent inequality にする。 -/
theorem zeroWhole_contracting
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E2BranchData v boundary n d u) :
    9 * 3 ^ u.length <
      8 * 2 ^ B.zeroSuffixExponent u.length := by
  have hC :=
    B.packet.paradoxical.firstCrossing.terminalContracting
  rw [B.tail_eq] at hC
  have hfull : B.zeroSuffixWord u.length = u := by
    dsimp [zeroSuffixWord]
    simp
  have hK : B.zeroSuffixExponent u.length = Word.twoSteps u := by
    dsimp [zeroSuffixExponent]
    rw [hfull]
  rw [hK]
  simpa [
    Word.Contracting,
    Word.oddSteps,
    Word.twoSteps,
    pow_add,
    Nat.add_assoc,
    Nat.add_comm,
    Nat.add_left_comm,
    Nat.mul_comm
  ] using hC

end E2BranchData

/--
E2 ZERO survivor から抽出される pure arithmetic centered trajectory。

この structure 以後は `Word`、canonical residue、Runs、budget を一切参照しない。
-/
structure E2ZeroCenteredTrajectoryData : Type where
  length : ℕ
  n : ℕ
  endpoint : ℕ
  prefixExponent : ℕ → ℕ
  suffixExponent : ℕ → ℕ
  backwardExponent : ℕ → ℕ
  halfGap : ℕ → ℕ

  seven_le_length : 7 ≤ length
  n_pos : 0 < n
  six_mul_n_lt_length : 6 * n < length

  halfGap_zero : halfGap 0 = 0
  halfGap_pos :
    ∀ r : ℕ, 0 < r → r ≤ length → 0 < halfGap r

  endpoint_balance :
    endpoint + 5 = 16 * halfGap length + 18 * n

  suffixExponent_zero : suffixExponent 0 = 0
  backwardExponent_pos :
    ∀ r : ℕ, r < length → 0 < backwardExponent r
  suffixExponent_succ :
    ∀ r : ℕ, r < length →
      suffixExponent (r + 1) =
        backwardExponent r + suffixExponent r

  exponent_split :
    ∀ k : ℕ, k ≤ length →
      prefixExponent k + suffixExponent (length - k) =
        suffixExponent length

  prefix_expanding :
    ∀ k : ℕ, k < length →
      2 ^ (3 + prefixExponent k) < 3 ^ (k + 2)

  suffix_contracting :
    ∀ r : ℕ, 0 < r → r ≤ length →
      3 ^ r < 2 ^ suffixExponent r

  whole_contracting :
    9 * 3 ^ length < 8 * 2 ^ suffixExponent length

  first_backward_exponent_eq_one :
    backwardExponent (length - 1) = 1

  step_recurrence :
    ∀ r : ℕ, r < length →
      6 * halfGap (r + 1) + 1 + 3 * endpoint =
        2 ^ backwardExponent r * endpoint +
          2 ^ (backwardExponent r + 1) * halfGap r

namespace E2ZeroCenteredTrajectoryData

/-- `sigma = m - 6*n`。 -/
def sigma (D : E2ZeroCenteredTrajectoryData) : ℕ :=
  D.length - 6 * D.n

/-- centered trajectory では `sigma > 0`。 -/
theorem sigma_pos (D : E2ZeroCenteredTrajectoryData) :
    0 < D.sigma := by
  have h := D.six_mul_n_lt_length
  dsimp [sigma]
  omega

/-- terminal endpoint は正。 -/
theorem endpoint_pos (D : E2ZeroCenteredTrajectoryData) :
    0 < D.endpoint := by
  have h7 := D.seven_le_length
  have hm : 0 < D.length := by omega
  have hh := D.halfGap_pos D.length hm le_rfl
  have hn := D.n_pos
  have hbal := D.endpoint_balance
  omega

/-- full half-gap は正。 -/
theorem full_halfGap_pos (D : E2ZeroCenteredTrajectoryData) :
    0 < D.halfGap D.length := by
  have h7 := D.seven_le_length
  have hm : 0 < D.length := by omega
  exact D.halfGap_pos D.length hm le_rfl

/--
最初の forward exponent `1` と endpoint balance を recurrence に入れた
penultimate exact relation。

`2*h_(m-1)+2 = 11*h_m+9*n`。
-/
theorem penultimateHalfGap
    (D : E2ZeroCenteredTrajectoryData) :
    2 * D.halfGap (D.length - 1) + 2 =
      11 * D.halfGap D.length + 9 * D.n := by
  have h7 := D.seven_le_length
  have hm : 0 < D.length := by
    omega
  have hr : D.length - 1 < D.length := by
    omega
  have hrec := D.step_recurrence (D.length - 1) hr
  rw [D.first_backward_exponent_eq_one] at hrec
  norm_num at hrec
  have hidx : D.length - 1 + 1 = D.length := by
    omega
  rw [hidx] at hrec
  nlinarith [D.endpoint_balance]

/-- second forward exponent は `1` または `2`。 -/
theorem secondBackwardExponent_one_or_two
    (D : E2ZeroCenteredTrajectoryData) :
    D.backwardExponent (D.length - 2) = 1 ∨
      D.backwardExponent (D.length - 2) = 2 := by
  have h7 := D.seven_le_length
  have hm2 : 2 < D.length := by
    omega
  have hr1 : D.length - 1 < D.length := by
    omega
  have hr2 : D.length - 2 < D.length := by
    omega
  have hpos :=
    D.backwardExponent_pos (D.length - 2) hr2
  have hK1 :=
    D.suffixExponent_succ (D.length - 1) hr1
  have hK2 :=
    D.suffixExponent_succ (D.length - 2) hr2
  have hsplit :=
    D.exponent_split 2 (by omega)
  have hfirst :=
    D.first_backward_exponent_eq_one
  have hsub1 :
      D.length - 1 + 1 = D.length := by
    omega
  have hsub2 :
      D.length - 2 + 1 = D.length - 1 := by
    omega
  rw [hsub1, hfirst] at hK1
  rw [hsub2] at hK2
  have hPrefix :
      D.prefixExponent 2 =
        D.backwardExponent (D.length - 2) + 1 := by
    omega
  have hExp :=
    D.prefix_expanding 2 (by omega)
  rw [hPrefix] at hExp
  by_contra hnot
  have hge :
      3 ≤ D.backwardExponent (D.length - 2) := by
    omega
  have hpow :
      2 ^ 7 ≤
        2 ^ (3 + (D.backwardExponent (D.length - 2) + 1)) :=
    Nat.pow_le_pow_right
      (by omega : 0 < (2 : ℕ))
      (by omega)
  norm_num at hpow hExp
  omega

/-- second forward exponent `1` の centered exact relation。 -/
theorem secondStep_one_relation
    (D : E2ZeroCenteredTrajectoryData)
    (he : D.backwardExponent (D.length - 2) = 1) :
    4 * D.halfGap (D.length - 2) + 10 =
      49 * D.halfGap D.length + 45 * D.n := by
  have h7 := D.seven_le_length
  have hr : D.length - 2 < D.length := by omega
  have hidx : D.length - 2 + 1 = D.length - 1 := by omega
  have hrec := D.step_recurrence (D.length - 2) hr
  rw [he, hidx] at hrec
  norm_num at hrec
  have hpen := D.penultimateHalfGap
  nlinarith [D.endpoint_balance]

/-- second forward exponent `2` の centered exact relation。 -/
theorem secondStep_two_relation
    (D : E2ZeroCenteredTrajectoryData)
    (he : D.backwardExponent (D.length - 2) = 2) :
    8 * D.halfGap (D.length - 2) =
      17 * D.halfGap D.length + 9 * D.n := by
  have h7 := D.seven_le_length
  have hr : D.length - 2 < D.length := by omega
  have hidx : D.length - 2 + 1 = D.length - 1 := by omega
  have hrec := D.step_recurrence (D.length - 2) hr
  rw [he, hidx] at hrec
  norm_num at hrec
  have hpen := D.penultimateHalfGap
  nlinarith [D.endpoint_balance]

/-- second step は二つの explicit Diophantine relation の一方へ落ちる。 -/
theorem secondStepOutcome
    (D : E2ZeroCenteredTrajectoryData) :
    (4 * D.halfGap (D.length - 2) + 10 =
        49 * D.halfGap D.length + 45 * D.n) ∨
      (8 * D.halfGap (D.length - 2) =
        17 * D.halfGap D.length + 9 * D.n) := by
  rcases D.secondBackwardExponent_one_or_two with h1 | h2
  · exact Or.inl (D.secondStep_one_relation h1)
  · exact Or.inr (D.secondStep_two_relation h2)

end E2ZeroCenteredTrajectoryData

namespace E2ZeroSurvivorData

/--
E2 ZERO survivor を pure centered trajectory へ完全に忘却する。
-/
noncomputable def toCenteredTrajectory
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    {B : E2BranchData v boundary n d u}
    (Z : E2ZeroSurvivorData B) :
    E2ZeroCenteredTrajectoryData := by
  classical
  refine {
    length := u.length
    n := n
    endpoint := Word.canonicalEnd u
    prefixExponent := B.zeroPrefixExponent
    suffixExponent := B.zeroSuffixExponent
    backwardExponent := B.zeroBackwardExponent
    halfGap := Z.zeroHalfGap
    seven_le_length := B.seven_le_innerLength
    n_pos := B.coordinates.n_pos
    six_mul_n_lt_length := ?_
    halfGap_zero := Z.zeroHalfGap_zero
    halfGap_pos := ?_
    endpoint_balance := ?_
    suffixExponent_zero := ?_
    backwardExponent_pos := ?_
    suffixExponent_succ := ?_
    exponent_split := ?_
    prefix_expanding := ?_
    suffix_contracting := ?_
    whole_contracting := B.zeroWhole_contracting
    first_backward_exponent_eq_one := ?_
    step_recurrence := ?_
  }
  · have hs := B.sigma_pos
    dsimp [E2BranchData.sigma] at hs
    omega
  · intro r hrPos hrLe
    exact Z.zeroHalfGap_pos hrPos hrLe
  · have h := Z.endpoint_add_five_eq
    have hfull := Z.zeroHalfGap_full_eq_endpointHalfGap
    rw [← hfull] at h
    exact h
  · dsimp [E2BranchData.zeroSuffixExponent, E2BranchData.zeroSuffixWord]
    simp
  · intro r hr
    exact (B.zeroBackwardExponent_spec hr).1
  · intro r hr
    exact B.zeroSuffixExponent_succ hr
  · intro k hk
    exact B.zeroExponent_split hk
  · intro k hk
    exact B.zeroPrefix_expanding hk
  · intro r hrPos hrLe
    exact B.zeroSuffix_threePow_lt_twoPow hrPos hrLe
  · have hm : 0 < u.length := by
      have h7 := B.seven_le_innerLength
      omega
    have hr : u.length - 1 < u.length := by
      omega
    have hspec := (B.zeroBackwardExponent_spec hr).2
    have hfirst := B.firstBackwardWord
    rw [hfirst] at hspec
    simp at hspec
    simpa using hspec.symm
  · intro r hr
    have hword := (B.zeroBackwardExponent_spec hr).2
    exact Z.zeroBackwardGapRecurrence hr hword

end E2ZeroSurvivorData

/-- pure centered trajectory の不存在。これが E2 ZERO の最終整数問題。 -/
def NoE2ZeroCenteredTrajectory : Prop :=
  ∀ _D : E2ZeroCenteredTrajectoryData, False

/-- centered trajectory を排除できれば E2 ZERO survivor は存在しない。 -/
theorem noE2ZeroSurvivor_of_noE2ZeroCenteredTrajectory
    (hNo : NoE2ZeroCenteredTrajectory) :
    NoE2ZeroSurvivor := by
  intro v boundary n d u B Z
  exact hNo Z.toCenteredTrajectory

/-- centered trajectory 排除から inner quotient-zero branch を直接排除する。 -/
theorem no_innerReplay_zero_of_noE2ZeroCenteredTrajectory
    (hNo : NoE2ZeroCenteredTrajectory)
    {v : Collatz.Word} {boundary n d : ℕ} {u : Collatz.Word}
    (B : E2BranchData v boundary n d u)
    (I : E2BranchData.InnerReplayData B)
    (hq : I.coordinate.quotient = 0) :
    False := by
  exact
    no_innerReplay_zero_of_noE2ZeroSurvivor
      (noE2ZeroSurvivor_of_noE2ZeroCenteredTrajectory hNo)
      B I hq

end EndpointFloorZero
end PositiveReturn
end AdjacentReturn
end Collatz
