import CollatzLean.Collatz3.Bridge.FullFirstCrossing
import CollatzLean.Collatz3.Bridge.CriticalActualFiber
import CollatzLean.Collatz3.Core.PrefixAffine
set_option linter.style.longLine false
/-!
# Collatz3 Bridge: full first crossing と restricted partition × overshoot

full first-crossing word の proper prefix geometry は従来の critical word と同じで、
terminal だけが minimal critical depth から上へ自由に伸びる。

従って fixed width `m > 0` では

`FullFirstCrossingWord m ≃ RestrictedCriticalPartition m × ℕ`

となる。左成分は lossless Young shape、右成分は terminal overshoot である。

逆構成では proper height を partition から、terminal height を

`criticalTwoDepth m + s`

から作り、既存の `Critical.wordFromHeight` を再利用する。
-/

namespace Collatz3
namespace Bridge

open Word
namespace Word

/-- valid word では prefix depth は index 以上。 -/
theorem index_le_prefixTwoDepth_of_valid
    {w : Word}
    (hValid : Valid w) :
    ∀ k : ℕ, k ≤ oddSteps w → k ≤ prefixTwoDepth w k := by
  intro k
  induction k with
  | zero =>
      intro _hk
      exact Nat.zero_le _
  | succ k ih =>
      intro hk
      have hkLt : k < oddSteps w := by omega
      have hPrev : k ≤ prefixTwoDepth w k :=
        ih (by omega)
      have hStep := prefixTwoDepth_lt_succ_of_valid hValid hkLt
      omega

end Word

namespace Critical.FullFirstCrossingWord

/-- full word の proper prefix excess を restricted partition として読む。 -/
def partition
    {m : ℕ}
    (W : Critical.FullFirstCrossingWord m) :
    RestrictedCriticalPartition m :=
  ⟨fun k => Word.prefixTwoDepth W.1 k.1 - k.1, by
    constructor
    · intro k
      have hIndex :
          k.1 ≤ Word.prefixTwoDepth W.1 k.1 :=
        Word.index_le_prefixTwoDepth_of_valid W.2.valid k.1 (by
          rw [W.2.oddSteps_eq]
          exact Nat.le_of_lt k.2)
      have hRoof :=
        W.2.prefixTwoDepth_le_beatty k.2
      have hCancel :
          k.1 + (Word.prefixTwoDepth W.1 k.1 - k.1) =
            Word.prefixTwoDepth W.1 k.1 := by
        omega
      rw [hCancel]
      exact hRoof
    · intro k hk
      have hk0 : k < m := by
        omega
      have hIndex0 :
          k ≤ Word.prefixTwoDepth W.1 k :=
        Word.index_le_prefixTwoDepth_of_valid W.2.valid k (by
          rw [W.2.oddSteps_eq]
          omega)
      have hIndex1 :
          k + 1 ≤ Word.prefixTwoDepth W.1 (k + 1) :=
        Word.index_le_prefixTwoDepth_of_valid W.2.valid (k + 1) (by
          rw [W.2.oddSteps_eq]
          omega)
      have hStep :=
        Word.prefixTwoDepth_lt_succ_of_valid W.2.valid (by
          rw [W.2.oddSteps_eq]
          exact hk0)
      change
        Word.prefixTwoDepth W.1 k - k ≤
          Word.prefixTwoDepth W.1 (k + 1) - (k + 1)
      omega⟩

end Critical.FullFirstCrossingWord

/--
partition `P` と overshoot `s` が指定する prefix-height path。
proper cut は `k + a_k`、terminal は `criticalTwoDepth m + s`。
-/
def fullFirstCrossingHeight
    {m : ℕ}
    (P : RestrictedCriticalPartition m)
    (s : ℕ)
    (k : ℕ) : ℕ :=
  if hk : k < m then
    k + P.1 ⟨k, hk⟩
  else
    Critical.criticalTwoDepth m + s

@[simp] theorem fullFirstCrossingHeight_of_lt
    {m : ℕ}
    (P : RestrictedCriticalPartition m)
    (s : ℕ)
    {k : ℕ}
    (hk : k < m) :
    fullFirstCrossingHeight P s k = k + P.1 ⟨k, hk⟩ := by
  simp [fullFirstCrossingHeight, hk]

@[simp] theorem fullFirstCrossingHeight_terminal
    {m : ℕ}
    (P : RestrictedCriticalPartition m)
    (s : ℕ) :
    fullFirstCrossingHeight P s m =
      Critical.criticalTwoDepth m + s := by
  simp [fullFirstCrossingHeight]

/-- positive width では full height path は `0` から始まる。 -/
theorem fullFirstCrossingHeight_zero
    {m : ℕ}
    (hm : 0 < m)
    (P : RestrictedCriticalPartition m)
    (s : ℕ) :
    fullFirstCrossingHeight P s 0 = 0 := by
  rw [fullFirstCrossingHeight_of_lt P s hm]
  have h0 := RestrictedCriticalPartition.first_eq_zero P hm
  simpa using h0

/-- full height path は terminal まで strict に増加する。 -/
theorem fullFirstCrossingHeight_lt_succ
    {m : ℕ}
    (P : RestrictedCriticalPartition m)
    (s : ℕ)
    {k : ℕ}
    (hk : k < m) :
    fullFirstCrossingHeight P s k <
      fullFirstCrossingHeight P s (k + 1) := by
  rw [fullFirstCrossingHeight_of_lt P s hk]
  by_cases hNext : k + 1 < m
  · rw [fullFirstCrossingHeight_of_lt P s hNext]
    have hMono := P.2.2 k hNext
    omega
  · have hEq : k + 1 = m := by
      omega
    have hRoof := P.2.1 ⟨k, hk⟩
    have hRoof' :
        k + P.1 ⟨k, hk⟩ ≤ Critical.beattyIndex k := by
      simpa using hRoof
    have hBeattySucc :=
      Critical.beattyIndex_lt_succ k
    have hBeattyM :
        Critical.beattyIndex k < Critical.beattyIndex m := by
      simpa [hEq] using hBeattySucc
    rw [hEq, fullFirstCrossingHeight_terminal]
    unfold Critical.criticalTwoDepth
    omega

/-- partition と overshoot から exponent word を復元する。 -/
def fullWordFromPartitionExtra
    {m : ℕ}
    (P : RestrictedCriticalPartition m)
    (s : ℕ) : Word :=
  Critical.wordFromHeight (fullFirstCrossingHeight P s) m

@[simp] theorem oddSteps_fullWordFromPartitionExtra
    {m : ℕ}
    (P : RestrictedCriticalPartition m)
    (s : ℕ) :
    Word.oddSteps (fullWordFromPartitionExtra P s) = m := by
  exact Critical.oddSteps_wordFromHeight (fullFirstCrossingHeight P s) m

/-- 復元 word は valid。 -/
theorem valid_fullWordFromPartitionExtra
    {m : ℕ}
    (P : RestrictedCriticalPartition m)
    (s : ℕ) :
    Word.Valid (fullWordFromPartitionExtra P s) := by
  exact
    Critical.valid_wordFromHeight
      (fullFirstCrossingHeight P s) m
      (fun k hk => fullFirstCrossingHeight_lt_succ P s hk)

/-- positive width では total depth は `criticalTwoDepth m + s`。 -/
theorem twoSteps_fullWordFromPartitionExtra
    {m : ℕ}
    (hm : 0 < m)
    (P : RestrictedCriticalPartition m)
    (s : ℕ) :
    Word.twoSteps (fullWordFromPartitionExtra P s) =
      Critical.criticalTwoDepth m + s := by
  calc
    Word.twoSteps (fullWordFromPartitionExtra P s)
        = fullFirstCrossingHeight P s m :=
      Critical.twoSteps_wordFromHeight
        (fullFirstCrossingHeight P s) m
        (fullFirstCrossingHeight_zero hm P s)
        (fun k hk => fullFirstCrossingHeight_lt_succ P s hk)
    _ = Critical.criticalTwoDepth m + s :=
      fullFirstCrossingHeight_terminal P s

/-- proper prefix depth は partition 座標 `k + a_k` に exact に戻る。 -/
theorem prefixTwoDepth_fullWordFromPartitionExtra
    {m : ℕ}
    (hm : 0 < m)
    (P : RestrictedCriticalPartition m)
    (s : ℕ)
    {k : ℕ}
    (hk : k ≤ m) :
    Word.prefixTwoDepth (fullWordFromPartitionExtra P s) k =
      fullFirstCrossingHeight P s k := by
  exact
    Critical.prefixTwoDepth_wordFromHeight
      (fullFirstCrossingHeight P s) m
      (fullFirstCrossingHeight_zero hm P s)
      (fun i hi => fullFirstCrossingHeight_lt_succ P s hi)
      hk

/-- partition × overshoot から full first-crossing condition を構成する。 -/
theorem isFullFirstCrossingWord_fullWordFromPartitionExtra
    {m : ℕ}
    (hm : 0 < m)
    (P : RestrictedCriticalPartition m)
    (s : ℕ) :
    Critical.IsFullFirstCrossingWord m
      (fullWordFromPartitionExtra P s) := by
  refine ⟨valid_fullWordFromPartitionExtra P s,
    oddSteps_fullWordFromPartitionExtra P s, ?_⟩
  constructor
  · rw [oddSteps_fullWordFromPartitionExtra]
    rw [twoSteps_fullWordFromPartitionExtra hm]
    exact Nat.le_add_right _ _
  · intro k hk
    have hkM : k < m := by
      simpa [oddSteps_fullWordFromPartitionExtra] using hk
    rw [prefixTwoDepth_fullWordFromPartitionExtra hm P s (Nat.le_of_lt hkM)]
    rw [fullFirstCrossingHeight_of_lt P s hkM]
    exact P.2.1 ⟨k, hkM⟩

/-- partition × overshoot から得る full first-crossing word subtype。 -/
def fullWordOfPartitionExtra
    {m : ℕ}
    (hm : 0 < m)
    (P : RestrictedCriticalPartition m)
    (s : ℕ) :
    Critical.FullFirstCrossingWord m :=
  ⟨fullWordFromPartitionExtra P s,
    isFullFirstCrossingWord_fullWordFromPartitionExtra hm P s⟩

/-- inverse construction の partition は元に戻る。 -/
theorem partition_fullWordOfPartitionExtra
    {m : ℕ}
    (hm : 0 < m)
    (P : RestrictedCriticalPartition m)
    (s : ℕ) :
    Critical.FullFirstCrossingWord.partition
      (fullWordOfPartitionExtra hm P s) = P := by
  apply Subtype.ext
  funext k
  change
    Word.prefixTwoDepth (fullWordFromPartitionExtra P s) k.1 - k.1 =
      P.1 k
  rw [prefixTwoDepth_fullWordFromPartitionExtra hm P s (Nat.le_of_lt k.2)]
  rw [fullFirstCrossingHeight_of_lt P s k.2]
  have hkFin :
      (⟨k.1, k.2⟩ : Fin m) = k := by
    apply Fin.ext
    rfl
  change
    k.1 + P.1 ⟨k.1, k.2⟩ - k.1 =
      P.1 k
  rw [hkFin]
  omega

/-- inverse construction の terminal overshoot は元に戻る。 -/
theorem terminalExtraDepth_fullWordOfPartitionExtra
    {m : ℕ}
    (hm : 0 < m)
    (P : RestrictedCriticalPartition m)
    (s : ℕ) :
    Critical.FullFirstCrossingWord.terminalExtraDepth
      (fullWordOfPartitionExtra hm P s) = s := by
  unfold Critical.FullFirstCrossingWord.terminalExtraDepth
  change
    Word.twoSteps (fullWordFromPartitionExtra P s) -
        Critical.criticalTwoDepth m =
      s
  rw [twoSteps_fullWordFromPartitionExtra hm]
  omega

/--
full first-crossing word から

* restricted partition
* terminal overshoot

を取り出す canonical code。
-/
def fullFirstCrossingPartitionExtraCode
    {m : ℕ}
    (W : Critical.FullFirstCrossingWord m) :
    RestrictedCriticalPartition m × ℕ :=
  (Critical.FullFirstCrossingWord.partition W,
    Critical.FullFirstCrossingWord.terminalExtraDepth W)


/--
restricted partition × terminal overshoot から
full first-crossing word を復元する。
-/
def fullFirstCrossingWordOfPartitionExtraCode
    {m : ℕ}
    (hm : 0 < m)
    (code : RestrictedCriticalPartition m × ℕ) :
    Critical.FullFirstCrossingWord m :=
  fullWordOfPartitionExtra hm code.1 code.2


/--
canonical code から復元した word の odd-step 数は元の幅 `m`。
-/
theorem oddSteps_fullFirstCrossingWordOfPartitionExtraCode
    {m : ℕ}
    (hm : 0 < m)
    (code : RestrictedCriticalPartition m × ℕ) :
    Word.oddSteps
        (fullFirstCrossingWordOfPartitionExtraCode hm code).1 =
      m := by
  rcases code with ⟨P, s⟩
  exact
    (fullWordOfPartitionExtra hm P s).2.oddSteps_eq

/--
`W` の canonical code から復元した word は、
各 proper prefix で元の `W` と同じ two-depth を持つ。
-/
theorem prefixTwoDepth_decode_encode_of_lt
    {m : ℕ}
    (hm : 0 < m)
    (W : Critical.FullFirstCrossingWord m)
    {k : ℕ}
    (hk : k < m) :
    Word.prefixTwoDepth
        (fullFirstCrossingWordOfPartitionExtraCode
          hm (fullFirstCrossingPartitionExtraCode W)).1 k =
      Word.prefixTwoDepth W.1 k := by
  have hkM : k ≤ m :=
    Nat.le_of_lt hk
  change
    Word.prefixTwoDepth
        (fullWordFromPartitionExtra
          (Critical.FullFirstCrossingWord.partition W)
          (Critical.FullFirstCrossingWord.terminalExtraDepth W))
        k =
      Word.prefixTwoDepth W.1 k
  rw [
    prefixTwoDepth_fullWordFromPartitionExtra
      hm
      (Critical.FullFirstCrossingWord.partition W)
      (Critical.FullFirstCrossingWord.terminalExtraDepth W)
      hkM
  ]
  rw [
    fullFirstCrossingHeight_of_lt
      (Critical.FullFirstCrossingWord.partition W)
      (Critical.FullFirstCrossingWord.terminalExtraDepth W)
      hk
  ]
  change
    k + (Word.prefixTwoDepth W.1 k - k) =
      Word.prefixTwoDepth W.1 k
  have hIndex :
      k ≤ Word.prefixTwoDepth W.1 k := by
    apply Word.index_le_prefixTwoDepth_of_valid W.2.valid
    rw [W.2.oddSteps_eq]
    exact hkM
  omega

/--
`W` の canonical code から復元した word は、
terminal prefix でも元の `W` と同じ two-depth を持つ。
-/
theorem prefixTwoDepth_decode_encode_terminal
    {m : ℕ}
    (hm : 0 < m)
    (W : Critical.FullFirstCrossingWord m) :
    Word.prefixTwoDepth
        (fullFirstCrossingWordOfPartitionExtraCode
          hm (fullFirstCrossingPartitionExtraCode W)).1 m =
      Word.prefixTwoDepth W.1 m := by
  let V :=
    fullWordOfPartitionExtra hm
      (Critical.FullFirstCrossingWord.partition W)
      (Critical.FullFirstCrossingWord.terminalExtraDepth W)
  change
    Word.prefixTwoDepth V.1 m =
      Word.prefixTwoDepth W.1 m
  have hVOdd :
      Word.oddSteps V.1 = m :=
    V.2.oddSteps_eq
  have hWOdd :
      Word.oddSteps W.1 = m :=
    W.2.oddSteps_eq
  have hVIndex :
      Word.prefixTwoDepth V.1 m =
        Word.prefixTwoDepth V.1 (Word.oddSteps V.1) := by
    exact congrArg
      (fun j : ℕ => Word.prefixTwoDepth V.1 j)
      hVOdd.symm
  have hWIndex :
      Word.prefixTwoDepth W.1 m =
        Word.prefixTwoDepth W.1 (Word.oddSteps W.1) := by
    exact congrArg
      (fun j : ℕ => Word.prefixTwoDepth W.1 j)
      hWOdd.symm
  have hVTerminal :
      Word.prefixTwoDepth V.1 m =
        Word.twoSteps V.1 := by
    exact hVIndex.trans
      (Word.prefixTwoDepth_oddSteps V.1)
  have hWTerminal :
      Word.prefixTwoDepth W.1 m =
        Word.twoSteps W.1 := by
    exact hWIndex.trans
      (Word.prefixTwoDepth_oddSteps W.1)
  have hVTwo :
      Word.twoSteps V.1 =
        Critical.criticalTwoDepth m +
          Critical.FullFirstCrossingWord.terminalExtraDepth W := by
    dsimp [V]
    exact twoSteps_fullWordFromPartitionExtra hm _ _
  calc
    Word.prefixTwoDepth V.1 m
        = Word.twoSteps V.1 :=
          hVTerminal
    _ = Critical.criticalTwoDepth m +
          Critical.FullFirstCrossingWord.terminalExtraDepth W :=
          hVTwo
    _ = Word.twoSteps W.1 :=
          (Critical.FullFirstCrossingWord.twoSteps_eq_criticalTwoDepth_add_terminalExtraDepth W).symm
    _ = Word.prefixTwoDepth W.1 m :=
          hWTerminal.symm


/--
canonical code から復元した full first-crossing word は元の word に戻る。
-/
theorem fullFirstCrossingWordOfPartitionExtraCode_code
    {m : ℕ}
    (hm : 0 < m)
    (W : Critical.FullFirstCrossingWord m) :
    fullFirstCrossingWordOfPartitionExtraCode
        hm (fullFirstCrossingPartitionExtraCode W) =
      W := by
  apply Subtype.ext
  apply Word.eq_of_oddSteps_eq_of_prefixTwoDepth_eq
  · change
      Word.oddSteps
          (fullWordFromPartitionExtra
            (Critical.FullFirstCrossingWord.partition W)
            (Critical.FullFirstCrossingWord.terminalExtraDepth W)) =
        Word.oddSteps W.1
    rw [
      oddSteps_fullWordFromPartitionExtra,
      W.2.oddSteps_eq
    ]
  · intro k hk
    have hkM : k ≤ m := by
      change
        k ≤ Word.oddSteps
          (fullWordFromPartitionExtra
            (Critical.FullFirstCrossingWord.partition W)
            (Critical.FullFirstCrossingWord.terminalExtraDepth W))
        at hk
      rw [oddSteps_fullWordFromPartitionExtra] at hk
      exact hk
    by_cases hProper : k < m
    · exact
        prefixTwoDepth_decode_encode_of_lt
          hm W hProper
    · have hkEq : k = m := by
        omega
      subst k
      exact
        prefixTwoDepth_decode_encode_terminal hm W


/--
partition × terminal overshoot から復元して再符号化すると、
元の pair に戻る。
-/
theorem fullFirstCrossingPartitionExtraCode_wordOfCode
    {m : ℕ}
    (hm : 0 < m)
    (code : RestrictedCriticalPartition m × ℕ) :
    fullFirstCrossingPartitionExtraCode
        (fullFirstCrossingWordOfPartitionExtraCode hm code) =
      code := by
  rcases code with ⟨P, s⟩
  apply Prod.ext
  · exact
      partition_fullWordOfPartitionExtra hm P s
  · exact
      terminalExtraDepth_fullWordOfPartitionExtra hm P s


/--
full first-crossing word と

`restricted partition × terminal overshoot`

の exact equivalence。
-/
def fullFirstCrossingWordEquivPartitionExtra
    (m : ℕ)
    (hm : 0 < m) :
    Critical.FullFirstCrossingWord m ≃
      (RestrictedCriticalPartition m × ℕ) where
  toFun :=
    fullFirstCrossingPartitionExtraCode

  invFun :=
    fullFirstCrossingWordOfPartitionExtraCode hm

  left_inv :=
    fullFirstCrossingWordOfPartitionExtraCode_code hm

  right_inv :=
    fullFirstCrossingPartitionExtraCode_wordOfCode hm

/-- overshoot `0` の full word は従来の critical word を与える。 -/
def criticalWordFromPartitionExtraZero
    {m : ℕ}
    (hm : 0 < m)
    (P : RestrictedCriticalPartition m) :
    Critical.CriticalWord m := by
  let W := fullWordOfPartitionExtra hm P 0
  refine ⟨W.1, W.2.valid, W.2.oddSteps_eq, ?_, ?_⟩
  · change
      Word.twoSteps (fullWordFromPartitionExtra P 0) =
        Critical.criticalTwoDepth m
    have h :=
      twoSteps_fullWordFromPartitionExtra hm P 0
    simpa using h
  · intro k hk
    exact W.2.prefixTwoDepth_le_beatty hk

/--
同じ値を持つ `Fin m` 上では restricted partition の座標値も一致する。
-/
theorem restrictedCriticalPartition_apply_mk_val
    {m : ℕ}
    (P : RestrictedCriticalPartition m)
    (k : Fin m)
    (h : k.1 < m) :
    P.1 ⟨k.1, h⟩ = P.1 k := by
  congr 1

/-- overshoot `0` の逆構成は既存 `criticalWordOfPartition` と一致する。 -/
theorem criticalWordFromPartitionExtraZero_eq
    {m : ℕ}
    (hm : 0 < m)
    (P : RestrictedCriticalPartition m) :
    criticalWordFromPartitionExtraZero hm P =
      criticalWordOfPartition m hm P := by
  apply (criticalWordEquivRestrictedCriticalPartition m hm).injective
  rw [partition_criticalWordOfPartition hm P]
  apply Subtype.ext
  funext k
  rw [
    restrictedCriticalPartition_criticalWord_coordinate
      hm (criticalWordFromPartitionExtraZero hm P) k
  ]
  change
    Word.prefixTwoDepth (fullWordFromPartitionExtra P 0) k.1 - k.1 =
      P.1 k
  rw [
    prefixTwoDepth_fullWordFromPartitionExtra
      hm P 0 (Nat.le_of_lt k.2)
  ]
  rw [fullFirstCrossingHeight_of_lt P 0 k.2]
  have hCoord :
      P.1 ⟨k.1, k.2⟩ = P.1 k :=
    restrictedCriticalPartition_apply_mk_val P k k.2
  rw [hCoord]
  exact Nat.add_sub_cancel_left k.1 (P.1 k)

/-- terminal overshoot は affine translation `B` を変えない。 -/
theorem affineConst_fullWordFromPartitionExtra_eq_zero
    {m : ℕ}
    (hm : 0 < m)
    (P : RestrictedCriticalPartition m)
    (s : ℕ) :
    Word.affineConst (fullWordFromPartitionExtra P s) =
      Word.affineConst (fullWordFromPartitionExtra P 0) := by
  rw [← Word.affinePrefixNumerator_eq_affineConst,
      ← Word.affinePrefixNumerator_eq_affineConst]
  unfold Word.affinePrefixNumerator
  rw [oddSteps_fullWordFromPartitionExtra,
      oddSteps_fullWordFromPartitionExtra]
  apply Finset.sum_congr rfl
  intro k hk
  have hkM : k < m := Finset.mem_range.mp hk
  unfold Word.affinePrefixTerm
  rw [oddSteps_fullWordFromPartitionExtra,
      oddSteps_fullWordFromPartitionExtra]
  rw [prefixTwoDepth_fullWordFromPartitionExtra hm P s (Nat.le_of_lt hkM)]
  rw [prefixTwoDepth_fullWordFromPartitionExtra hm P 0 (Nat.le_of_lt hkM)]
  rw [fullFirstCrossingHeight_of_lt P s hkM]
  rw [fullFirstCrossingHeight_of_lt P 0 hkM]

/-- full word の affine translation は同じ partition の base critical word と一致。 -/
theorem affineConst_fullWordOfPartitionExtra_eq_critical
    {m : ℕ}
    (hm : 0 < m)
    (P : RestrictedCriticalPartition m)
    (s : ℕ) :
    Word.affineConst (fullWordOfPartitionExtra hm P s).1 =
      Word.affineConst (criticalWordOfPartition m hm P).1 := by
  change
    Word.affineConst (fullWordFromPartitionExtra P s) =
      Word.affineConst (criticalWordOfPartition m hm P).1
  rw [affineConst_fullWordFromPartitionExtra_eq_zero hm P s]
  have hW := criticalWordFromPartitionExtraZero_eq hm P
  exact congrArg (fun W : Critical.CriticalWord m => Word.affineConst W.1) hW

end Bridge
end Collatz3
