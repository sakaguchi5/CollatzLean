import CollatzLean.Collatz3.Bridge.FullCriticalYoung

/-!
# Collatz3 Bridge: full critical Young と制限付き整数分割

`FullCriticalYoung` が保持している lossless な excess 座標を、
Beatty 屋根の内部に入る有限の制限付き整数分割として切り出す。

forward 座標は proper cut `k` における

`a_k = D_k - k`

である。これは左から右へ非減少で、各列で

`k + a_k ≤ beattyIndex k`

を満たす。通常の Young/Ferrers の行方向では、この列を逆順に読む。
したがって本ファイルの `RestrictedCriticalPartition m` は、
固定屋根

`c_k = beattyIndex k - k`

の内部に入る partition を forward excess 座標で保存したものになる。

`FullCriticalYoung` とこの restricted partition は情報を失わず exact に同値であり、
positive width では既存の `CriticalWord` との同値を合成して

`CriticalWord m ≃ RestrictedCriticalPartition m`

を得る。
-/

namespace Collatz3
namespace Bridge

/--
幅 `m` の restricted critical partition が満たす純粋組合せ条件。

* 各 proper column は Beatty 屋根以下、
* forward excess は非減少。

`Fin m` の `0` 列も含めるが、屋根が `beattyIndex 0 = 0` なので
その値は自動的に `0` に固定される。従って実質的な自由度は
positive proper columns `1,...,m-1` だけである。
-/
def IsRestrictedCriticalPartition
    {m : ℕ}
    (a : Fin m → ℕ) : Prop :=
  (∀ k : Fin m,
    k.1 + a k ≤ Critical.beattyIndex k.1) ∧
  (∀ k : ℕ, (hk : k + 1 < m) →
    a ⟨k, by omega⟩ ≤ a ⟨k + 1, hk⟩)

/--
幅 `m` の critical first-passage を表す制限付き整数分割。

保存する primitive data は forward excess `a_k` だけであり、
profile / word / actual orbit は埋め込まない。
-/
abbrev RestrictedCriticalPartition (m : ℕ) :=
  {a : Fin m → ℕ // IsRestrictedCriticalPartition a}

namespace RestrictedCriticalPartition

/-- Beatty 屋根から最低傾き `1` を引いた forward roof excess。 -/
def roofExcessAt (k : ℕ) : ℕ :=
  Critical.beattyIndex k - k

/-- roof excess 自身も forward 方向に非減少。 -/
theorem roofExcessAt_le_succ (k : ℕ) :
    roofExcessAt k ≤ roofExcessAt (k + 1) := by
  have hBeatty := Critical.beattyIndex_lt_succ k
  unfold roofExcessAt
  omega

/-- restricted partition は各列で固定 roof excess 以下。 -/
theorem le_roofExcessAt
    {m : ℕ}
    (P : RestrictedCriticalPartition m)
    (k : Fin m) :
    P.1 k ≤ roofExcessAt k.1 := by
  have hRoof := P.2.1 k
  unfold roofExcessAt
  omega

/-- forward excess は adjacent columns で非減少。 -/
theorem forward_le_succ
    {m : ℕ}
    (P : RestrictedCriticalPartition m)
    {k : ℕ}
    (hk : k + 1 < m) :
    P.1 ⟨k, by omega⟩ ≤ P.1 ⟨k + 1, hk⟩ :=
  P.2.2 k hk

/-- positive width では最初の excess は必ず `0`。 -/
theorem first_eq_zero
    {m : ℕ}
    (P : RestrictedCriticalPartition m)
    (hm : 0 < m) :
    P.1 ⟨0, hm⟩ = 0 := by
  have hRoof := P.2.1 ⟨0, hm⟩
  simp only [Critical.beattyIndex_zero, Nat.zero_add,
    nonpos_iff_eq_zero] at hRoof
  exact hRoof

/--
通常の Young 行方向で読む row list。
forward excess を逆順にし、強制された最初の `0` 列を落とす。
-/
def rows
    {m : ℕ}
    (P : RestrictedCriticalPartition m) : List ℕ :=
  (List.ofFn P.1).tail.reverse

/--
restricted partition から finite critical profile を復元する。

proper height は `k + a_k` なので、profile depth は
Beatty roof との差

`beattyIndex k - (k + a_k)`

で一意に決まる。
-/
def profile
    {m : ℕ}
    (P : RestrictedCriticalPartition m) : Critical.Profile m :=
  fun k => Critical.beattyIndex k.1 - (k.1 + P.1 k)

/-- 復元 profile の checkpoint は `k + a_k` に exact に戻る。 -/
theorem checkpoint_profile
    {m : ℕ}
    (P : RestrictedCriticalPartition m)
    (k : Fin m) :
    Critical.checkpoint (profile P) k = k.1 + P.1 k := by
  unfold Critical.checkpoint profile
  have hRoof := P.2.1 k
  omega

/-- restricted partition から復元した profile は admissible。 -/
theorem admissible_profile
    {m : ℕ}
    (P : RestrictedCriticalPartition m) :
    Critical.Admissible (profile P) := by
  constructor
  · intro k
    unfold profile
    exact Nat.sub_le _ _
  · intro k hk
    rw [
      checkpoint_profile P ⟨k, by omega⟩,
      checkpoint_profile P ⟨k + 1, hk⟩
    ]
    have hMono := P.2.2 k hk
    change
      k + P.1 ⟨k, by omega⟩ <
        (k + 1) + P.1 ⟨k + 1, hk⟩
    omega

/-- restricted partition から lossless full critical Young object を復元する。 -/
def toFullCriticalYoung
    {m : ℕ}
    (P : RestrictedCriticalPartition m) : FullCriticalYoung m :=
  ⟨profile P, admissible_profile P⟩

/-- 復元後の Young excess は元の partition 座標に exact に戻る。 -/
theorem excessAt_toFullCriticalYoung
    {m : ℕ}
    (P : RestrictedCriticalPartition m)
    (k : Fin m) :
    FullCriticalYoung.excessAt (toFullCriticalYoung P) k.1 = P.1 k := by
  change
    Critical.profileHeight (profile P) k.1 - k.1 = P.1 k
  rw [Critical.profileHeight_of_lt (profile P) k.2]
  rw [checkpoint_profile P k]
  omega

/-- 復元後の full excess 関数は元 partition そのもの。 -/
theorem excess_toFullCriticalYoung
    {m : ℕ}
    (P : RestrictedCriticalPartition m) :
    FullCriticalYoung.excess (toFullCriticalYoung P) = P.1 := by
  funext k
  exact excessAt_toFullCriticalYoung P k

end RestrictedCriticalPartition

namespace FullCriticalYoung

/--
full critical Young object から restricted partition を読む。
primitive data は既存の lossless excess 関数をそのまま使う。
-/
def toRestrictedCriticalPartition
    {m : ℕ}
    (Y : FullCriticalYoung m) : RestrictedCriticalPartition m :=
  ⟨excess Y, by
    constructor
    · intro k
      have hHeight :=
        profileHeight_eq_index_add_excessAt Y (Nat.le_of_lt k.2)
      have hRoof :
          Critical.profileHeight Y.1 k.1 ≤ Critical.beattyIndex k.1 := by
        rw [Critical.profileHeight_of_lt Y.1 k.2]
        unfold Critical.checkpoint
        exact Nat.sub_le _ _
      change k.1 + excessAt Y k.1 ≤ Critical.beattyIndex k.1
      rw [← hHeight]
      exact hRoof
    · intro k hk
      change excessAt Y k ≤ excessAt Y (k + 1)
      exact excessAt_le_succ Y (by omega)⟩

/-- restricted partition にしてから full Young に戻すと元に戻る。 -/
theorem toFullCriticalYoung_toRestrictedCriticalPartition
    {m : ℕ}
    (Y : FullCriticalYoung m) :
    RestrictedCriticalPartition.toFullCriticalYoung
        (toRestrictedCriticalPartition Y) = Y := by
  apply excess_injective
  have h :=
    RestrictedCriticalPartition.excess_toFullCriticalYoung
      (toRestrictedCriticalPartition Y)
  simpa [toRestrictedCriticalPartition] using h

end FullCriticalYoung

namespace RestrictedCriticalPartition

/-- full Young に戻してから restricted partition を読むと元に戻る。 -/
theorem toRestrictedCriticalPartition_toFullCriticalYoung
    {m : ℕ}
    (P : RestrictedCriticalPartition m) :
    FullCriticalYoung.toRestrictedCriticalPartition
        (toFullCriticalYoung P) = P := by
  apply Subtype.ext
  exact excess_toFullCriticalYoung P

end RestrictedCriticalPartition

/--
full critical Young object と restricted critical partition の exact equivalence。
`m = 0` でも両側は空座標一つなので成立する。
-/
def fullCriticalYoungEquivRestrictedCriticalPartition
    (m : ℕ) :
    FullCriticalYoung m ≃ RestrictedCriticalPartition m where
  toFun := FullCriticalYoung.toRestrictedCriticalPartition
  invFun := RestrictedCriticalPartition.toFullCriticalYoung
  left_inv := FullCriticalYoung.toFullCriticalYoung_toRestrictedCriticalPartition
  right_inv :=
    RestrictedCriticalPartition.toRestrictedCriticalPartition_toFullCriticalYoung

/--
positive width では critical word と restricted critical partition は exact に同値。

これが

`CriticalWord m ≃ RestrictedCriticalPartition m`

という有限組合せ論の完全符号化。
-/
def criticalWordEquivRestrictedCriticalPartition
    (m : ℕ)
    (hm : 0 < m) :
    Critical.CriticalWord m ≃ RestrictedCriticalPartition m :=
  (FullCriticalYoung.criticalWordEquiv m hm).trans
    (fullCriticalYoungEquivRestrictedCriticalPartition m)

/--
critical word から得る restricted partition の forward 座標は、
元 word の `prefixTwoDepth(k) - k` そのもの。
-/
theorem restrictedCriticalPartition_criticalWord_coordinate
    {m : ℕ}
    (hm : 0 < m)
    (W : Critical.CriticalWord m)
    (k : Fin m) :
    (criticalWordEquivRestrictedCriticalPartition m hm W).1 k =
      Word.prefixTwoDepth W.1 k.1 - k.1 := by
  change
    FullCriticalYoung.excess
        (FullCriticalYoung.criticalWordEquiv m hm W) k =
      Word.prefixTwoDepth W.1 k.1 - k.1
  exact
    FullCriticalYoung.excess_criticalWordEquiv_eq_prefixTwoDepth_sub
      hm W k

end Bridge
end Collatz3
