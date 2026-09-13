import CollatzLean.Collatz3.Critical.WordProfileEquiv

/-!
# Collatz3 Bridge: full critical Young 座標

95 / 175 の比較から得た full critical Young 座標を、既存の
`CriticalWord <-> AdmissibleProfile` の exact equivalence を壊さずに導入する。

設計原則は thin definitions + derived theorems とする。
新しい巨大 structure は作らず、有限 first-passage shape の既存の完全符号
`Critical.AdmissibleProfile m` を `FullCriticalYoung m` の正本として再利用する。

Young 側の実座標は proper prefix height から最低傾き `1` を引いた

`a_k = profileHeight(k) - k`

である。admissible path は各 step で height が strict に増えるので、
`a_k` は左から右へ非減少になる。通常の Young 行方向はこれを逆順に読む。

重要なのは、この座標が record cut を取る前の full profile を保持する点である。
従って `canonicalRecordLengths` と異なり、95 / 175 型の内部差を潰さない。
-/

namespace Collatz3
namespace Bridge

/--
幅 `m` の full critical Young object。

primitive data を増やさず、既存の admissible finite profile をそのまま正本とする。
`CriticalWord` との lossless equivalence は既存 theorem を再利用する。
-/
abbrev FullCriticalYoung (m : ℕ) := Critical.AdmissibleProfile m

namespace FullCriticalYoung

/--
full critical Young の forward excess 座標。

`k` 番目の critical prefix height から最低傾き `1` の高さ `k` を引く。
95 / 175 の議論で用いた `a_k = D_k - k` の profile 版である。
-/
def excessAt
    {m : ℕ}
    (Y : FullCriticalYoung m)
    (k : ℕ) : ℕ :=
  Critical.profileHeight Y.1 k - k

/--
admissible path では Young excess は一段進んでも減少しない。
これは exponent がすべて正であることの Young 座標版。
-/
theorem excessAt_le_succ
    {m : ℕ}
    (Y : FullCriticalYoung m)
    {k : ℕ}
    (hk : k < m) :
    excessAt Y k ≤ excessAt Y (k + 1) := by
  have hStep := Critical.profileHeight_lt_succ Y.2 hk
  unfold excessAt
  omega

/--
admissible height path は最低でも対角線 `height = k` の上にある。
各 step が strict に増加することだけから従う。
-/
theorem index_le_profileHeight
    {m : ℕ}
    (Y : FullCriticalYoung m) :
    ∀ k : ℕ, k ≤ m → k ≤ Critical.profileHeight Y.1 k := by
  intro k
  induction k with
  | zero =>
      intro _hk
      exact Nat.zero_le _
  | succ k ih =>
      intro hk
      have hklt : k < m := by omega
      have hPrev : k ≤ Critical.profileHeight Y.1 k :=
        ih (by omega)
      have hStep := Critical.profileHeight_lt_succ Y.2 hklt
      omega

/--
terminal までの height は `index + Young excess` で exact に復元できる。
Nat subtraction による情報損失が無いことを明示する補題。
-/
theorem profileHeight_eq_index_add_excessAt
    {m : ℕ}
    (Y : FullCriticalYoung m)
    {k : ℕ}
    (hk : k ≤ m) :
    Critical.profileHeight Y.1 k = k + excessAt Y k := by
  have hLe := index_le_profileHeight Y k hk
  unfold excessAt
  omega

/--
finite full Young 座標。
`Fin m` の各 proper critical column に `a_k` を保存する。
-/
def excess
    {m : ℕ}
    (Y : FullCriticalYoung m) : Fin m → ℕ :=
  fun k => excessAt Y k.1

/--
full Young excess は admissible profile の完全符号である。
同じ `a_k` を持つ二つの admissible profile は一致する。

したがって record partition のような情報損失はこの段階では起きない。
-/
theorem excess_injective
    {m : ℕ} :
    Function.Injective (excess (m := m)) := by
  intro Y Z hExcess
  apply Subtype.ext
  funext k
  have hEk : excessAt Y k.1 = excessAt Z k.1 := by
    exact congrFun hExcess k
  have hYHeight :=
    profileHeight_eq_index_add_excessAt Y (Nat.le_of_lt k.2)
  have hZHeight :=
    profileHeight_eq_index_add_excessAt Z (Nat.le_of_lt k.2)
  have hHeight :
      Critical.profileHeight Y.1 k.1 =
        Critical.profileHeight Z.1 k.1 := by
    rw [hYHeight, hZHeight, hEk]
  rw [
    Critical.profileHeight_of_lt Y.1 k.2,
    Critical.profileHeight_of_lt Z.1 k.2
  ] at hHeight
  unfold Critical.checkpoint at hHeight
  have hHeight' :
      Critical.beattyIndex k.1 - Y.1 k =
        Critical.beattyIndex k.1 - Z.1 k := by
    simpa using hHeight
  have hYLe := Y.2.depth_le k
  have hZLe := Z.2.depth_le k
  omega

/--
通常の Young 行方向で読む有限 row code。
proper positive columns `1,...,m-1` の excess を逆順に並べる。

`m=5` では 95 型は `[0,0,0,0]`、175 型は `[1,0,0,0]`
という向きになる。
-/
def rows
    {m : ℕ}
    (Y : FullCriticalYoung m) : List ℕ :=
  ((List.range (m - 1)).map
      (fun j => excessAt Y (j + 1))).reverse

/-- row code の長さは proper positive column 数 `m-1`。 -/
@[simp] theorem rows_length
    {m : ℕ}
    (Y : FullCriticalYoung m) :
    (rows Y).length = m - 1 := by
  simp [rows]

/--
positive width では、critical word shape と full critical Young object は exact に同値。
既存の `CriticalWord <-> AdmissibleProfile` をそのまま公開する薄い wrapper。
-/
def criticalWordEquiv
    (m : ℕ)
    (hm : 0 < m) :
    Critical.CriticalWord m ≃ FullCriticalYoung m :=
  Critical.criticalWordEquivAdmissibleProfile m hm

/--
critical word から作った full Young excess は、元 word の
`prefixTwoDepth(k) - k` そのもの。
これが 95 / 175 の観察との exact bridge。
-/
theorem excess_criticalWordEquiv_eq_prefixTwoDepth_sub
    {m : ℕ}
    (hm : 0 < m)
    (W : Critical.CriticalWord m)
    (k : Fin m) :
    excess (criticalWordEquiv m hm W) k =
      Word.prefixTwoDepth W.1 k.1 - k.1 := by
  change
    Critical.profileHeight (Critical.profileOfWord W.1) k.1 - k.1 =
      Word.prefixTwoDepth W.1 k.1 - k.1
  rw [Critical.profileHeight_profileOfWord W.2 (Nat.le_of_lt k.2)]

end FullCriticalYoung
end Bridge
end Collatz3
