import CollatzLean.Collatz3.Mersenne.SmallHoleExitDepth
import CollatzLean.Collatz3.Mersenne.TailLoopModular
import Mathlib.Tactic.NormNum

set_option linter.style.nativeDecide false

/-!
# Collatz3 Mersenne: one-hole finite tail/loop sieve

`SmallHoleExitDepth` で low-bit の non-resonant branch を整理した後、
Dimitrov--Howe 型の tail/loop lifting を一段進める。

ここでは

`M₂ = 2^7 * 5 * 17 * 257 = 2796160`

を使う。この modulus 上では

* `2` は tail 7、その後 period 16、
* `3` は tail 0、period 256、

となる。

したがって任意 exponent は

* `2` 側では `0 .. 22`,
* `3` 側では `0 .. 255`

の有限代表へ落ちる。

## finite sieve の実装方針

素朴な

`K × N × R × L`

の四重全探索では、source-one だけでも

`256 * 23^3 = 3,114,752`

個の modular equation を毎回評価することになる。

ここでは meet-in-the-middle 型に分離する。

* source-one `a=2`
  * `(R,L)` から生じる右辺 residue を 23^2 個だけ先に table 化
  * `(K,N)` は 256*23 個だけ走査
  * 各候補では右辺 table への membership だけを見る

* target-one `n=1`
  * `(R,L,B)` から生じる右辺 residue を 23^3 個だけ先に table 化
  * `K` は 256 個だけ走査
  * 各候補では右辺 table への membership だけを見る

さらに table には `ZMod` 本体ではなく `.val : Nat` を保存し、
inner membership を自然数比較だけにする。

外向きの theorem API は従来の四変数版のまま維持する。
そのため後段の exact equation → tail/loop reduction の証明は変更しない。
-/

namespace Collatz3
namespace Mersenne

/-! ## M₂ の tail/loop certificate -/

/-- `mod 2796160 = 2^7 * 5 * 17 * 257` では 2冪は tail 7、period 16。 -/
theorem powTailLoop_two_mod2796160 :
    PowTailLoop 2796160 2 7 16 := by
  refine ⟨by norm_num, ?_⟩
  decide

/-- `mod 2796160` では 3 は unit で period 256。 -/
theorem powTailLoop_three_mod2796160 :
    PowTailLoop 2796160 3 0 256 := by
  refine ⟨by norm_num, ?_⟩
  native_decide

/-- `mod 2796160` の combined certificate。 -/
theorem pow23TailLoops_mod2796160 :
    Pow23TailLoops 2796160 7 16 0 256 :=
  ⟨powTailLoop_two_mod2796160, powTailLoop_three_mod2796160⟩


/-! ## source one-hole `a=2` -/

/--
`M₂` 上で source hole `a=2` が許す 3-exponent residue。

parity 条件をまだ使わない over-approximation として
`0,1,5,85,125,127,149,253,254,255` の10 class だけが残る。
-/
def SourceOneHoleKResidue256 (K : ℕ) : Prop :=
  K = 0 ∨ K = 1 ∨ K = 5 ∨ K = 85 ∨ K = 125 ∨
  K = 127 ∨ K = 149 ∨ K = 253 ∨ K = 254 ∨ K = 255

/--
source-one `a=2` の左辺 residue。

finite sieve では最後に `.val` を取り、自然数 table と比較する。
-/
private def sourceOneHoleHoleTwoLhs
    (K N : ℕ) : ZMod 2796160 :=
  (3 : ZMod 2796160) ^ K *
    ((2 : ZMod 2796160) ^ N - 1 - (2 : ZMod 2796160) ^ 2)

/-- source-one の右辺 residue。 -/
private def sourceOneHoleRhs
    (R L : ℕ) : ZMod 2796160 :=
  (2 : ZMod 2796160) ^ R *
      ((2 : ZMod 2796160) ^ L - 1) + 1

/--
source-one の `(R,L)` 側で到達可能な residue 値。

`23^2 = 529` 個だけを一度列挙する。
`ZMod` ではなく `.val : Nat` を保存して inner lookup を軽くする。
-/
private def sourceOneHoleRhsTable : List ℕ :=
  (List.range 23).flatMap fun R =>
    (List.range 23).map fun L =>
      (sourceOneHoleRhs R L).val

/-- 任意の finite `(R,L)` が source-one 右辺 table に入る。 -/
private theorem sourceOneHoleRhs_mem
    (R L : Fin 23) :
    (sourceOneHoleRhs R.1 L.1).val ∈ sourceOneHoleRhsTable := by
  simp only [sourceOneHoleRhsTable, List.mem_flatMap, List.mem_map]
  exact ⟨R.1, List.mem_range.mpr R.2,
    L.1, List.mem_range.mpr L.2, rfl⟩

/--
meet-in-the-middle の計算核。

従来の `256 * 23^3` 個の full modular equation ではなく、

* `(K,N)` は `256 * 23 = 5888` 個
* 右辺候補は固定 table `23^2 = 529` 個

として分離する。

冪計算を四重ループの最内側で繰り返さないのが主目的。
-/
private theorem sourceOneHole_holeTwo_finite_sieve_mitm :
    ∀ K : Fin 256,
      ∀ N : Fin 23,
        (sourceOneHoleHoleTwoLhs K.1 N.1).val ∈
            sourceOneHoleRhsTable →
          SourceOneHoleKResidue256 K.1 := by
  unfold SourceOneHoleKResidue256
  native_decide

/--
従来 API を保つ wrapper。

実際の modular equation が成立すれば、その左辺 `.val` は
右辺 table の要素なので、meet-in-the-middle certificate に渡せる。
-/
private theorem sourceOneHole_holeTwo_finite_sieve :
    ∀ K : Fin 256,
      ∀ N R L : Fin 23,
        SourceOneHoleModEquation
            2796160 K.1 N.1 R.1 L.1 2 →
          SourceOneHoleKResidue256 K.1 := by
  intro K N R L hEq
  apply sourceOneHole_holeTwo_finite_sieve_mitm K N
  have hEqZ :
      sourceOneHoleHoleTwoLhs K.1 N.1 =
        sourceOneHoleRhs R.1 L.1 := by
    simpa [sourceOneHoleHoleTwoLhs, sourceOneHoleRhs,
      SourceOneHoleModEquation] using hEq
  have hEqVal :
      (sourceOneHoleHoleTwoLhs K.1 N.1).val =
        (sourceOneHoleRhs R.1 L.1).val :=
    congrArg ZMod.val hEqZ
  rw [hEqVal]
  exact sourceOneHoleRhs_mem R L

/--
任意の整数 source-one equation `a=2` は、`k mod 256` が上の10 class の
どれかに入る。

`a=2` は tail 7 の内部なので、hole position 自体は finite reduction で exact に保持される。
-/
theorem SourceOneHoleEquation.k_mod_256_of_hole_two
    {k n r L : ℕ}
    (hEq : SourceOneHoleEquation k n r L 2) :
    SourceOneHoleKResidue256 (k % 256) := by
  have hMod := hEq.to_mod 2796160
  have hRed :=
    hMod.reduce_tailLoop pow23TailLoops_mod2796160
  let N : ℕ := tailLoopExponent 7 16 n
  let R : ℕ := tailLoopExponent 7 16 r
  let T : ℕ := tailLoopExponent 7 16 L
  have hNlt : N < 23 := by
    dsimp [N]
    have h := powTailLoop_two_mod2796160.tailLoopExponent_lt (e := n)
    norm_num at h ⊢
    exact h
  have hRlt : R < 23 := by
    dsimp [R]
    have h := powTailLoop_two_mod2796160.tailLoopExponent_lt (e := r)
    norm_num at h ⊢
    exact h
  have hTlt : T < 23 := by
    dsimp [T]
    have h := powTailLoop_two_mod2796160.tailLoopExponent_lt (e := L)
    norm_num at h ⊢
    exact h
  have hKlt : k % 256 < 256 :=
    Nat.mod_lt _ (by norm_num)
  let Kf : Fin 256 := ⟨k % 256, hKlt⟩
  let Nf : Fin 23 := ⟨N, hNlt⟩
  let Rf : Fin 23 := ⟨R, hRlt⟩
  let Tf : Fin 23 := ⟨T, hTlt⟩
  have hEqFinite :
      SourceOneHoleModEquation
        2796160 Kf.1 Nf.1 Rf.1 Tf.1 2 := by
    dsimp [Kf, Nf, Rf, Tf, N, R, T]
    simpa [tailLoopExponent] using hRed
  exact
    sourceOneHole_holeTwo_finite_sieve
      Kf Nf Rf Tf hEqFinite


/-! ## target one-hole low-source -/

/--
`n=1` の target-one equation が `M₂` 上で許す `k mod 256`。

残るのは `0,1,2,3,4,48,128,208` の8 class。
-/
def TargetOneHoleSourceOneKResidue256 (K : ℕ) : Prop :=
  K = 0 ∨ K = 1 ∨ K = 2 ∨ K = 3 ∨
  K = 4 ∨ K = 48 ∨ K = 128 ∨ K = 208

/-- target-one `n=1` の左辺 residue。 -/
private def targetOneHoleSourceOneLhs
    (K : ℕ) : ZMod 2796160 :=
  (3 : ZMod 2796160) ^ K *
    ((2 : ZMod 2796160) ^ 1 - 1)

/-- target-one `n=1` の右辺 residue。 -/
private def targetOneHoleRhs
    (R L B : ℕ) : ZMod 2796160 :=
  (2 : ZMod 2796160) ^ R *
      ((2 : ZMod 2796160) ^ L - 1 -
        (2 : ZMod 2796160) ^ B) + 1

/--
target-one の `(R,L,B)` 側で到達可能な residue 値。

`23^3 = 12167` 個を一度だけ table 化し、
256 個の `K` 候補から lookup する。
-/
private def targetOneHoleRhsTable : List ℕ :=
  (List.range 23).flatMap fun R =>
    (List.range 23).flatMap fun L =>
      (List.range 23).map fun B =>
        (targetOneHoleRhs R L B).val

/-- 任意の finite `(R,L,B)` が target-one 右辺 table に入る。 -/
private theorem targetOneHoleRhs_mem
    (R L B : Fin 23) :
    (targetOneHoleRhs R.1 L.1 B.1).val ∈ targetOneHoleRhsTable := by
  simp only [targetOneHoleRhsTable, List.mem_flatMap, List.mem_map]
  exact ⟨R.1, List.mem_range.mpr R.2,
    L.1, List.mem_range.mpr L.2,
    B.1, List.mem_range.mpr B.2, rfl⟩

/--
target-one `n=1` の meet-in-the-middle 計算核。

外側は `K : Fin 256` だけで、`R,L,B` は右辺 table に畳み込む。
-/
private theorem targetOneHole_sourceOne_finite_sieve_mitm :
    ∀ K : Fin 256,
      (targetOneHoleSourceOneLhs K.1).val ∈
          targetOneHoleRhsTable →
        TargetOneHoleSourceOneKResidue256 K.1 := by
  unfold TargetOneHoleSourceOneKResidue256
  native_decide

/-- 従来 API を保つ target-one wrapper。 -/
private theorem targetOneHole_sourceOne_finite_sieve :
    ∀ K : Fin 256,
      ∀ R L B : Fin 23,
        TargetOneHoleModEquation
            2796160 K.1 1 R.1 L.1 B.1 →
          TargetOneHoleSourceOneKResidue256 K.1 := by
  intro K R L B hEq
  apply targetOneHole_sourceOne_finite_sieve_mitm K
  have hEqZ :
      targetOneHoleSourceOneLhs K.1 =
        targetOneHoleRhs R.1 L.1 B.1 := by
    simpa [targetOneHoleSourceOneLhs, targetOneHoleRhs,
      TargetOneHoleModEquation] using hEq
  have hEqVal :
      (targetOneHoleSourceOneLhs K.1).val =
        (targetOneHoleRhs R.1 L.1 B.1).val :=
    congrArg ZMod.val hEqZ
  rw [hEqVal]
  exact targetOneHoleRhs_mem R L B

/-- `n=1` の target-one equation は `k mod 256` が8 class に限られる。 -/
theorem TargetOneHoleEquation.k_mod_256_of_source_one
    {k r L b : ℕ}
    (hEq : TargetOneHoleEquation k 1 r L b) :
    TargetOneHoleSourceOneKResidue256 (k % 256) := by
  have hMod := hEq.to_mod 2796160
  have hRed :=
    hMod.reduce_tailLoop pow23TailLoops_mod2796160
  let R : ℕ := tailLoopExponent 7 16 r
  let T : ℕ := tailLoopExponent 7 16 L
  let B : ℕ := tailLoopExponent 7 16 b
  have hRlt : R < 23 := by
    dsimp [R]
    have h := powTailLoop_two_mod2796160.tailLoopExponent_lt (e := r)
    norm_num at h ⊢
    exact h
  have hTlt : T < 23 := by
    dsimp [T]
    have h := powTailLoop_two_mod2796160.tailLoopExponent_lt (e := L)
    norm_num at h ⊢
    exact h
  have hBlt : B < 23 := by
    dsimp [B]
    have h := powTailLoop_two_mod2796160.tailLoopExponent_lt (e := b)
    norm_num at h ⊢
    exact h
  have hKlt : k % 256 < 256 :=
    Nat.mod_lt _ (by norm_num)
  let Kf : Fin 256 := ⟨k % 256, hKlt⟩
  let Rf : Fin 23 := ⟨R, hRlt⟩
  let Tf : Fin 23 := ⟨T, hTlt⟩
  let Bf : Fin 23 := ⟨B, hBlt⟩
  have hEqFinite :
      TargetOneHoleModEquation
        2796160 Kf.1 1 Rf.1 Tf.1 Bf.1 := by
    dsimp [Kf, Rf, Tf, Bf, R, T, B]
    simpa [tailLoopExponent] using hRed
  exact
    targetOneHole_sourceOne_finite_sieve
      Kf Rf Tf Bf hEqFinite

/--
`n=2` は既存 bridge で `n=1, depth=k+1` へ移るので、
`(k+1) mod 256` が同じ8 class に入る。
-/
theorem TargetOneHoleEquation.succ_k_mod_256_of_source_two
    {k r L b : ℕ}
    (hEq : TargetOneHoleEquation k 2 r L b) :
    TargetOneHoleSourceOneKResidue256 ((k + 1) % 256) := by
  exact
    hEq.source_two_to_source_one.k_mod_256_of_source_one


/-! ## 最初の residue-stage summary -/

/--
source `a=2` resonance と target low-source の最初の finite sieve が閉じている、
というまとめ用 conjunction。

後段ではこの二つの finite residue predicate だけを次の modulus へ lift すればよい。
-/
theorem oneHole_firstFiniteSieve_ready :
    (∀ {k n r L : ℕ},
      SourceOneHoleEquation k n r L 2 →
      SourceOneHoleKResidue256 (k % 256)) ∧
    (∀ {k r L b : ℕ},
      TargetOneHoleEquation k 1 r L b →
      TargetOneHoleSourceOneKResidue256 (k % 256)) ∧
    (∀ {k r L b : ℕ},
      TargetOneHoleEquation k 2 r L b →
      TargetOneHoleSourceOneKResidue256 ((k + 1) % 256)) := by
  exact ⟨
    fun h => h.k_mod_256_of_hole_two,
    fun h => h.k_mod_256_of_source_one,
    fun h => h.succ_k_mod_256_of_source_two
  ⟩

end Mersenne
end Collatz3
