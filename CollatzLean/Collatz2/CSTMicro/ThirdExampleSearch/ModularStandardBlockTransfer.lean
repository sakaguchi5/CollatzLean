import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.StandardBlockTransfer
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleConvergent22Checkpoint

/-!
# 第3例探索: modular standard-block transfer

通常の `StandardBlockTransfer` は

  x ↦ a*x + b

を `ℤ` 上で保持する。
巨大 window では `a = 3^L` や affine numerator 自体が数十億 bit になり得るため、
それらを通常整数として実体化してはいけない。

このファイルでは fixed modulus `M` に対して

  x ↦ a*x + b   (mod M)

だけを `ZMod M` で保持する。

重要なのは、continued-fraction / Christoffel recurrence を使うとき、
巨大 block length 回の反復ではなく、小さい partial quotient 回の transfer 合成だけで
次の standard block を作れることである。

このファイル自身は巨大 `criticalIntervalPhiZ` を評価しない。
後段では base-scale transfer を一度 modular に与え、`comp` / `repeat` だけで
scale 21 まで持ち上げる。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

/-- modulus `M` 上の affine standard-block summary。 -/
@[ext]
structure ModularStandardBlockTransfer (M : ℕ) where
  mul : ZMod M
  add : ZMod M

namespace ModularStandardBlockTransfer

/-- modular transfer の作用。 -/
def apply
    {M : ℕ}
    (T : ModularStandardBlockTransfer M)
    (x : ZMod M) : ZMod M :=
  T.mul * x + T.add

/-- `before` の後に `after` を適用する chronological composition。 -/
def comp
    {M : ℕ}
    (after before : ModularStandardBlockTransfer M) :
    ModularStandardBlockTransfer M :=
  {
    mul := after.mul * before.mul
    add := after.mul * before.add + after.add
  }

/-- 空 block の恒等 transfer。 -/
def id (M : ℕ) : ModularStandardBlockTransfer M :=
  { mul := 1, add := 0 }

/-- modular summary の合成は関数合成そのもの。 -/
theorem comp_apply
    {M : ℕ}
    (after before : ModularStandardBlockTransfer M)
    (x : ZMod M) :
    (after.comp before).apply x =
      after.apply (before.apply x) := by
  simp [comp, apply]
  ring

/-- 左恒等元。 -/
theorem id_comp
    {M : ℕ}
    (T : ModularStandardBlockTransfer M) :
    (id M).comp T = T := by
  apply ModularStandardBlockTransfer.ext <;>
    simp [id, comp]

/-- 右恒等元。 -/
theorem comp_id
    {M : ℕ}
    (T : ModularStandardBlockTransfer M) :
    T.comp (id M) = T := by
  apply ModularStandardBlockTransfer.ext <;>
    simp [id, comp]

/-- 合成は結合的。DAG の括り方に依存しない。 -/
theorem comp_assoc
    {M : ℕ}
    (A B C : ModularStandardBlockTransfer M) :
    A.comp (B.comp C) = (A.comp B).comp C := by
  apply ModularStandardBlockTransfer.ext <;>
    simp [comp] <;> ring

/--
同一 standard block transfer を `n` 回 chronological に合成する。

`n` は巨大 block length ではなく continued-fraction の partial quotient 用で、
今回の relevant range では小さい値だけを使う。
-/
def compIterate
    {M : ℕ}
    (T : ModularStandardBlockTransfer M) :
    ℕ → ModularStandardBlockTransfer M
  | 0 => id M
  | n + 1 => T.comp (compIterate T n)

@[simp] theorem compIterate_zero
    {M : ℕ}
    (T : ModularStandardBlockTransfer M) :
    compIterate T 0 = id M := rfl

@[simp] theorem compIterate_succ
    {M : ℕ}
    (T : ModularStandardBlockTransfer M)
    (n : ℕ) :
    compIterate T (n + 1) =
      T.comp (compIterate T n) := rfl

/-- `compIterate` の一段作用。 -/
theorem compIterate_succ_apply
    {M : ℕ}
    (T : ModularStandardBlockTransfer M)
    (n : ℕ)
    (x : ZMod M) :
    (compIterate T (n + 1)).apply x =
      T.apply ((compIterate T n).apply x) := by
  rw [compIterate_succ, comp_apply]

def appendCurrentCopies
    {M : ℕ}
    (older current : ModularStandardBlockTransfer M)
    (a : ℕ) : ModularStandardBlockTransfer M :=
  (compIterate current a).comp older

theorem appendCurrentCopies_apply
    {M : ℕ}
    (older current : ModularStandardBlockTransfer M)
    (a : ℕ)
    (x : ZMod M) :
    (appendCurrentCopies older current a).apply x =
      (compIterate current a).apply (older.apply x) := by
  rw [appendCurrentCopies, comp_apply]

def prependCurrentCopies
    {M : ℕ}
    (older current : ModularStandardBlockTransfer M)
    (a : ℕ) : ModularStandardBlockTransfer M :=
  older.comp (compIterate current a)

theorem prependCurrentCopies_apply
    {M : ℕ}
    (older current : ModularStandardBlockTransfer M)
    (a : ℕ)
    (x : ZMod M) :
    (prependCurrentCopies older current a).apply x =
      older.apply ((compIterate current a).apply x) := by
  rw [prependCurrentCopies, comp_apply]

/-- transfer list を chronological order で一つへ fold する。 -/
def fold
    {M : ℕ} :
    List (ModularStandardBlockTransfer M) →
      ModularStandardBlockTransfer M
  | [] => id M
  | T :: Ts => (fold Ts).comp T

@[simp] theorem fold_nil
    {M : ℕ} :
    (fold ([] : List (ModularStandardBlockTransfer M))) = id M := rfl

@[simp] theorem fold_cons
    {M : ℕ}
    (T : ModularStandardBlockTransfer M)
    (Ts : List (ModularStandardBlockTransfer M)) :
    fold (T :: Ts) = (fold Ts).comp T := rfl

/-- chronological fold の先頭作用。 -/
theorem fold_cons_apply
    {M : ℕ}
    (T : ModularStandardBlockTransfer M)
    (Ts : List (ModularStandardBlockTransfer M))
    (x : ZMod M) :
    (fold (T :: Ts)).apply x =
      (fold Ts).apply (T.apply x) := by
  rw [fold_cons, comp_apply]

/--
既存 `ℤ` transfer を modulus `M` へ写す意味論 bridge。
この関数を hot path で巨大 transfer に適用するのではなく、
後段の correctness theorem で使う。
-/
def ofStandard
    {M : ℕ}
    (T : StandardBlockTransfer) :
    ModularStandardBlockTransfer M :=
  {
    mul := T.mul
    add := T.add
  }

/-- integer affine action を modular 化した結果と exact に一致。 -/
theorem ofStandard_apply
    {M : ℕ}
    (T : StandardBlockTransfer)
    (x : ℤ) :
    (ofStandard (M := M) T).apply (x : ZMod M) =
      ((T.apply x : ℤ) : ZMod M) := by
  simp [ofStandard, apply, StandardBlockTransfer.apply]

/-- integer transfer の composition を先にしても、modular 化してから合成しても同じ。 -/
theorem ofStandard_comp
    {M : ℕ}
    (after before : StandardBlockTransfer) :
    ofStandard (M := M) (after.comp before) =
      (ofStandard (M := M) after).comp
        (ofStandard (M := M) before) := by
  apply ModularStandardBlockTransfer.ext <;>
    simp [
      ofStandard,
      comp,
      StandardBlockTransfer.comp
    ]

end ModularStandardBlockTransfer

/-- 第3例 start 側 `mod 2^68` の transfer 型。 -/
abbrev ThirdExampleLeftModularTransfer :=
  ModularStandardBlockTransfer thirdExampleLeftModulus

/-- 第3例 endpoint 側 `mod 3^42` の transfer 型。 -/
abbrev ThirdExampleRightModularTransfer :=
  ModularStandardBlockTransfer thirdExampleRightModulus

end ThirdExampleSearch
end CSTMicro
end Collatz2
