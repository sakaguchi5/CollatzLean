import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ModularStandardBlockTransfer
import Mathlib.Tactic.Ring

/-!
# 第3例探索: continued-fraction standard block の modular 正規化 packet

巨大 standard block を列ごとに展開せず、局所 block を

  length : odd-column 数
  rise   : local dyadic rise
  phi    : local affine numerator mod M
  gap    : 2^rise - 3^length mod M

の四つだけで保持する。

局所 block `A` の後ろに `B` を連結すると、既存 critical interval の concat law と同じ

  Phi(A B)
    = 3^length(B) Phi(A) + 2^rise(A) Phi(B)

  Gap(A B)
    = 3^length(B) Gap(A) + 2^rise(A) Gap(B)

で更新できる。

従って block length が数十億でも、`ZMod M` 上の modular exponentiation と
continued-fraction の小さい partial quotient 回の合成だけで次 scale を生成できる。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

/--
modulus `M` 上の、原点正規化された standard-word block packet。
`phi` / `gap` は通常整数ではなく最初から `ZMod M` に落として保持する。
-/
@[ext]
structure ModularStandardWordPacket (M : ℕ) where
  length : ℕ
  rise : ℕ
  phi : ZMod M
  gap : ZMod M

namespace ModularStandardWordPacket

/-- 空 word の正規化 packet。 -/
def empty (M : ℕ) : ModularStandardWordPacket M :=
  {
    length := 0
    rise := 0
    phi := 0
    gap := 0
  }

/-- global parameter `y` に対する local affine defect `Phi - Gap*y`。 -/
def defect
    {M : ℕ}
    (B : ModularStandardWordPacket M)
    (y : ZMod M) : ZMod M :=
  B.phi - B.gap * y

/--
chronological concatenation `left ++ right`。

重要: `phi` / `gap` は巨大整数を作らず、常に `ZMod M` のまま更新する。
-/
def concat
    {M : ℕ}
    (left right : ModularStandardWordPacket M) :
    ModularStandardWordPacket M :=
  {
    length := left.length + right.length
    rise := left.rise + right.rise
    phi :=
      (3 : ZMod M) ^ right.length * left.phi +
        (2 : ZMod M) ^ left.rise * right.phi
    gap :=
      (3 : ZMod M) ^ right.length * left.gap +
        (2 : ZMod M) ^ left.rise * right.gap
  }

@[simp] theorem concat_length
    {M : ℕ}
    (left right : ModularStandardWordPacket M) :
    (left.concat right).length = left.length + right.length := rfl

@[simp] theorem concat_rise
    {M : ℕ}
    (left right : ModularStandardWordPacket M) :
    (left.concat right).rise = left.rise + right.rise := rfl

/-- defect 自身も同じ positive-linear concat law を持つ。 -/
theorem concat_defect
    {M : ℕ}
    (left right : ModularStandardWordPacket M)
    (y : ZMod M) :
    (left.concat right).defect y =
      (3 : ZMod M) ^ right.length * left.defect y +
        (2 : ZMod M) ^ left.rise * right.defect y := by
  simp [concat, defect]
  ring

/-- 同じ normalized word を `n` 回 chronological に連結する。 -/
def concatIterate
    {M : ℕ}
    (B : ModularStandardWordPacket M) :
    ℕ → ModularStandardWordPacket M
  | 0 => empty M
  | n + 1 => (concatIterate B n).concat B

@[simp] theorem concatIterate_zero
    {M : ℕ}
    (B : ModularStandardWordPacket M) :
    B.concatIterate 0 = empty M := rfl

@[simp] theorem concatIterate_succ
    {M : ℕ}
    (B : ModularStandardWordPacket M)
    (n : ℕ) :
    B.concatIterate (n + 1) =
      (B.concatIterate n).concat B := rfl

/-- `concatIterate` で連結した block の長さ。 -/
theorem concatIterate_length
    {M : ℕ}
    (B : ModularStandardWordPacket M)
    (n : ℕ) :
    (B.concatIterate n).length = n * B.length := by
  induction n with
  | zero =>
      simp [concatIterate, empty]
  | succ n ih =>
      rw [concatIterate_succ, concat_length, ih]
      simp [Nat.add_mul]

/-- `concatIterate` で連結した block の local dyadic rise。 -/
theorem concatIterate_rise
    {M : ℕ}
    (B : ModularStandardWordPacket M)
    (n : ℕ) :
    (B.concatIterate n).rise = n * B.rise := by
  induction n with
  | zero =>
      simp [concatIterate, empty]
  | succ n ih =>
      rw [concatIterate_succ, concat_rise, ih]
      simp [Nat.add_mul]

/--
continued-fraction standard-word recurrence

  W_(r+1) = W_r ^ a_r ++ W_(r-1)

に対応する一段。

`current` を `a` 個 chronological に並べ、
その右に `older` を付ける。
-/
def next
    {M : ℕ}
    (older current : ModularStandardWordPacket M)
    (a : ℕ) : ModularStandardWordPacket M :=
  (current.concatIterate a).concat older

/-- CF recurrence は length を `older + a*current` で更新する。 -/
theorem next_length
    {M : ℕ}
    (older current : ModularStandardWordPacket M)
    (a : ℕ) :
    (next older current a).length =
      older.length + a * current.length := by
  rw [next, concat_length, concatIterate_length]
  omega

/-- CF recurrence は rise も同じ線形 recurrence で更新する。 -/
theorem next_rise
    {M : ℕ}
    (older current : ModularStandardWordPacket M)
    (a : ℕ) :
    (next older current a).rise =
      older.rise + a * current.rise := by
  rw [next, concat_rise, concatIterate_rise]
  omega

/--
原点正規化 packet を origin-prefix 用 modular transfer にする。

  E_(P)(y) = 3^P * E_0(y) + F[0,P](y)

の local affine summary。
-/
def originTransfer
    {M : ℕ}
    (B : ModularStandardWordPacket M)
    (y : ZMod M) : ModularStandardBlockTransfer M :=
  {
    mul := (3 : ZMod M) ^ B.length
    add := B.defect y
  }

/-- origin transfer の作用。 -/
theorem originTransfer_apply
    {M : ℕ}
    (B : ModularStandardWordPacket M)
    (y x : ZMod M) :
    (B.originTransfer y).apply x =
      (3 : ZMod M) ^ B.length * x + B.defect y := by
  rfl

/--
odd standard scale の shifted corrected dictionary が与える modular transfer。

odd scale では

  2^beta_l F[l,l+P](y)
    = 3^l L(y) + (2^Q - 3^P) E_l(y)

なので prefix defect の更新は

  E_(l+P)(y)
    = 2^Q E_l(y) + 3^l L(y).

ここで normalized packet の `rise = Q`、`defect y = L(y)` と読む。
この定義自身は `criticalIntervalPhiZ` を評価しない。
-/
def oddShiftedTransfer
    {M : ℕ}
    (B : ModularStandardWordPacket M)
    (left : ℕ)
    (y : ZMod M) : ModularStandardBlockTransfer M :=
  {
    mul := (2 : ZMod M) ^ B.rise
    add := (3 : ZMod M) ^ left * B.defect y
  }

/-- odd shifted transfer の作用。 -/
theorem oddShiftedTransfer_apply
    {M : ℕ}
    (B : ModularStandardWordPacket M)
    (left : ℕ)
    (y x : ZMod M) :
    (B.oddShiftedTransfer left y).apply x =
      (2 : ZMod M) ^ B.rise * x +
        (3 : ZMod M) ^ left * B.defect y := by
  rfl

end ModularStandardWordPacket

end ThirdExampleSearch
end CSTMicro
end Collatz2
