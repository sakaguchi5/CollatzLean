import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ModularContinuedFractionStandardBlock
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleConvergent22Checkpoint

/-!
# 第3例探索: scale 3,5,...,21 の modular standard-block generator

convergent 22 window で必要な standard scales は

  3, 5, 7, 9, 11, 13, 15, 17, 19, 21.

ここでは `criticalPowerP/Q` や巨大 power comparison を一切呼ばない。
scale 2 / 3 の小さい normalized packet だけを seed とし、literal checkpoint の
continued-fraction partial quotient

  a_3,...,a_20

を使って

  W_(r+1) = W_r ^ a_r W_(r-1)

を18段だけ回す。

各段の `phi` / `gap` は `ZMod M` 上で更新されるため、scale 21 の長さが
6_189_245_291 でも block 内部を展開しない。

actual Farey/convergent 列との一致は certification 層に分離し、探索 hot path は
この literal recurrence だけを使う。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

open ModularStandardWordPacket

/--
scale `r` から `r+1` を作る partial quotient checkpoint。
実探索で使うのは `3 <= r <= 20` のみ。
-/
def thirdExampleCFPartialQuotient (r : ℕ) : ℕ :=
  match r with
  | 3  => 2
  | 4  => 2
  | 5  => 3
  | 6  => 1
  | 7  => 5
  | 8  => 2
  | 9  => 23
  | 10 => 2
  | 11 => 2
  | 12 => 1
  | 13 => 1
  | 14 => 55
  | 15 => 1
  | 16 => 4
  | 17 => 3
  | 18 => 1
  | 19 => 1
  | 20 => 15
  | _  => 0

/-- scale 2 の小さい exact normalized packet。 -/
def thirdExampleScale2Packet
    (M : ℕ) : ModularStandardWordPacket M :=
  {
    length := 1
    rise := 1
    phi := 1
    gap := -1
  }

/-- scale 3 の小さい exact normalized packet。 -/
def thirdExampleScale3Packet
    (M : ℕ) : ModularStandardWordPacket M :=
  {
    length := 2
    rise := 3
    phi := 5
    gap := -1
  }

/--
`n` 回 CF recurrence を進めた `(older,current)` packet pair。

* `n=0`: scale `(2,3)`
* `n=1`: scale `(3,4)`
* ...
* `n=18`: scale `(20,21)`

従って current は scale `3+n`。
-/
def thirdExampleCFPacketPair
    (M : ℕ) : ℕ →
      ModularStandardWordPacket M × ModularStandardWordPacket M
  | 0 =>
      (thirdExampleScale2Packet M, thirdExampleScale3Packet M)
  | n + 1 =>
      let prev := thirdExampleCFPacketPair M n
      let r := n + 3
      (prev.2,
        ModularStandardWordPacket.next
          prev.1 prev.2 (thirdExampleCFPartialQuotient r))

/--
scale `r >= 3` の normalized modular packet。
探索では `r = 3,5,...,21` だけを呼ぶ。
-/
def thirdExampleScalePacket
    (M r : ℕ) : ModularStandardWordPacket M :=
  (thirdExampleCFPacketPair M (r - 3)).2

/-- relevant odd scales。 -/
def thirdExampleOddStandardScales : List ℕ :=
  [3, 5, 7, 9, 11, 13, 15, 17, 19, 21]

/-- relevant scale は10種類。 -/
theorem thirdExampleOddStandardScales_length :
    thirdExampleOddStandardScales.length = 10 := by
  norm_num [thirdExampleOddStandardScales]

/--
各 relevant odd scale の packet table。
値はすべて18段以内の CF recurrence だけから生成される。
-/
def thirdExampleOddScalePackets
    (M : ℕ) : List (ℕ × ModularStandardWordPacket M) :=
  thirdExampleOddStandardScales.map
    (fun r => (r, thirdExampleScalePacket M r))

/-- packet table も10要素。 -/
theorem thirdExampleOddScalePackets_length
    (M : ℕ) :
    (thirdExampleOddScalePackets M).length = 10 := by
  simp [thirdExampleOddScalePackets,
    thirdExampleOddStandardScales]

/--
任意 modulus 上で、odd scale `r` の shifted modular transfer を recurrence packet から作る。
`left` はこの block の actual left endpoint。
-/
def thirdExampleOddScaleTransferAt
    (M r left : ℕ)
    (y : ZMod M) : ModularStandardBlockTransfer M :=
  (thirdExampleScalePacket M r).oddShiftedTransfer left y

/-- start 側 `mod 2^68` 用。 -/
def thirdExampleLeftOddScaleTransferAt
    (r left : ℕ)
    (y : ZMod thirdExampleLeftModulus) :
    ThirdExampleLeftModularTransfer :=
  thirdExampleOddScaleTransferAt
    thirdExampleLeftModulus r left y

/-- endpoint 側 `mod 3^42` 用。 -/
def thirdExampleRightOddScaleTransferAt
    (r left : ℕ)
    (y : ZMod thirdExampleRightModulus) :
    ThirdExampleRightModularTransfer :=
  thirdExampleOddScaleTransferAt
    thirdExampleRightModulus r left y

/--
scale 3 packet は seed そのもの。
この theorem は recurrence index の向きを固定する checkpoint。
-/
theorem thirdExampleScalePacket_three
    (M : ℕ) :
    thirdExampleScalePacket M 3 = thirdExampleScale3Packet M := by
  rfl

/--
一段目は `a_3 = 2` を使って scale 4 を生成する。
standard-word recurrence の向き `W_4 = W_3^2 W_2` を固定する checkpoint。
-/
theorem thirdExampleScalePacket_four
    (M : ℕ) :
    thirdExampleScalePacket M 4 =
      ModularStandardWordPacket.next
        (thirdExampleScale2Packet M)
        (thirdExampleScale3Packet M)
        2 := by
  rfl

/--
scale 3 の length/rise checkpoint。
-/
@[simp] theorem thirdExampleScalePacket_three_length
    (M : ℕ) :
    (thirdExampleScalePacket M 3).length = 2 := by
  rfl

@[simp] theorem thirdExampleScalePacket_three_rise
    (M : ℕ) :
    (thirdExampleScalePacket M 3).rise = 3 := by
  rfl

/--
scale 4 は `P_4 = P_2 + 2 P_3 = 5`,
`Q_4-1 = 1 + 2*3 = 7` を packet recurrence だけで復元する。
巨大 power comparison は現れない。
-/
@[simp] theorem thirdExampleScalePacket_four_length
    (M : ℕ) :
    (thirdExampleScalePacket M 4).length = 5 := by
  rw [thirdExampleScalePacket_four]
  rw [ModularStandardWordPacket.next_length]
  rfl

@[simp] theorem thirdExampleScalePacket_four_rise
    (M : ℕ) :
    (thirdExampleScalePacket M 4).rise = 7 := by
  rw [thirdExampleScalePacket_four]
  rw [ModularStandardWordPacket.next_rise]
  rfl

/--
scale 21 packet を直接呼ぶ hot-path 名。
内部計算は18段の CF recurrence と `ZMod` 演算だけ。
-/
def thirdExampleScale21Packet
    (M : ℕ) : ModularStandardWordPacket M :=
  thirdExampleScalePacket M 21

/-- 左 modulus 上の scale 21 packet。 -/
def thirdExampleLeftScale21Packet :
    ModularStandardWordPacket thirdExampleLeftModulus :=
  thirdExampleScale21Packet thirdExampleLeftModulus

/-- 右 modulus 上の scale 21 packet。 -/
def thirdExampleRightScale21Packet :
    ModularStandardWordPacket thirdExampleRightModulus :=
  thirdExampleScale21Packet thirdExampleRightModulus

end ThirdExampleSearch
end CSTMicro
end Collatz2
