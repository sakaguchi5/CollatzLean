import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleOddScaleModularTransfers
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.ShiftedCorrectedChristoffelDictionary

/-!
# 第3例探索 A: CF packet certification

前段の experimental generator では、standard block の `rise` に
`beattyIndex P_r` をそのまま入れていたため、even scale の

  beattyIndex P_r = Q_r - 1

という endpoint correction を次段へ持ち越してしまう。

Christoffel numerator の標準再帰で使うべき full height は `Q_r` であり、
さらに Farey determinant の向きに応じて concatenation order が交互に反転する。

そこで探索 hot path 用の packet をここで改めて

* scale 2 seed : (P,Q,Phi,Gap) = (1,2,1,1)
* scale 3 seed : (2,3,5,-1)
* odd r  : W_(r+1) = W_r^a ++ W_(r-1)
* even r : W_(r+1) = W_(r-1) ++ W_r^a

として作る。

このファイルの後半では、巨大 Farey power comparison を hot path から切り離すため、
この literal packet と actual power-Farey/Christoffel packet の一致を
proof-only certificate として切り出す。

重要: certificate は探索時の計算データには入らない。後段の soundness theorem だけが使う。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

open ExternalArithmetic
open ModularStandardWordPacket

/--
actual Christoffel recurrence 用の corrected seed: scale 2 は full height `Q_2 = 2`。
-/
def thirdExampleCertifiedScale2Packet
    (M : ℕ) : ModularStandardWordPacket M :=
  {
    length := 1
    rise := 2
    phi := 1
    gap := 1
  }

/-- scale 3 は `(P_3,Q_3)=(2,3)`, `Phi_3=5`, `2^3-3^2=-1`。 -/
def thirdExampleCertifiedScale3Packet
    (M : ℕ) : ModularStandardWordPacket M :=
  {
    length := 2
    rise := 3
    phi := 5
    gap := -1
  }

/--
Farey determinant の向きを反映した一段。

* odd current scale: `current^a ++ older`
* even current scale: `older ++ current^a`
-/
def thirdExampleCertifiedCFNext
    {M : ℕ}
    (r : ℕ)
    (older current : ModularStandardWordPacket M)
    (a : ℕ) : ModularStandardWordPacket M :=
  if r % 2 = 1 then
    (current.concatIterate a).concat older
  else
    older.concat (current.concatIterate a)

/--
corrected `(older,current)` packet recurrence。
`n=0` は scale `(2,3)`、current は scale `3+n`。
-/
def thirdExampleCertifiedCFPacketPair
    (M : ℕ) : ℕ →
      ModularStandardWordPacket M × ModularStandardWordPacket M
  | 0 =>
      (thirdExampleCertifiedScale2Packet M,
       thirdExampleCertifiedScale3Packet M)
  | n + 1 =>
      let prev := thirdExampleCertifiedCFPacketPair M n
      let r := n + 3
      (prev.2,
        thirdExampleCertifiedCFNext
          r prev.1 prev.2 (thirdExampleCFPartialQuotient r))

/-- scale `r >= 3` の corrected hot-path packet。 -/
def thirdExampleCertifiedScalePacket
    (M r : ℕ) : ModularStandardWordPacket M :=
  (thirdExampleCertifiedCFPacketPair M (r - 3)).2

/-- scale 3 checkpoint。 -/
@[simp] theorem thirdExampleCertifiedScalePacket_three
    (M : ℕ) :
    thirdExampleCertifiedScalePacket M 3 =
      thirdExampleCertifiedScale3Packet M := by
  rfl

/-- even correction を full Q に戻したので scale 4 rise は 8。 -/
@[simp] theorem thirdExampleCertifiedScalePacket_four_rise
    (M : ℕ) :
    (thirdExampleCertifiedScalePacket M 4).rise = 8 := by
  rfl

/-- alternating concatenation により scale 5 rise は actual Q_5=19 に戻る。 -/
@[simp] theorem thirdExampleCertifiedScalePacket_five_rise
    (M : ℕ) :
    (thirdExampleCertifiedScalePacket M 5).rise = 19 := by
  rfl

/--
固定 window で使う literal `P_r` table。
これは実行用 checkpoint であり `criticalPowerP` を評価しない。
-/
def thirdExampleLiteralPowerP (r : ℕ) : ℕ :=
  match r with
  | 9  => 665
  | 10 => 15_601
  | 11 => 31_867
  | 12 => 79_335
  | 13 => 111_202
  | 14 => 190_537
  | 15 => 10_590_737
  | 16 => 10_781_274
  | 17 => 53_715_833
  | 18 => 171_928_773
  | 19 => 225_644_606
  | 20 => 397_573_379
  | 21 => 6_189_245_291
  | 22 => 6_586_818_670
  | _  => 0

/-- 同じ fixed window の literal `Q_r` table。 -/
def thirdExampleLiteralPowerQ (r : ℕ) : ℕ :=
  match r with
  | 9  => 1_054
  | 10 => 24_727
  | 11 => 50_508
  | 12 => 125_743
  | 13 => 176_251
  | 14 => 301_994
  | 15 => 16_785_921
  | 16 => 17_087_915
  | 17 => 85_137_581
  | 18 => 272_500_658
  | 19 => 357_638_239
  | 20 => 630_138_897
  | 21 => 9_809_721_694
  | 22 => 10_439_860_591
  | _  => 0

/-- endpoint checkpoint と literal table の一致。 -/
@[simp] theorem thirdExampleLiteralPowerP_twentyTwo :
    thirdExampleLiteralPowerP 22 = thirdExampleConvergent22P := by
  rfl

@[simp] theorem thirdExampleLiteralPowerQ_twentyTwo :
    thirdExampleLiteralPowerQ 22 = thirdExampleConvergent22Q := by
  rfl

/--
一つの relevant odd scale について、hot-path packet が actual arithmetic と一致すること。

この structure の proof fields は runtime では消える。巨大 `criticalPowerP/Q` や
`criticalChristoffelPhiAt` を探索ループの中で評価しないための境界である。
-/
structure ThirdExampleActualOddScalePacketCertificate
    (M r : ℕ) : Prop where
  nine_le : 9 ≤ r
  le_twentyOne : r ≤ 21
  odd : r % 2 = 1

  p_eq :
    criticalPowerP r = thirdExampleLiteralPowerP r
  q_eq :
    criticalPowerQ r = thirdExampleLiteralPowerQ r
  next_p_eq :
    criticalPowerP (r + 1) = thirdExampleLiteralPowerP (r + 1)

  length_eq :
    (thirdExampleCertifiedScalePacket M r).length = criticalPowerP r
  rise_eq :
    (thirdExampleCertifiedScalePacket M r).rise = criticalPowerQ r

  phi_eq :
    (thirdExampleCertifiedScalePacket M r).phi =
      ((criticalChristoffelPhiAt
          actualCriticalContinuedFractionData r : ℤ) : ZMod M)

  gap_eq :
    (thirdExampleCertifiedScalePacket M r).gap =
      ((actualCriticalRawPowerGap r : ℤ) : ZMod M)

/--
scale `9,11,...,21` 全体の proof-only certification interface。
探索器本体はこの object を引数に取らない。
-/
structure ThirdExampleCFPacketCertification
    (M : ℕ) : Prop where
  certify :
    ∀ r : ℕ,
      9 ≤ r →
      r ≤ 21 →
      r % 2 = 1 →
      ThirdExampleActualOddScalePacketCertificate M r

/-- certified hot-path packet の local defect は actual corrected linear formの mod M。 -/
theorem ThirdExampleActualOddScalePacketCertificate.defect_eq_correctedLinearForm
    {M r : ℕ}
    (C : ThirdExampleActualOddScalePacketCertificate M r)
    (y : ℤ) :
    (thirdExampleCertifiedScalePacket M r).defect (y : ZMod M) =
      ((actualCorrectedChristoffelLinearForm r y : ℤ) : ZMod M) := by
  unfold ModularStandardWordPacket.defect
  rw [C.phi_eq, C.gap_eq]
  unfold actualCorrectedChristoffelLinearForm
  rw [correctedChristoffelP_odd actualCriticalContinuedFractionData C.odd]
  rw [correctedChristoffelQ_odd actualCriticalContinuedFractionData C.odd]
  unfold actualCriticalRawPowerGap
  push_cast
  ring_nf
  rfl

end ThirdExampleSearch
end CSTMicro
end Collatz2
