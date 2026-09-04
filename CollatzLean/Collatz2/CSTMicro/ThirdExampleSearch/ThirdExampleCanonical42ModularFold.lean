import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleOneBlockModularCorrectness
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleConvergent22Checkpoint

/-!
# 第3例探索 C: canonical 42-block modular fold

canonical 42 blocks のうち最初の

  scale 3 x2, scale 5 x3, scale 7 x5

は合計 305 columns しかない。
`shiftedDefect_correctedDictionary_of_odd` の public range は scale 9 以降なので、
この 305-column collar は exact prefix defect を直接 modular 化する。

残り 32 blocks

  scale 9 x23, 11 x2, 13, 15, 17 x3, 19, 21

だけを A/B の certified hot-path transfer で fold する。

これにより巨大 block 内部を一列も展開せず、full target prefix defect mod M へ到達する。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

open ExternalArithmetic
open ModularStandardBlockTransfer

/-- scale 3/5/7 collar の total length。 -/
def thirdExampleInitialExactPrefixLength : ℕ := 305

/-- scale 9 以降の32 blocks。 -/
def thirdExampleLargeCanonicalBlockScales : List ℕ :=
  List.replicate 23 9 ++
  List.replicate 2 11 ++
  [13] ++
  [15] ++
  List.replicate 3 17 ++
  [19] ++
  [21]

/-- large side は exact に32 blocks。 -/
theorem thirdExampleLargeCanonicalBlockScales_length :
    thirdExampleLargeCanonicalBlockScales.length = 32 := by
  norm_num [thirdExampleLargeCanonicalBlockScales]

/-- literal scale mass。hot path では `criticalPowerP` を呼ばない。 -/
def thirdExampleLiteralScaleMass : List ℕ → ℕ
  | [] => 0
  | r :: rs =>
      thirdExampleLiteralPowerP r + thirdExampleLiteralScaleMass rs

/-- 305 collar + 32 large blocks は target p 全体を覆う。 -/
theorem thirdExampleInitial_add_largeMass_eq_targetP :
    thirdExampleInitialExactPrefixLength +
        thirdExampleLiteralScaleMass thirdExampleLargeCanonicalBlockScales =
      thirdExampleTargetP := by
  norm_num [
    thirdExampleInitialExactPrefixLength,
    thirdExampleLiteralScaleMass,
    thirdExampleLargeCanonicalBlockScales,
    thirdExampleLiteralPowerP,
    thirdExampleTargetP
  ]
  simp only [List.reduceReplicate, List.cons_append, List.nil_append]
  decide

/--
fixed block placement が corrected dictionary の phase corridor 内に留まることを
literal P table だけで検査する。
-/
def ThirdExampleLargePlacementOK :
    ℕ → List ℕ → Prop
  | _, [] => True
  | left, r :: rs =>
      9 ≤ r ∧
      r ≤ 21 ∧
      r % 2 = 1 ∧
      left + thirdExampleLiteralPowerP r <
        thirdExampleLiteralPowerP (r + 1) ∧
      ThirdExampleLargePlacementOK
        (left + thirdExampleLiteralPowerP r) rs

/-- fixed 32 blocks はすべて各 scale の phase corridor に収まる。 -/
theorem thirdExampleLargePlacementOK_fixed :
    ThirdExampleLargePlacementOK
      thirdExampleInitialExactPrefixLength
      thirdExampleLargeCanonicalBlockScales := by
  simp only [
    thirdExampleInitialExactPrefixLength,
    thirdExampleLargeCanonicalBlockScales
  ]
  simp [
    ThirdExampleLargePlacementOK,
    thirdExampleLiteralPowerP
  ]

/--
最初の 305 columns を exact に計算する小 collar transfer。
ここだけは `criticalPrefixDefectZ 305` を直接使うが、巨大 window には依存しない。
-/
def thirdExampleInitial305ModularTransfer
    (M : ℕ)
    (y : ℤ) : ModularStandardBlockTransfer M :=
  {
    mul := (3 : ZMod M) ^ thirdExampleInitialExactPrefixLength
    add := ((criticalPrefixDefectZ
      thirdExampleInitialExactPrefixLength y : ℤ) : ZMod M)
  }

@[simp] theorem thirdExampleInitial305ModularTransfer_apply_zero
    (M : ℕ)
    (y : ℤ) :
    (thirdExampleInitial305ModularTransfer M y).apply 0 =
      ((criticalPrefixDefectZ
        thirdExampleInitialExactPrefixLength y : ℤ) : ZMod M) := by
  simp [thirdExampleInitial305ModularTransfer,
    ModularStandardBlockTransfer.apply]

/--
scale list を chronological に高速 modular fold する。
left endpoint の更新も literal P table だけで行う。
-/
def thirdExampleLargeModularFoldFrom
    (M : ℕ) :
    ℕ → List ℕ → ZMod M → ModularStandardBlockTransfer M
  | _, [], _ => ModularStandardBlockTransfer.id M
  | left, r :: rs, y =>
      (thirdExampleLargeModularFoldFrom
          M
          (left + thirdExampleLiteralPowerP r)
          rs y).comp
        (thirdExampleCertifiedOddScaleTransferAt M r left y)

/-- fixed 32-block large fold。 -/
def thirdExampleLargeModularFold
    (M : ℕ)
    (y : ZMod M) : ModularStandardBlockTransfer M :=
  thirdExampleLargeModularFoldFrom
    M thirdExampleInitialExactPrefixLength
    thirdExampleLargeCanonicalBlockScales y

/-- full 42-block fold = small exact collar の後に large certified fold。 -/
def thirdExampleCanonical42ModularFold
    (M : ℕ)
    (y : ℤ) : ModularStandardBlockTransfer M :=
  (thirdExampleLargeModularFold M (y : ZMod M)).comp
    (thirdExampleInitial305ModularTransfer M y)

/--
placement certificate の下で large fold が actual prefix defect を exact に運ぶ。
-/
theorem thirdExampleLargeModularFoldFrom_apply_prefixDefect
    {M : ℕ}
    (Cert : ThirdExampleCFPacketCertification M)
    (left : ℕ)
    (scales : List ℕ)
    (hOK : ThirdExampleLargePlacementOK left scales)
    (y : ℤ) :
    (thirdExampleLargeModularFoldFrom
        M left scales (y : ZMod M)).apply
        ((criticalPrefixDefectZ left y : ℤ) : ZMod M) =
      ((criticalPrefixDefectZ
          (left + thirdExampleLiteralScaleMass scales) y : ℤ) : ZMod M) := by
  induction scales generalizing left with
  | nil =>
      simp [thirdExampleLargeModularFoldFrom,
        thirdExampleLiteralScaleMass,
        ModularStandardBlockTransfer.id,
        ModularStandardBlockTransfer.apply]
  | cons r rs ih =>
      simp only [ThirdExampleLargePlacementOK] at hOK
      rcases hOK with ⟨hr9, hr21, hrOdd, hRange, hTail⟩
      let C := Cert.certify r hr9 hr21 hrOdd
      have hHead :=
        thirdExampleCertifiedOddScaleTransferAt_apply_of_literalRange
          C hRange y
      rw [thirdExampleLargeModularFoldFrom]
      rw [ModularStandardBlockTransfer.comp_apply]
      rw [hHead]
      have hTailApply :=
        ih
          (left := left + thirdExampleLiteralPowerP r)
          hTail
      rw [hTailApply]
      have hIndex :
          (left + thirdExampleLiteralPowerP r) +
              thirdExampleLiteralScaleMass rs =
            left + thirdExampleLiteralScaleMass (r :: rs) := by
        simp [thirdExampleLiteralScaleMass]
        omega
      rw [hIndex]

/-- fixed large fold の endpoint は target p。 -/
theorem thirdExampleLargeModularFold_apply_prefix305
    {M : ℕ}
    (Cert : ThirdExampleCFPacketCertification M)
    (y : ℤ) :
    (thirdExampleLargeModularFold M (y : ZMod M)).apply
        ((criticalPrefixDefectZ
          thirdExampleInitialExactPrefixLength y : ℤ) : ZMod M) =
      ((criticalPrefixDefectZ thirdExampleTargetP y : ℤ) : ZMod M) := by
  unfold thirdExampleLargeModularFold
  have h :=
    thirdExampleLargeModularFoldFrom_apply_prefixDefect
      Cert
      thirdExampleInitialExactPrefixLength
      thirdExampleLargeCanonicalBlockScales
      thirdExampleLargePlacementOK_fixed
      y
  rw [thirdExampleInitial_add_largeMass_eq_targetP] at h
  exact h

/--
A/B certification があれば、full 42-block hot-path fold は zero state から
actual full prefix defect mod M を exact に返す。
-/
theorem thirdExampleCanonical42ModularFold_apply_zero
    {M : ℕ}
    (Cert : ThirdExampleCFPacketCertification M)
    (y : ℤ) :
    (thirdExampleCanonical42ModularFold M y).apply 0 =
      ((criticalPrefixDefectZ thirdExampleTargetP y : ℤ) : ZMod M) := by
  unfold thirdExampleCanonical42ModularFold
  rw [ModularStandardBlockTransfer.comp_apply]
  rw [thirdExampleInitial305ModularTransfer_apply_zero]
  exact thirdExampleLargeModularFold_apply_prefix305 Cert y

/-- left collar modulus 専用 wrapper。 -/
theorem thirdExampleCanonical42LeftFold_apply_zero
    (Cert : ThirdExampleCFPacketCertification thirdExampleLeftModulus)
    (y : ℤ) :
    (thirdExampleCanonical42ModularFold
        thirdExampleLeftModulus y).apply 0 =
      ((criticalPrefixDefectZ thirdExampleTargetP y : ℤ) :
        ZMod thirdExampleLeftModulus) :=
  thirdExampleCanonical42ModularFold_apply_zero Cert y

/-- right collar modulus 専用 wrapper。 -/
theorem thirdExampleCanonical42RightFold_apply_zero
    (Cert : ThirdExampleCFPacketCertification thirdExampleRightModulus)
    (y : ℤ) :
    (thirdExampleCanonical42ModularFold
        thirdExampleRightModulus y).apply 0 =
      ((criticalPrefixDefectZ thirdExampleTargetP y : ℤ) :
        ZMod thirdExampleRightModulus) :=
  thirdExampleCanonical42ModularFold_apply_zero Cert y

end ThirdExampleSearch
end CSTMicro
end Collatz2
