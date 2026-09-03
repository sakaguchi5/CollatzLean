import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ActualOstrowskiStandardBlockTransfer

/-!
# 第3例探索 次段 2: canonical Ostrowski block list 全体の transfer

一つの `ActualCriticalPhaseBlock` が prefix defect を左端から右端へ exact に運ぶことは
`ActualOstrowskiStandardBlockTransfer` で証明済みである。

ここでは canonical Ostrowski block list

  [B₁, B₂, ..., Bₛ]

全体を `StandardBlockTransfer.comp` で fold し、その合成 transfer を origin に適用すると
full prefix defect `criticalPrefixDefectZ n y` が exact に得られることを示す。

従って巨大 prefix を block ごとに step-by-step 展開する必要はなく、各 standard block の
affine summary だけを DAG / memoization で合成すればよい。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

open ExternalArithmetic

/--
phase block list の transfer を chronological order で合成する。
先頭 block を最初に適用し、残りの transfer をその後に適用する。
-/
def actualPhaseBlockTransferFold :
    List ActualCriticalPhaseBlock → ℤ → StandardBlockTransfer
  | [], _ => StandardBlockTransfer.id
  | B :: Bs, y =>
      (actualPhaseBlockTransferFold Bs y).comp
        (standardBlockTransferOfActualPhaseBlock B y)

@[simp] theorem actualPhaseBlockTransferFold_nil
    (y : ℤ) :
    actualPhaseBlockTransferFold [] y = StandardBlockTransfer.id := rfl

@[simp] theorem actualPhaseBlockTransferFold_cons
    (B : ActualCriticalPhaseBlock)
    (Bs : List ActualCriticalPhaseBlock)
    (y : ℤ) :
    actualPhaseBlockTransferFold (B :: Bs) y =
      (actualPhaseBlockTransferFold Bs y).comp
        (standardBlockTransferOfActualPhaseBlock B y) := rfl

/--
scale listを consecutive phase blocks に展開した場合の同じ transfer。
証明を簡潔にするため left endpoint と scale list を直接再帰する版を持つ。
-/
def actualScaleTransferFrom :
    ℕ → List ℕ → ℤ → StandardBlockTransfer
  | _, [], _ => StandardBlockTransfer.id
  | left, r :: rs, y =>
      let B : ActualCriticalPhaseBlock := ⟨left, r⟩
      (actualScaleTransferFrom B.right rs y).comp
        (standardBlockTransferOfActualPhaseBlock B y)

/-- explicit phase-block list の fold と scale-list 再帰は exact に同じ transfer。 -/
theorem actualPhaseBlockTransferFold_phaseBlocksFrom
    (left : ℕ)
    (scales : List ℕ)
    (y : ℤ) :
    actualPhaseBlockTransferFold
        (actualCriticalPhaseBlocksFrom left scales) y =
      actualScaleTransferFrom left scales y := by
  induction scales generalizing left with
  | nil =>
      rfl
  | cons r rs ih =>
      let B : ActualCriticalPhaseBlock := ⟨left, r⟩
      change
        (actualPhaseBlockTransferFold
            (actualCriticalPhaseBlocksFrom B.right rs) y).comp
          (standardBlockTransferOfActualPhaseBlock B y) =
        (actualScaleTransferFrom B.right rs y).comp
          (standardBlockTransferOfActualPhaseBlock B y)
      rw [ih]

/--
scale list の先頭 block を一回適用すると、
prefix defect はその block の右端へ exact に移る。
-/
theorem actualScaleTransferFrom_cons_apply_prefixDefect_head
    (left r : ℕ)
    (rs : List ℕ)
    (y : ℤ) :
    let B : ActualCriticalPhaseBlock := ⟨left, r⟩
    (actualScaleTransferFrom left (r :: rs) y).apply
        (criticalPrefixDefectZ left y) =
      (actualScaleTransferFrom B.right rs y).apply
        (criticalPrefixDefectZ B.right y) := by
  let B : ActualCriticalPhaseBlock := ⟨left, r⟩
  have hOne :
      (standardBlockTransferOfActualPhaseBlock B y).apply
          (criticalPrefixDefectZ left y) =
        criticalPrefixDefectZ B.right y := by
    simpa [B] using
      standardBlockTransferOfActualPhaseBlock_apply_prefixDefect B y
  dsimp only
  rw [actualScaleTransferFrom]
  rw [standardBlockTransfer_comp]
  rw [hOne]

/--
先頭 phase block の右端に tail の scale mass を足した位置は、
scale list 全体の full right endpoint と一致する。
-/
theorem actualCriticalPhaseBlock_right_add_scaleMass
    (left r : ℕ)
    (rs : List ℕ) :
    let B : ActualCriticalPhaseBlock := ⟨left, r⟩
    B.right + actualCriticalBlockScaleMass rs =
      left + actualCriticalBlockScaleMass (r :: rs) := by
  dsimp only
  simp [ActualCriticalPhaseBlock.right,
    ActualCriticalPhaseBlock.length,
    actualCriticalBlockScaleMass,
    Nat.add_assoc]

/--
consecutive scale blocks の合成 transfer は、left endpoint の prefix defect を
block 列の full right endpoint まで exact に運ぶ。
-/
theorem actualScaleTransferFrom_apply_prefixDefect
    (left : ℕ)
    (scales : List ℕ)
    (y : ℤ) :
    (actualScaleTransferFrom left scales y).apply
        (criticalPrefixDefectZ left y) =
      criticalPrefixDefectZ
        (left + actualCriticalBlockScaleMass scales) y := by
  induction scales generalizing left with
  | nil =>
      simp [actualScaleTransferFrom,
        StandardBlockTransfer.id, StandardBlockTransfer.apply]
  | cons r rs ih =>
      let B : ActualCriticalPhaseBlock := ⟨left, r⟩
      have hHead :
          (actualScaleTransferFrom left (r :: rs) y).apply
              (criticalPrefixDefectZ left y) =
            (actualScaleTransferFrom B.right rs y).apply
              (criticalPrefixDefectZ B.right y) := by
        simpa [B] using
          actualScaleTransferFrom_cons_apply_prefixDefect_head
            left r rs y
      have hEnd :
          B.right + actualCriticalBlockScaleMass rs =
            left + actualCriticalBlockScaleMass (r :: rs) := by
        simpa [B] using
          actualCriticalPhaseBlock_right_add_scaleMass left r rs
      calc
        (actualScaleTransferFrom left (r :: rs) y).apply
            (criticalPrefixDefectZ left y)
            =
          (actualScaleTransferFrom B.right rs y).apply
            (criticalPrefixDefectZ B.right y) := hHead
        _ =
          criticalPrefixDefectZ
            (B.right + actualCriticalBlockScaleMass rs) y :=
              ih (left := B.right)
        _ =
          criticalPrefixDefectZ
            (left + actualCriticalBlockScaleMass (r :: rs)) y := by
              rw [hEnd]


/--
任意 scale list から作った explicit consecutive phase blocks の fold は、
left prefix defect を full endpoint へ exact に運ぶ。
-/
theorem actualPhaseBlockTransferFold_phaseBlocksFrom_apply_prefixDefect
    (left : ℕ)
    (scales : List ℕ)
    (y : ℤ) :
    (actualPhaseBlockTransferFold
        (actualCriticalPhaseBlocksFrom left scales) y).apply
        (criticalPrefixDefectZ left y) =
      criticalPrefixDefectZ
        (left + actualCriticalBlockScaleMass scales) y := by
  rw [actualPhaseBlockTransferFold_phaseBlocksFrom]
  exact actualScaleTransferFrom_apply_prefixDefect left scales y

/-- arbitrary prefix `n` の canonical Ostrowski block list 全体の transfer。 -/
def actualCriticalOstrowskiTransfer
    (n : ℕ)
    (y : ℤ) : StandardBlockTransfer :=
  actualPhaseBlockTransferFold
    (actualCriticalOstrowskiPhaseBlocks n) y

/--
canonical Ostrowski block list 全体の transfer を origin prefix defect に適用すると、
full prefix defect `E_n(y)` が exact に得られる。
-/
theorem actualCriticalOstrowskiTransfer_apply_originPrefixDefect
    (n : ℕ)
    (y : ℤ) :
    (actualCriticalOstrowskiTransfer n y).apply
        (criticalPrefixDefectZ 0 y) =
      criticalPrefixDefectZ n y := by
  unfold actualCriticalOstrowskiTransfer
    actualCriticalOstrowskiPhaseBlocks
  rw [actualPhaseBlockTransferFold_phaseBlocksFrom]
  have h :=
    actualScaleTransferFrom_apply_prefixDefect
      0 (actualCriticalOstrowskiBlockScales n) y
  rw [actualCriticalOstrowskiBlockScales_mass_eq] at h
  simpa using h

/-- origin prefix defect は zero。 -/
@[simp] theorem criticalPrefixDefectZ_zero_thirdExample
    (y : ℤ) :
    criticalPrefixDefectZ 0 y = 0 := by
  unfold criticalPrefixDefectZ criticalPrefixGapZ
  simp [criticalPrefixPhiZ]

/--
従って canonical Ostrowski transfer は zero state から直接 full prefix defect を生成する。
探索器が実際に使う最終形。
-/
theorem actualCriticalOstrowskiTransfer_apply_zero
    (n : ℕ)
    (y : ℤ) :
    (actualCriticalOstrowskiTransfer n y).apply 0 =
      criticalPrefixDefectZ n y := by
  rw [← criticalPrefixDefectZ_zero_thirdExample y]
  exact actualCriticalOstrowskiTransfer_apply_originPrefixDefect n y

/--
既存 canonical phase-defect fold と、新しい StandardBlockTransfer fold は同じ full prefix defect を計算する。
これにより旧 Ostrowski 算術と新しい DAG transfer 探索器の結果を lossless に比較できる。
-/
theorem actualCriticalOstrowskiTransfer_apply_zero_eq_phaseDefectFold
    (n : ℕ)
    (y : ℤ) :
    (actualCriticalOstrowskiTransfer n y).apply 0 =
      actualCriticalPhaseDefectFold
        0 (actualCriticalOstrowskiBlockScales n) y := by
  rw [actualCriticalOstrowskiTransfer_apply_zero]
  exact criticalPrefixDefectZ_eq_actualOstrowskiPhaseDefectFold n y

end ThirdExampleSearch
end CSTMicro
end Collatz2
