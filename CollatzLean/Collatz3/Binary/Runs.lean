import CollatzLean.Collatz3.Binary.Basic

/-!
# Collatz3 Binary: binary runs

LSB-first binary word を maximal constant run に圧縮するための最小語彙。

run 自体は `(bit, length)` の pair として持ち、新しい大きな structure は導入しない。
`binaryRuns` は下位 bit から上位 bit へ並ぶ。
-/

namespace Collatz3
namespace Binary

/-- binary run。第一成分が bit、第二成分が run length。 -/
abbrev Run := Bool × ℕ

/--
既に run 圧縮された tail の先頭へ 1 bit を追加する。
同じ bit なら先頭 run を 1 延長し、異なれば長さ 1 の新 run を作る。
-/
def prependRunBit (b : Bool) : List Run → List Run
  | [] => [(b, 1)]
  | (c, n) :: rs =>
      if b = c then
        (c, n + 1) :: rs
      else
        (b, 1) :: (c, n) :: rs

/-- LSB-first binary word の maximal run 列。 -/
def binaryRuns : List Bool → List Run
  | [] => []
  | b :: bs => prependRunBit b (binaryRuns bs)

/-- run の長さ成分だけを読む。 -/
def runLengths (bits : List Bool) : List ℕ :=
  (binaryRuns bits).map Prod.snd

@[simp] theorem binaryRuns_nil : binaryRuns [] = [] := rfl

@[simp] theorem binaryRuns_singleton (b : Bool) :
    binaryRuns [b] = [(b, 1)] := by
  simp [binaryRuns, prependRunBit]

@[simp] theorem runLengths_nil : runLengths [] = [] := rfl

@[simp] theorem runLengths_singleton (b : Bool) :
    runLengths [b] = [1] := by
  simp [runLengths]

/-- 非空 binary word の run 列は非空。 -/
theorem binaryRuns_nonempty
    {bits : List Bool}
    (h : bits ≠ []) :
    binaryRuns bits ≠ [] := by
  cases bits with
  | nil => contradiction
  | cons b bs =>
      cases hRuns : binaryRuns bs with
      | nil =>
          simp [binaryRuns, hRuns, prependRunBit]
      | cons r rs =>
          rcases r with ⟨c, n⟩
          by_cases hbc : b = c <;>
            simp [binaryRuns, hRuns, prependRunBit, hbc]

end Binary
end Collatz3
