import CollatzLean.Collatz2.Core.Realization

/-!
# Collatz2: lossless word intervals

局所対象を `prefix` / `suffix` / cut index の射影として先に定義せず、
元の word と exact decomposition を保持した interval として扱う。

`Interval` は新しい算術情報を追加しない。
`whole = left ++ body ++ right` という lossless な位置情報だけを保持する。
-/

namespace Collatz2

/-- word 内の一つの連続区間を exact decomposition で保持する。 -/
structure Interval (whole : Word) where
  left : Word
  body : Word
  right : Word
  decomp : whole = left ++ body ++ right

namespace Interval

/-- whole word 自身を interval として見る。 -/
def whole (w : Word) : Interval w :=
  { left := []
    body := w
    right := []
    decomp := by simp }

/-- interval body の affine transfer。 -/
def transfer {w : Word} (I : Interval w) : AffineTransfer :=
  AffineTransfer.ofWord I.body

/-- interval body の odd step 数。 -/
def oddSteps {w : Word} (I : Interval w) : ℕ :=
  Word.oddSteps I.body

/-- interval body の総2除算指数。 -/
def twoSteps {w : Word} (I : Interval w) : ℕ :=
  Word.twoSteps I.body

/-- interval body の translation。 -/
def affineConst {w : Word} (I : Interval w) : ℕ :=
  Word.affineConst I.body

/-- exact decomposition に沿った whole transfer の三分解。 -/
theorem whole_transfer_factorization
    {w : Word}
    (I : Interval w) :
    AffineTransfer.ofWord w =
      (AffineTransfer.ofWord I.left).followedBy
        ((AffineTransfer.ofWord I.body).followedBy
          (AffineTransfer.ofWord I.right)) := by
  simp only [I.decomp, List.append_assoc, AffineTransfer.ofWord_append]


/-- whole word が valid なら interval body も valid。 -/
theorem body_valid
    {w : Word}
    (I : Interval w)
    (hvalid : Word.Valid w) :
    Word.Valid I.body := by
  rw [I.decomp] at hvalid
  have hTail : Word.Valid (I.body ++ I.right) := by
    apply Word.Valid.suffix
      (u := I.left)
      (v := I.body ++ I.right)
    simpa [List.append_assoc] using hvalid
  exact hTail.prefix

/--
隣接する二つの body `u`, `v` を一つの interval として保持するための
lossless decomposition package。
-/
structure Split (whole : Word) where
  left : Word
  first : Word
  second : Word
  right : Word
  decomp : whole = left ++ first ++ second ++ right

namespace Split

/-- split の中央二区間を結合した transfer。 -/
def transfer {w : Word} (S : Split w) : AffineTransfer :=
  AffineTransfer.ofWord (S.first ++ S.second)

/-- split transfer は二つの interval transfer の composition。 -/
theorem transfer_eq_followedBy
    {w : Word}
    (S : Split w) :
    S.transfer =
      (AffineTransfer.ofWord S.first).followedBy
        (AffineTransfer.ofWord S.second) := by
  exact AffineTransfer.ofWord_append S.first S.second

/-- split decomposition に沿った whole transfer の四分解。 -/
theorem whole_transfer_factorization
    {w : Word}
    (S : Split w) :
    AffineTransfer.ofWord w =
      (AffineTransfer.ofWord S.left).followedBy
        ((AffineTransfer.ofWord S.first).followedBy
          ((AffineTransfer.ofWord S.second).followedBy
            (AffineTransfer.ofWord S.right))) := by
  simp only [S.decomp, List.append_assoc, AffineTransfer.ofWord_append]

end Split
end Interval
end Collatz2
