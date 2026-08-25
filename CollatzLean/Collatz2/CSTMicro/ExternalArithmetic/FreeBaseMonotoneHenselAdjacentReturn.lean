import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.FreeBaseMonotoneHenselLeftExtension

/-!
# Free-base Hensel repeat: maximal-left stop から adjacent left-special return へ

このファイルでは、absolute exponent の baseline を捨てて
「同じ relative delta factor が別の位置に出現する」という pure combinatorial object を作る。

元の repeated block が左へ maximal に延長され、そこで predecessor offset が壊れるなら、
同じ factor の二つの occurrence は異なる predecessor signature を持つ。
その二点の間に occurrence があれば、predecessor signature が変わる側へ区間を縮める。
有限回の strong induction により、間に同じ factor の occurrence を一つも持たない
adjacent pair が得られる。

この adjacent pair が後段の Sturmian return-word 正規化の pure arithmetic 受け皿である。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

namespace FreeBaseMonotoneHenselChain

/--
`anchor` と `pos` から始まる長さ `N` の delta profile が、baseline の違いを除いて同じこと。

  delta(pos) + delta(anchor+r)
    = delta(anchor) + delta(pos+r)

を `0 ≤ r ≤ N` で要求する。
-/
def SameRelativeDeltaBlock
    (C : FreeBaseMonotoneHenselChain)
    (anchor pos N : ℕ) : Prop :=
  ∀ r : ℕ, r ≤ N →
    C.delta pos + C.delta (anchor + r) =
      C.delta anchor + C.delta (pos + r)

/-- relative delta block は自分自身に対して成立する。 -/
theorem sameRelativeDeltaBlock_refl
    (C : FreeBaseMonotoneHenselChain)
    (anchor N : ℕ) :
    C.SameRelativeDeltaBlock anchor anchor N := by
  intro r hr
  omega

/--
一定 offset の repeated block は baseline-free な relative delta block を与える。
-/
theorem sameRelativeDeltaBlock_of_sameDeltaOffsetBlock
    (C : FreeBaseMonotoneHenselChain)
    {anchor pos N Delta : ℕ}
    (hBlock : C.SameDeltaOffsetBlock anchor pos N Delta) :
    C.SameRelativeDeltaBlock anchor pos N := by
  intro r hr
  have hZero := hBlock 0 (Nat.zero_le N)
  have hR := hBlock r hr
  simp only [Nat.add_zero] at hZero
  omega

/--
同じ anchor factor の二つの occurrence は、互いにも同じ relative delta block を持つ。
-/
theorem sameRelativeDeltaBlock_pair
    (C : FreeBaseMonotoneHenselChain)
    {anchor x y N : ℕ}
    (hX : C.SameRelativeDeltaBlock anchor x N)
    (hY : C.SameRelativeDeltaBlock anchor y N) :
    C.SameRelativeDeltaBlock x y N := by
  intro r hr
  have hx := hX r hr
  have hy := hY r hr
  omega

/--
relative delta block と start の単調性から、実際の constant offset block を復元する。
-/
theorem sameDeltaOffsetBlock_of_sameRelativeDeltaBlock
    (C : FreeBaseMonotoneHenselChain)
    {x y N : ℕ}
    (hxy : x ≤ y)
    (hy : y < C.width)
    (hRel : C.SameRelativeDeltaBlock x y N) :
    let Delta := C.delta y - C.delta x
    C.SameDeltaOffsetBlock x y N Delta := by
  dsimp
  have hMono : C.delta x ≤ C.delta y :=
    C.delta_mono_of_le hxy hy
  intro r hr
  have hR := hRel r hr
  omega

/--
位置 `k` の直前一歩を baseline-free に記録する整数 signature。
straight corridor 内では 0 または -1 になるが、adjacency 抽出にはその二値性を使わない。
-/
def predecessorSignature
    (C : FreeBaseMonotoneHenselChain)
    (k : ℕ) : ℤ :=
  (C.delta (k - 1) : ℤ) - (C.delta k : ℤ)

/--
現在位置で同じ offset を持つ二 occurrence が一セル左へ延長できないなら、
predecessor signature は異なる。
-/
theorem predecessorSignature_ne_of_not_leftExtendable
    (C : FreeBaseMonotoneHenselChain)
    {i j Delta : ℕ}
    (hDelta : C.delta j = C.delta i + Delta)
    (hStop : C.delta (j - 1) ≠ C.delta (i - 1) + Delta) :
    C.predecessorSignature i ≠ C.predecessorSignature j := by
  intro hSig
  unfold predecessorSignature at hSig
  have hDeltaZ :
      (C.delta j : ℤ) =
        (C.delta i : ℤ) + (Delta : ℤ) := by
    exact_mod_cast hDelta
  have hPredZ :
      (C.delta (j - 1) : ℤ) =
        (C.delta (i - 1) : ℤ) + (Delta : ℤ) := by
    linarith
  have hPred :
      C.delta (j - 1) = C.delta (i - 1) + Delta := by
    exact_mod_cast hPredZ
  exact hStop hPred

/--
逆に predecessor signature が異なれば、現在の offset を一セル左へ延長できない。
-/
theorem not_leftExtendable_of_predecessorSignature_ne
    (C : FreeBaseMonotoneHenselChain)
    {i j Delta : ℕ}
    (hDelta : C.delta j = C.delta i + Delta)
    (hSig : C.predecessorSignature i ≠ C.predecessorSignature j) :
    C.delta (j - 1) ≠ C.delta (i - 1) + Delta := by
  intro hPred
  apply hSig
  unfold predecessorSignature
  have hDeltaZ :
      (C.delta j : ℤ) =
        (C.delta i : ℤ) + (Delta : ℤ) := by
    exact_mod_cast hDelta
  have hPredZ :
      (C.delta (j - 1) : ℤ) =
        (C.delta (i - 1) : ℤ) + (Delta : ℤ) := by
    exact_mod_cast hPred
  linarith

/--
二端点で mark が異なる occurrence 区間には、mark が異なる adjacent occurrence pair がある。
ここで adjacent とは、その二点の strict 間に `Occ` が一つも無いこと。

Sturmian theory に依存しない有限順序の純粋補題。
-/
private theorem exists_adjacent_occurrences_of_endpoint_mark_ne
    (Occ : ℕ → Prop)
    (mark : ℕ → ℤ)
    {a b : ℕ}
    (hab : a < b)
    (ha : Occ a)
    (hb : Occ b)
    (hmark : mark a ≠ mark b) :
    ∃ x y : ℕ,
      a ≤ x ∧
      x < y ∧
      y ≤ b ∧
      Occ x ∧
      Occ y ∧
      mark x ≠ mark y ∧
      (∀ z : ℕ, x < z → z < y → ¬ Occ z) := by
  classical
  let Good : ℕ → Prop := fun d =>
    ∀ a b : ℕ,
      b - a = d →
      a < b →
      Occ a →
      Occ b →
      mark a ≠ mark b →
      ∃ x y : ℕ,
        a ≤ x ∧
        x < y ∧
        y ≤ b ∧
        Occ x ∧
        Occ y ∧
        mark x ≠ mark y ∧
        (∀ z : ℕ, x < z → z < y → ¬ Occ z)
  have hGood : ∀ d : ℕ, Good d := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        dsimp [Good]
        intro a b hdist hab ha hb hmark
        by_cases hMid : ∃ z : ℕ, a < z ∧ z < b ∧ Occ z
        · rcases hMid with ⟨z, haz, hzb, hzOcc⟩
          by_cases hAZ : mark a = mark z
          · have hzB : mark z ≠ mark b := by
              intro hZB
              apply hmark
              exact hAZ.trans hZB
            have hSmall : b - z < d := by omega
            have hRec := ih (b - z) hSmall
            dsimp [Good] at hRec
            rcases hRec z b rfl hzb hzOcc hb hzB with
              ⟨x, y, hzx, hxy, hyb, hxOcc, hyOcc, hxyMark, hNoMid⟩
            exact
              ⟨x, y, by omega, hxy, hyb,
                hxOcc, hyOcc, hxyMark, hNoMid⟩
          · have hSmall : z - a < d := by omega
            have hRec := ih (z - a) hSmall
            dsimp [Good] at hRec
            rcases hRec a z rfl haz ha hzOcc hAZ with
              ⟨x, y, hax, hxy, hyz, hxOcc, hyOcc, hxyMark, hNoMid⟩
            exact
              ⟨x, y, hax, hxy, by omega,
                hxOcc, hyOcc, hxyMark, hNoMid⟩
        · refine ⟨a, b, le_rfl, hab, le_rfl, ha, hb, hmark, ?_⟩
          intro z haz hzb hzOcc
          exact hMid ⟨z, haz, hzb, hzOcc⟩
  have h := hGood (b - a)
  dsimp [Good] at h
  exact h a b rfl hab ha hb hmark

/--
maximal-left stopped repeat から取り出す adjacent left-special return packet。

`anchor` で指定した同一 factor の二 occurrence `left < right` を持ち、
その間に同じ factor の occurrence は無い。
さらに pair 自身は constant delta offset block で、predecessor ではその offset が壊れる。
-/
structure AdjacentLeftSpecialReturn
    (C : FreeBaseMonotoneHenselChain)
    (anchor N : ℕ) where
  left : ℕ
  right : ℕ
  Delta : ℕ
  anchor_le_left : anchor ≤ left
  left_lt_right : left < right
  right_add_len_lt_width : right + N < C.width
  left_occurs : C.SameRelativeDeltaBlock anchor left N
  right_occurs : C.SameRelativeDeltaBlock anchor right N
  block : C.SameDeltaOffsetBlock left right N Delta
  noLeftExtension : C.delta (right - 1) ≠ C.delta (left - 1) + Delta
  noOccurrenceBetween :
    ∀ z : ℕ,
      left < z → z < right →
      ¬ C.SameRelativeDeltaBlock anchor z N

/--
左へ maximal に延長した repeated block が入口より手前で停止したときの pure normal form。

仮定 `hStop` は maximality の一セル版である。
結論は、同じ relative factor の adjacent occurrence pair で、
その pair も左へ一セル延長できないという return packet。
-/
theorem maximalLeftStoppedRepeat_gives_adjacentLeftSpecialReturn
    (C : FreeBaseMonotoneHenselChain)
    {a b N Delta : ℕ}
    (hab : a < b)
    (hbEnd : b + N < C.width)
    (hBlock : C.SameDeltaOffsetBlock a b N Delta)
    (hStop : C.delta (b - 1) ≠ C.delta (a - 1) + Delta) :
    ∃ R : C.AdjacentLeftSpecialReturn a N,
      R.right ≤ b := by
  have hOccA : C.SameRelativeDeltaBlock a a N :=
    C.sameRelativeDeltaBlock_refl a N
  have hOccB : C.SameRelativeDeltaBlock a b N :=
    C.sameRelativeDeltaBlock_of_sameDeltaOffsetBlock hBlock
  have hDeltaAB : C.delta b = C.delta a + Delta := by
    have h := hBlock 0 (Nat.zero_le N)
    simpa using h
  have hSigAB : C.predecessorSignature a ≠ C.predecessorSignature b :=
    C.predecessorSignature_ne_of_not_leftExtendable hDeltaAB hStop
  rcases
      exists_adjacent_occurrences_of_endpoint_mark_ne
        (Occ := fun z => C.SameRelativeDeltaBlock a z N)
        (mark := C.predecessorSignature)
        hab hOccA hOccB hSigAB with
    ⟨x, y, hax, hxy, hyb, hOccX, hOccY, hSigXY, hNoMid⟩
  have hyWidth : y < C.width := by omega
  have hyEnd : y + N < C.width := by omega
  have hPairRel : C.SameRelativeDeltaBlock x y N :=
    C.sameRelativeDeltaBlock_pair hOccX hOccY
  let DeltaXY := C.delta y - C.delta x
  have hPairBlock : C.SameDeltaOffsetBlock x y N DeltaXY := by
    simpa [DeltaXY] using
      (C.sameDeltaOffsetBlock_of_sameRelativeDeltaBlock
        (Nat.le_of_lt hxy) hyWidth hPairRel)
  have hDeltaXY : C.delta y = C.delta x + DeltaXY := by
    have h := hPairBlock 0 (Nat.zero_le N)
    simpa using h
  have hNoLeftXY :
      C.delta (y - 1) ≠ C.delta (x - 1) + DeltaXY :=
    C.not_leftExtendable_of_predecessorSignature_ne hDeltaXY hSigXY
  let R : C.AdjacentLeftSpecialReturn a N :=
    { left := x
      right := y
      Delta := DeltaXY
      anchor_le_left := hax
      left_lt_right := hxy
      right_add_len_lt_width := hyEnd
      left_occurs := hOccX
      right_occurs := hOccY
      block := hPairBlock
      noLeftExtension := hNoLeftXY
      noOccurrenceBetween := hNoMid }
  exact ⟨R, hyb⟩

end FreeBaseMonotoneHenselChain

end ExternalArithmetic
end CSTMicro
end Collatz2
