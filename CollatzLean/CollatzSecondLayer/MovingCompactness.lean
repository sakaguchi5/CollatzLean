import CollatzLean.CollatzSecondLayer.FutureMinimum

/-!
# moving-anchorの2進コンパクト化

固定自然数anchorを仮定せず、future-minimum部分列から
整合する2進剰余系と固定極限指数語を保持するためのデータ型を定義する。
-/

namespace CollatzSecondLayer

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

/-- 無限指数列 `E` の先頭 `m` 文字。 -/
def prefixWord (E : ℕ → ℕ) : ℕ → ExpWord
  | 0 => []
  | m + 1 => E 0 :: prefixWord (fun n => E (n + 1)) m

@[simp] theorem prefixWord_zero (E : ℕ → ℕ) :
    prefixWord E 0 = [] := rfl

@[simp] theorem prefixWord_succ (E : ℕ → ℕ) (m : ℕ) :
    prefixWord E (m + 1) =
      E 0 :: prefixWord (fun n => E (n + 1)) m := rfl

@[simp] theorem prefixWord_length (E : ℕ → ℕ) (m : ℕ) :
    (prefixWord E m).length = m := by
  induction m generalizing E with
  | zero => rfl
  | succ m ih =>
      simp [prefixWord, ih]

/-- 長い極限prefixの先頭を取ると短い極限prefixになる。 -/
theorem prefixWord_take_of_le (E : ℕ → ℕ)
    {m n : ℕ} (h : m ≤ n) :
    (prefixWord E n).take m = prefixWord E m := by
  induction m generalizing E n with
  | zero => simp
  | succ m ih =>
      cases n with
      | zero => omega
      | succ n =>
          simp only [prefixWord_succ, List.take_succ_cons]
          rw [ih (E := fun k => E (k + 1)) (n := n) (by omega)]

/-- 正の無限指数列の有限prefixは有効語である。 -/
theorem prefixWord_valid
    {E : ℕ → ℕ} (hE : ∀ n, 0 < E n) (m : ℕ) :
    Valid (prefixWord E m) := by
  induction m generalizing E with
  | zero => simp [Valid]
  | succ m ih =>
      intro e he
      simp only [prefixWord_succ, List.mem_cons] at he
      rcases he with rfl | he
      · exact hE 0
      · exact ih (E := fun n => E (n + 1))
          (fun n => hE (n + 1)) e he

/-- `Z₂` の元を、互いに整合する有限剰余の塔だけで表す。 -/
structure CoherentTwoAdicShadow where
  residue : ℕ → ℕ
  residue_lt : ∀ r, residue r < 2 ^ r
  compatible : ∀ r,
    residue (r + 1) % 2 ^ r = residue r

/-- moving anchor列が整合剰余系へ2進収束すること。 -/
def ConvergesToShadow
    (a : ℕ → ℕ) (ξ : CoherentTwoAdicShadow) : Prop :=
  ∀ r : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
    a j % 2 ^ r = ξ.residue r

/--
一般のmoving-anchor解析で固定するデータ。
`prefix_stabilizes` は、各固定長で指数語が最終的に同一になることを表す。
-/
structure MovingLimitData (O : OddOrbit) where
  minima : O.FutureMinimumSequence
  shadow : CoherentTwoAdicShadow
  shadow_convergence :
    ConvergesToShadow
      (fun j => O.value (minima.index j)) shadow
  limitExponent : ℕ → ℕ
  limitExponent_pos : ∀ n, 0 < limitExponent n
  prefix_stabilizes :
    ∀ m : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      O.segmentWord (minima.index j) m =
        prefixWord limitExponent m

namespace MovingLimitData

/-- 極限指数語の長さ `m` のprefix。 -/
def limitWord {O : OddOrbit} (D : MovingLimitData O) (m : ℕ) : ExpWord :=
  prefixWord D.limitExponent m

@[simp] theorem limitWord_length {O : OddOrbit}
    (D : MovingLimitData O) (m : ℕ) :
    (D.limitWord m).length = m := by
  simp [limitWord]

/-- 極限指数語の有限prefixは有効である。 -/
theorem limitWord_valid {O : OddOrbit}
    (D : MovingLimitData O) (m : ℕ) :
    Valid (D.limitWord m) := by
  exact prefixWord_valid D.limitExponent_pos m

end MovingLimitData

/--
任意の非有界軌道からmoving-limitデータを抽出できる、という上流接続命題。
このファイルでは仮定として隠さず、後続の還元定理へ明示的に渡す。
-/
def MovingCompactnessPrinciple : Prop :=
  ∀ O : OddOrbit, O.Unbounded → Nonempty (MovingLimitData O)

end CollatzSecondLayer
