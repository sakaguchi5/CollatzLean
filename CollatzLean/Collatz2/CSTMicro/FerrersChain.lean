import CollatzLean.Collatz2.CSTMicro.SmallRepresentativeCarry

/-!
# General CST: Ferrers chains

first-passage binary word の Ferrers order を
adjacent cover `01 -> 10` の有限 chain として持つ。

任意の first-passage word から inversion number を下げる predecessor を
可能な限り辿り、first-passage predecessor を持たない minimal word を
Ferrers boundary と呼ぶ。

この定義は mechanical/Sturmian boundary の combinatorial minimality だけを
先に切り出したもので、boundary の明示式・一意性は後段へ残す。
-/

namespace Collatz2
namespace CSTMicro

/-- word 単体で書いた first-passage 条件。 -/
def IsFirstPassageWord (v : ParityWord) : Prop :=
  v ≠ [] ∧
    (∀ k : ℕ, 0 < k → k < v.length →
      CoefficientExpandingAt v k) ∧
    CoefficientContracting v

namespace FirstPassagePath

/-- structure から word-level first-passage packet を忘れる。 -/
theorem isFirstPassageWord (P : FirstPassagePath) :
    IsFirstPassageWord P.word := by
  exact ⟨P.nonempty, P.proper_expanding, P.terminal_contracting⟩

end FirstPassagePath

/-- word-level packet を `FirstPassagePath` に戻す。 -/
def firstPassagePathOfWord
    (v : ParityWord)
    (h : IsFirstPassageWord v) : FirstPassagePath :=
  { word := v
    nonempty := h.1
    proper_expanding := h.2.1
    terminal_contracting := h.2.2 }

/-- binary word の zero 数。 -/
def zeroCount : ParityWord → ℕ
  | [] => 0
  | false :: v => zeroCount v + 1
  | true :: v => zeroCount v

@[simp] theorem zeroCount_nil : zeroCount ([] : ParityWord) = 0 := rfl
@[simp] theorem zeroCount_false_cons (v : ParityWord) :
    zeroCount (false :: v) = zeroCount v + 1 := rfl
@[simp] theorem zeroCount_true_cons (v : ParityWord) :
    zeroCount (true :: v) = zeroCount v := rfl

/-- zero count の append formula。 -/
theorem zeroCount_append (u v : ParityWord) :
    zeroCount (u ++ v) = zeroCount u + zeroCount v := by
  induction u with
  | nil => simp [zeroCount]
  | cons b u ih =>
      cases b <;> simp [zeroCount, ih, Nat.add_assoc]
      ac_rfl

/--
Ferrers inversion number。

`true` の右にある `false` の組の総数。
`01 -> 10` 一回で exact に 1 増える。
-/
def ferrersInversion : ParityWord → ℕ
  | [] => 0
  | false :: v => ferrersInversion v
  | true :: v => zeroCount v + ferrersInversion v

/-- inversion number の append formula。 -/
theorem ferrersInversion_append (u v : ParityWord) :
    ferrersInversion (u ++ v) =
      ferrersInversion u + ferrersInversion v +
        oddCount u * zeroCount v := by
  induction u with
  | nil => simp [ferrersInversion, oddCount]
  | cons b u ih =>
      cases b
      · simp [ferrersInversion, oddCount, bitNat, ih]
      · simp [ferrersInversion, oddCount, bitNat, zeroCount_append, ih]
        ring

/-- two words が一つの adjacent Ferrers cover で結ばれる packet。 -/
structure FerrersStep (lower upper : ParityWord) where
  edge : AdjacentFerrersSwap
  lower_eq : lower = edge.lowerWord
  upper_eq : upper = edge.upperWord

namespace FerrersStep

/-- adjacent cover は length を保存する。 -/
theorem length_eq
    {lower upper : ParityWord}
    (S : FerrersStep lower upper) :
    lower.length = upper.length := by
  calc
    lower.length = S.edge.lowerWord.length :=
      congrArg List.length S.lower_eq
    _ = S.edge.upperWord.length := by
      rw [S.edge.lowerWord_length, S.edge.upperWord_length]
    _ = upper.length :=
      (congrArg List.length S.upper_eq).symm

/-- adjacent cover は endpoint odd count を保存する。 -/
theorem oddCount_eq
    {lower upper : ParityWord}
    (S : FerrersStep lower upper) :
    oddCount lower = oddCount upper := by
  calc
    oddCount lower = oddCount S.edge.lowerWord :=
      congrArg oddCount S.lower_eq
    _ = oddCount S.edge.upperWord := by
      rw [S.edge.lowerWord_oddCount, S.edge.upperWord_oddCount]
    _ = oddCount upper :=
      (congrArg oddCount S.upper_eq).symm

/-- `01 -> 10` は Ferrers inversion を exact に一つ増やす。 -/
theorem ferrersInversion_succ
    {lower upper : ParityWord}
    (S : FerrersStep lower upper) :
    ferrersInversion upper = ferrersInversion lower + 1 := by
  calc
    ferrersInversion upper =
        ferrersInversion S.edge.upperWord :=
      congrArg ferrersInversion S.upper_eq
    _ = ferrersInversion S.edge.lowerWord + 1 := by
      unfold AdjacentFerrersSwap.lowerWord AdjacentFerrersSwap.upperWord
      rw [ferrersInversion_append, ferrersInversion_append]
      rw [ferrersInversion_append, ferrersInversion_append]
      simp [ferrersInversion, zeroCount]
      ring
    _ = ferrersInversion lower + 1 := by
      rw [← congrArg ferrersInversion S.lower_eq]

end FerrersStep

/-- adjacent `01 -> 10` cover の有限列。 -/
inductive FerrersChain : ParityWord → ParityWord → Type
  | refl (v : ParityWord) : FerrersChain v v
  | step {u v w : ParityWord} :
      FerrersChain u v →
      FerrersStep v w →
      FerrersChain u w

namespace FerrersChain

/-- chain の先頭に一つ cover を付ける。 -/
def prepend
    {u v w : ParityWord}
    (S : FerrersStep u v)
    (C : FerrersChain v w) :
    FerrersChain u w :=
  match C with
  | .refl _ =>
      FerrersChain.step
        (FerrersChain.refl u)
        S
  | .step C T =>
      FerrersChain.step
        (prepend S C)
        T

end FerrersChain

/--
first-passage predecessor を持たない Ferrers-minimal path。

後段で mechanical/Sturmian boundary と同定するための pure combinatorial 定義。
-/
def IsFerrersBoundary (v : ParityWord) : Prop :=
  IsFirstPassageWord v ∧
    ∀ u : ParityWord, FerrersStep u v → ¬ IsFirstPassageWord u

/--
任意の first-passage word は、ある Ferrers boundary から
有限個の `01 -> 10` cover で到達できる。
-/
theorem exists_ferrersBoundary_chain
    {target : ParityWord}
    (hTarget : IsFirstPassageWord target) :
    ∃ boundary : ParityWord,
      IsFerrersBoundary boundary ∧
        Nonempty (FerrersChain boundary target) := by
  classical
  let Good : ℕ → Prop := fun n =>
    ∃ boundary : ParityWord,
      IsFirstPassageWord boundary ∧
        Nonempty (FerrersChain boundary target) ∧
        ferrersInversion boundary = n
  have hExists : ∃ n : ℕ, Good n := by
    refine ⟨ferrersInversion target, target, hTarget, ?_, rfl⟩
    exact ⟨FerrersChain.refl target⟩
  have hSpec := Nat.find_spec hExists
  rcases hSpec with ⟨boundary, hBoundaryFP, ⟨C⟩, hInv⟩
  refine ⟨boundary, ?_, ⟨C⟩⟩
  constructor
  · exact hBoundaryFP
  · intro lower S hLowerFP
    have C' : FerrersChain lower target :=
      FerrersChain.prepend S C
    have hGoodLower : Good (ferrersInversion lower) := by
      exact ⟨lower, hLowerFP, ⟨C'⟩, rfl⟩
    have hMin : Nat.find hExists ≤ ferrersInversion lower :=
      Nat.find_min' hExists hGoodLower
    have hStep := S.ferrersInversion_succ
    omega

end CSTMicro
end Collatz2
