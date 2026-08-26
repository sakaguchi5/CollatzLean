import CollatzLean.Collatz2.RecordFerrers.Lattice.AffineValuationTransport
import Mathlib.Combinatorics.SetFamily.FourFunctions
import Mathlib.Data.Fintype.Basic

/-!
# Record–Ferrers RF-D1: 有限分配束上の四関数定理と正相関制約

このファイルでは Mathlib に既にある四関数定理・Daykin 不等式・FKG 不等式を、
Record–Ferrers の Ferrers 束へ接続する。

目的は確率論を導入すること自体ではない。
複数の候補図形を同時に許すとき、meet / join によって生成される候補族の大きさや、
単調な二つの量の同時発生が独立には選べないことを、後段の矛盾証明で使える形にする。

ここでは次を用意する。

* 任意の Ferrers 図形族に対する四関数定理の直接ラッパー
* Daykin の濃度不等式
* critical roof 以下であることが meet / join 生成族へ保存されること
* 有限かつ meet / join で閉じた critical family を有限分配束として読む構造
* その有限分配束上の FKG 不等式

英語名は Mathlib の既存定理名・API 名として必要な箇所だけ残し、説明は日本語を主にする。
-/

namespace Collatz2
namespace RecordFerrers

open Word
open scoped FinsetFamily

namespace FerrersShape

/--
有限図形族を `Finset` として扱うための判定可能な等号。
数学的な新情報ではなく、有限集合 API を使うための実装上の入口である。
-/
noncomputable instance instDecidableEqRF (p : ℕ) : DecidableEq (FerrersShape p) :=
  Classical.decEq _

end FerrersShape

/--
Ferrers 分配束に Mathlib の四関数定理をそのまま適用する。

各二図形 `A,B` に対する局所的な積不等式が分かれば、
二つの有限候補族全体の和に対する積不等式へ持ち上がる。
-/
theorem ferrers_fourFunctions_nat
    {p : ℕ}
    (f₁ f₂ f₃ f₄ : FerrersShape p → ℕ)
    (hLocal :
      ∀ A B : FerrersShape p,
        f₁ A * f₂ B ≤ f₃ (A ⊓ B) * f₄ (A ⊔ B))
    (s t : Finset (FerrersShape p)) :
    (∑ A ∈ s, f₁ A) * (∑ B ∈ t, f₂ B) ≤
      (∑ C ∈ s ⊼ t, f₃ C) * (∑ D ∈ s ⊻ t, f₄ D) := by
  classical
  exact
    four_functions_theorem f₁ f₂ f₃ f₄
      (fun _ => Nat.zero_le _)
      (fun _ => Nat.zero_le _)
      (fun _ => Nat.zero_le _)
      (fun _ => Nat.zero_le _)
      hLocal s t

/--
二つの Ferrers 図形族の大きさは、meet 生成族と join 生成族の大きさにより制約される。

`|s| |t| ≤ |s ⊼ t| |s ⊻ t|`

これは Daykin の濃度不等式を Record–Ferrers 束へ直接適用したもの。
-/
theorem ferrers_daykin_card_product
    {p : ℕ}
    (s t : Finset (FerrersShape p)) :
    s.card * t.card ≤ (s ⊼ t).card * (s ⊻ t).card := by
  classical
  exact Finset.le_card_infs_mul_card_sups s t

/--
左側の候補族が critical roof 以下なら、
任意の右側候補族との meet で生成した族も critical roof 以下。

meet は左 operand 以下なので、右側候補族の criticality は不要。
-/
theorem criticalFamily_infs_below
    {p : ℕ}
    {s t : Finset (FerrersShape p)}
    (hs : ∀ A ∈ s, IsCriticalSubshape A) :
    ∀ C ∈ s ⊼ t, IsCriticalSubshape C := by
  intro C hC
  rcases Finset.mem_infs.mp hC with ⟨A, hA, B, hB, rfl⟩
  have hInf :
      A ⊓ B = A.meet B := by
    apply FerrersShape.ext
    intro i
    rfl
  rw [hInf]
  exact criticalSubshape_meet (hs A hA)

/--
二つの候補族がともに critical roof 以下なら、join で生成した族も critical roof 以下。
-/
theorem criticalFamily_sups_below
    {p : ℕ}
    {s t : Finset (FerrersShape p)}
    (hs : ∀ A ∈ s, IsCriticalSubshape A)
    (ht : ∀ B ∈ t, IsCriticalSubshape B) :
    ∀ C ∈ s ⊻ t, IsCriticalSubshape C := by
  intro C hC
  rcases Finset.mem_sups.mp hC with ⟨A, hA, B, hB, rfl⟩
  have hSup :
      A ⊔ B = A.join B := by
    apply FerrersShape.ext
    intro i
    rfl
  rw [hSup]
  exact criticalSubshape_join (hs A hA) (ht B hB)

/--
critical roof 以下にある有限 Ferrers 図形族で、meet / join に閉じているもの。

この構造を一つ与えると、その要素型自身を有限分配束として扱える。
FKG を適用するための局所的な受け皿であり、全 critical subshape 空間を
毎回完全列挙することは要求しない。
-/
structure FiniteCriticalSublattice (p : ℕ) where
  carrier : Finset (FerrersShape p)
  belowCritical : ∀ A ∈ carrier, IsCriticalSubshape A
  inf_mem : ∀ A ∈ carrier, ∀ B ∈ carrier, A ⊓ B ∈ carrier
  sup_mem : ∀ A ∈ carrier, ∀ B ∈ carrier, A ⊔ B ∈ carrier

namespace FiniteCriticalSublattice

/-- 有限 critical family の一点。 -/
abbrev Point
    {p : ℕ}
    (F : FiniteCriticalSublattice p) :=
  {A : FerrersShape p // A ∈ F.carrier}

/-- carrier 自体が列挙表なので、その要素型は有限。 -/
noncomputable instance instFintypePoint
    {p : ℕ}
    (F : FiniteCriticalSublattice p) : Fintype F.Point :=
  Fintype.subtype F.carrier (by
    intro A
    rfl)

/-- meet / join 閉性から、有限 family の要素型にも lattice 構造を入れる。 -/
instance instLatticePoint
    {p : ℕ}
    (F : FiniteCriticalSublattice p) : Lattice F.Point where
  sup A B := ⟨A.1 ⊔ B.1, F.sup_mem A.1 A.2 B.1 B.2⟩
  le_sup_left := by
    intro A B
    change A.1 ≤ A.1 ⊔ B.1
    exact le_sup_left
  le_sup_right := by
    intro A B
    change B.1 ≤ A.1 ⊔ B.1
    exact le_sup_right
  sup_le := by
    intro A B C hAC hBC
    change A.1 ⊔ B.1 ≤ C.1
    exact sup_le hAC hBC
  inf A B := ⟨A.1 ⊓ B.1, F.inf_mem A.1 A.2 B.1 B.2⟩
  inf_le_left := by
    intro A B
    change A.1 ⊓ B.1 ≤ A.1
    exact inf_le_left
  inf_le_right := by
    intro A B
    change A.1 ⊓ B.1 ≤ B.1
    exact inf_le_right
  le_inf := by
    intro A B C hAB hAC
    change A.1 ≤ B.1 ⊓ C.1
    exact le_inf hAB hAC

/-- 元の Ferrers 束が分配的なので、閉部分族も分配束。 -/
instance instDistribLatticePoint
    {p : ℕ}
    (F : FiniteCriticalSublattice p) : DistribLattice F.Point where
  le_sup_inf := by
    intro A B C
    change
      (A.1 ⊔ B.1) ⊓ (A.1 ⊔ C.1) ≤
        A.1 ⊔ (B.1 ⊓ C.1)
    exact le_sup_inf

@[simp] theorem coe_inf
    {p : ℕ}
    (F : FiniteCriticalSublattice p)
    (A B : F.Point) :
    ((A ⊓ B : F.Point) : FerrersShape p) = A.1 ⊓ B.1 := rfl

@[simp] theorem coe_sup
    {p : ℕ}
    (F : FiniteCriticalSublattice p)
    (A B : F.Point) :
    ((A ⊔ B : F.Point) : FerrersShape p) = A.1 ⊔ B.1 := rfl

/--
有限 critical sublattice 上の FKG 不等式。

`f,g` が Ferrers 順序に沿って単調増加し、重み `μ` が meet / join に対して
対数的な超モジュラー条件を満たすなら、二つの量の重み付き同時発生には
正相関型の下限制約が入る。

この定理は一本の軌道を直接排除するものではない。
後段で「悪い軌道仮定がこの有限候補族を強制する」という橋と組み合わせる。
-/
theorem fkg_nat
    {p : ℕ}
    (F : FiniteCriticalSublattice p)
    (f g μ : F.Point → ℕ)
    (hf : Monotone f)
    (hg : Monotone g)
    (hμ :
      ∀ A B : F.Point,
        μ A * μ B ≤ μ (A ⊓ B) * μ (A ⊔ B)) :
    (∑ A : F.Point, μ A * f A) *
        (∑ A : F.Point, μ A * g A) ≤
      (∑ A : F.Point, μ A) *
        (∑ A : F.Point, μ A * (f A * g A)) := by
  classical
  exact
    fkg f g μ
      (fun _ => Nat.zero_le _)
      (fun _ => Nat.zero_le _)
      (fun _ => Nat.zero_le _)
      hf hg hμ

end FiniteCriticalSublattice

end RecordFerrers
end Collatz2
