import CollatzLean.Collatz2.RecordFerrers.Counting.EhrhartCounting

/-!
# Record–Ferrers RF-D3: 候補族全体に対する容量矛盾

D1 の四関数定理 / FKG と D2 の格子点計数を、
「悪い軌道仮定が多数の相異なる Record–Ferrers 候補を強制する」場合に使える
矛盾証明書へまとめる。

ここでは Collatz 固有の発散仮定そのものは import しない。
上位の Synthesis / Macro 層が

* 候補状態から critical Ferrers shape への単射
* 二つの候補族が十分大きいこと
* meet / join 生成族が別の算術条件により十分小さいこと
* FKG と逆向きの strict inequality

のいずれかを供給すれば、このファイルの定理だけで `False` まで閉じられる。

つまり D3 は「集合を数えた」という事実ではなく、
その数え上げを実際の軌道仮定の不存在へ戻すための family-level obstruction 層である。
-/

namespace Collatz2
namespace RecordFerrers

open Word
open scoped FinsetFamily

/--
ある元の候補状態型 `α` を critical Ferrers 図形へ情報損失なく送る証明書。
開始値や数値軌道全体の復元は要求しない。
この候補族を区別する目的に対して単射であり、全像が critical roof 以下なら十分。
-/
structure FamilyEncodingCertificate
    (α : Type*)
    (p : ℕ) where
  encode : α → FerrersShape p
  injective : Function.Injective encode
  belowCritical : ∀ x : α, IsCriticalSubshape (encode x)

namespace FamilyEncodingCertificate

/--
元の候補を RF-B4 の臨界上限制約つき整数点へ送る。
Ferrers shape から累積整数座標への exact 変換だけを使う。
-/
def toPrefixPoint
    {α : Type*}
    {p : ℕ}
    (E : FamilyEncodingCertificate α p)
    (x : α) : PrefixPolytopePoint p :=
  { coordinates := (E.encode x).toPrefixCoordinates
    belowCritical := by
      intro i
      simpa [criticalShape] using E.belowCritical x i }

/-- 元の候補を整数点へ送っても単射性は失われない。 -/
theorem toPrefixPoint_injective
    {α : Type*}
    {p : ℕ}
    (E : FamilyEncodingCertificate α p) :
    Function.Injective E.toPrefixPoint := by
  intro x y hxy
  apply E.injective
  apply FerrersShape.ext
  intro i
  have hCoord :=
    congrArg
      (fun P : PrefixPolytopePoint p => P.coordinates.cumulative i)
      hxy
  exact hCoord

/-- 有限な元候補族を Ferrers 図形族へ写す。 -/
noncomputable def shapeFamily
    {α : Type*}
    {p : ℕ}
    [DecidableEq α]
    (E : FamilyEncodingCertificate α p)
    (s : Finset α) : Finset (FerrersShape p) :=
  s.image E.encode

/-- 単射符号化なので候補族の個数は Ferrers 側で exact に保存される。 -/
theorem card_shapeFamily
    {α : Type*}
    {p : ℕ}
    [DecidableEq α]
    (E : FamilyEncodingCertificate α p)
    (s : Finset α) :
    (E.shapeFamily s).card = s.card := by
  classical
  simpa [shapeFamily] using
    Finset.card_image_of_injective s E.injective

/-- 符号化された有限候補族は全て critical roof 以下に残る。 -/
theorem shapeFamily_belowCritical
    {α : Type*}
    {p : ℕ}
    [DecidableEq α]
    (E : FamilyEncodingCertificate α p)
    (s : Finset α) :
    ∀ A ∈ E.shapeFamily s, IsCriticalSubshape A := by
  classical
  intro A hA
  rcases Finset.mem_image.mp hA with ⟨x, hx, rfl⟩
  exact E.belowCritical x

/--
倍率 1 の universal FirstCrossing 格子点数は、
この単射符号化で区別される任意の有限候補族の容量上限になる。
-/
theorem card_le_ehrhartCount_one
    {α : Type*}
    {p : ℕ}
    (E : FamilyEncodingCertificate α p)
    (s : Finset α) :
    s.card ≤ ehrhartCount p 1 := by
  classical
  calc
    s.card = (s.image E.toPrefixPoint).card := by
      symm
      exact Finset.card_image_of_injective s E.toPrefixPoint_injective
    _ ≤ Fintype.card (PrefixPolytopePoint p) :=
      Finset.card_le_univ _
    _ = ehrhartCount p 1 :=
      (ehrhartCount_one p).symm

/--
悪い軌道仮定などが `ehrhartCount p 1` より多くの相異なる候補を強制したなら即矛盾。

これは「状態空間の容量不足」を元の候補型へ戻す最小形。
-/
theorem impossible_of_card_gt_ehrhartCount_one
    {α : Type*}
    {p : ℕ}
    (E : FamilyEncodingCertificate α p)
    (s : Finset α)
    (hTooMany : ehrhartCount p 1 < s.card) :
    False := by
  exact (not_lt_of_ge (E.card_le_ehrhartCount_one s)) hTooMany

/--
Daykin 不等式を使う family-level 容量矛盾。

二つの元候補族 `s,t` を Ferrers 側へ単射で移し、
算術側などから meet 生成族と join 生成族の容量上限 `infCap,supCap` が得られたとする。
その積が元候補族の積より小さければ、分配束の既存定理と矛盾する。
-/
theorem impossible_of_daykin_capacity
    {α : Type*}
    {p : ℕ}
    [DecidableEq α]
    (E : FamilyEncodingCertificate α p)
    (s t : Finset α)
    (infCap supCap : ℕ)
    (hInf :
      ((E.shapeFamily s) ⊼ (E.shapeFamily t)).card ≤ infCap)
    (hSup :
      ((E.shapeFamily s) ⊻ (E.shapeFamily t)).card ≤ supCap)
    (hStrict : infCap * supCap < s.card * t.card) :
    False := by
  classical
  have hDaykin :=
    ferrers_daykin_card_product (E.shapeFamily s) (E.shapeFamily t)
  rw [E.card_shapeFamily s, E.card_shapeFamily t] at hDaykin
  have hUpper :
      ((E.shapeFamily s) ⊼ (E.shapeFamily t)).card *
          ((E.shapeFamily s) ⊻ (E.shapeFamily t)).card ≤
        infCap * supCap :=
    Nat.mul_le_mul hInf hSup
  have hTotal : s.card * t.card ≤ infCap * supCap :=
    hDaykin.trans hUpper
  exact (not_lt_of_ge hTotal) hStrict

end FamilyEncodingCertificate

/--
FKG が要求する正相関型不等式と strict に逆向きの評価が別の理論から出た場合の矛盾。

この形なら上位の Collatz / macro 層は、有限 closed family と三つの重み関数を構成し、
最後の strict inequality だけを示せばよい。
-/
theorem impossible_of_fkg_reverse
    {p : ℕ}
    (F : FiniteCriticalSublattice p)
    (f g μ : F.Point → ℕ)
    (hf : Monotone f)
    (hg : Monotone g)
    (hμ :
      ∀ A B : F.Point,
        μ A * μ B ≤ μ (A ⊓ B) * μ (A ⊔ B))
    (hReverse :
      (∑ A : F.Point, μ A) *
          (∑ A : F.Point, μ A * (f A * g A)) <
        (∑ A : F.Point, μ A * f A) *
          (∑ A : F.Point, μ A * g A)) :
    False := by
  classical
  have hFKG := F.fkg_nat f g μ hf hg hμ
  exact (not_lt_of_ge hFKG) hReverse

end RecordFerrers
end Collatz2
