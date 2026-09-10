import CollatzLean.Collatz3.Experimental2.MechanicalConvergentCorridorSharp

/-!
# Collatz3 Experimental2: inverse corridor の有限 exact 合成

一つの corridor translation

`H(Q+k) = P + H(k)`

を二段、三段、任意有限段へ合成する。

ここでは continued fraction や Ostrowski digit を data として保存しない。
各段で本当に必要な exact translation だけを再帰的に要求する
`ExactInverseCorridorChain` を薄い述語として置く。

この層の重要な点は、途中の corridor orientation の endpoint correction が
scalar height には現れないことである。残差が正の間は通常 translation だけが使われ、
補正は最後に residual `0` へ着地する endpoint で一度だけ現れる。
-/

namespace Collatz3
namespace Experimental2

/-- corridor 列の横方向 `P` の総和。 -/
def corridorPSum : List (ℕ × ℕ) → ℕ
  | [] => 0
  | (P, _Q) :: xs => P + corridorPSum xs

/-- corridor 列の高さ方向 `Q` の総和。 -/
def corridorQSum : List (ℕ × ℕ) → ℕ
  | [] => 0
  | (_P, Q) :: xs => Q + corridorQSum xs

@[simp] theorem corridorPSum_nil : corridorPSum [] = 0 := rfl
@[simp] theorem corridorQSum_nil : corridorQSum [] = 0 := rfl

@[simp] theorem corridorPSum_cons
    (P Q : ℕ) (xs : List (ℕ × ℕ)) :
    corridorPSum ((P, Q) :: xs) = P + corridorPSum xs := rfl

@[simp] theorem corridorQSum_cons
    (P Q : ℕ) (xs : List (ℕ × ℕ)) :
    corridorQSum ((P, Q) :: xs) = Q + corridorQSum xs := rfl

/-- `P` 総和は list append に対して加法的。 -/
theorem corridorPSum_append :
    ∀ xs ys : List (ℕ × ℕ),
      corridorPSum (xs ++ ys) = corridorPSum xs + corridorPSum ys
  | [], ys => by simp
  | (P, Q) :: xs, ys => by
      simp [corridorPSum, corridorPSum_append xs ys, Nat.add_assoc]

/-- `Q` 総和も list append に対して加法的。 -/
theorem corridorQSum_append :
    ∀ xs ys : List (ℕ × ℕ),
      corridorQSum (xs ++ ys) = corridorQSum xs + corridorQSum ys
  | [], ys => by simp
  | (P, Q) :: xs, ys => by
      simp [corridorQSum, corridorQSum_append xs ys, Nat.add_assoc]

/--
残差 `k` に向かって順に exact translation を適用できる有限 corridor 列。

head `(P,Q)` では、tail 全体の `Q` 総和と最終 residual `k` を合わせた量を
positive residual として読み、次の translation を一つだけ要求する。
新しい幾何 data は保存せず、必要な等式だけを certificate とする。
-/
def ExactInverseCorridorChain
    (H : ℕ → ℕ) : List (ℕ × ℕ) → ℕ → Prop
  | [], _k => True
  | (P, Q) :: xs, k =>
      H (Q + (corridorQSum xs + k)) =
          P + H (corridorQSum xs + k) ∧
        ExactInverseCorridorChain H xs k

/-- 空の corridor 列は任意 residual に対して exact。 -/
@[simp] theorem exactInverseCorridorChain_nil
    (H : ℕ → ℕ) (k : ℕ) :
    ExactInverseCorridorChain H [] k := trivial

/-- head translation と tail certificate から chain を一段延長する。 -/
theorem exactInverseCorridorChain_cons
    {H : ℕ → ℕ}
    {P Q k : ℕ}
    {xs : List (ℕ × ℕ)}
    (hHead :
      H (Q + (corridorQSum xs + k)) =
        P + H (corridorQSum xs + k))
    (hTail : ExactInverseCorridorChain H xs k) :
    ExactInverseCorridorChain H ((P, Q) :: xs) k := by
  exact ⟨hHead, hTail⟩

/--
有限 corridor chain の exact composition。

`Q` shift は全て足し合わされ、対応する `P` shift も全て足し合わされる。
途中に追加補正は発生しない。
-/
theorem exactInverseCorridorChain_eq
    {H : ℕ → ℕ} :
    ∀ {xs : List (ℕ × ℕ)} {k : ℕ},
      ExactInverseCorridorChain H xs k →
      H (corridorQSum xs + k) = corridorPSum xs + H k
  | [], k, _ => by simp
  | (P, Q) :: xs, k, C => by
      rcases C with ⟨hHead, hTail⟩
      have hTailEq :=
        exactInverseCorridorChain_eq (H := H) (xs := xs) (k := k) hTail
      calc
        H (corridorQSum ((P, Q) :: xs) + k)
            = H (Q + (corridorQSum xs + k)) := by
                simp [corridorQSum, Nat.add_assoc]
        _ = P + H (corridorQSum xs + k) := hHead
        _ = P + (corridorPSum xs + H k) := by rw [hTailEq]
        _ = corridorPSum ((P, Q) :: xs) + H k := by
              simp [corridorPSum, Nat.add_assoc]

/-- 二段 exact translation の明示形。 -/
theorem twoInverseCorridors_exact
    {H : ℕ → ℕ}
    {P₁ Q₁ P₂ Q₂ k : ℕ}
    (h₂ : H (Q₂ + k) = P₂ + H k)
    (h₁ : H (Q₁ + (Q₂ + k)) = P₁ + H (Q₂ + k)) :
    H (Q₁ + Q₂ + k) = P₁ + P₂ + H k := by
  calc
    H (Q₁ + Q₂ + k) = H (Q₁ + (Q₂ + k)) := by simp [Nat.add_assoc]
    _ = P₁ + H (Q₂ + k) := h₁
    _ = P₁ + (P₂ + H k) := by rw [h₂]
    _ = P₁ + P₂ + H k := by omega

/-- 三段 exact translation の明示形。 -/
theorem threeInverseCorridors_exact
    {H : ℕ → ℕ}
    {P₁ Q₁ P₂ Q₂ P₃ Q₃ k : ℕ}
    (h₃ : H (Q₃ + k) = P₃ + H k)
    (h₂ : H (Q₂ + (Q₃ + k)) = P₂ + H (Q₃ + k))
    (h₁ : H (Q₁ + (Q₂ + Q₃ + k)) = P₁ + H (Q₂ + Q₃ + k)) :
    H (Q₁ + Q₂ + Q₃ + k) = P₁ + P₂ + P₃ + H k := by
  calc
    H (Q₁ + Q₂ + Q₃ + k)
        = H (Q₁ + (Q₂ + Q₃ + k)) := by
            simp [Nat.add_assoc]
    _ = P₁ + H (Q₂ + Q₃ + k) := h₁
    _ = P₁ + H (Q₂ + (Q₃ + k)) := by
          simp [Nat.add_assoc]
    _ = P₁ + (P₂ + H (Q₃ + k)) := by
          rw [h₂]
    _ = P₁ + (P₂ + (P₃ + H k)) := by
          rw [h₃]
    _ = P₁ + P₂ + P₃ + H k := by
          omega

/--
有限 chain の最後を endpoint `(P,Q)` に着地させた形。

最後の endpoint が `H(Q)=P+ε` なら、全体の補正も exact にその `ε` 一個だけになる。
途中の corridor の orientation correction は scalar height には現れない。
-/
theorem exactInverseCorridorChain_to_endpoint
    {H : ℕ → ℕ}
    {xs : List (ℕ × ℕ)}
    {P Q ε : ℕ}
    (C : ExactInverseCorridorChain H xs Q)
    (hEnd : H Q = P + ε) :
    H (corridorQSum xs + Q) =
      corridorPSum xs + P + ε := by
  have h := exactInverseCorridorChain_eq (H := H) C
  rw [hEnd] at h
  omega

/--
同じ corridor `(P,Q)` を `c` 回 head 側へ反復したときの総和。
-/
@[simp] theorem corridorPSum_replicate
    (c P Q : ℕ) :
    corridorPSum (List.replicate c (P, Q)) = c * P := by
  induction c with
  | zero => simp
  | succ c ih =>
      simp [List.replicate_succ, ih, Nat.succ_mul, Nat.add_comm]

/-- 同じ corridor の `Q` 総和。 -/
@[simp] theorem corridorQSum_replicate
    (c P Q : ℕ) :
    corridorQSum (List.replicate c (P, Q)) = c * Q := by
  induction c with
  | zero =>
      simp
  | succ c ih =>
      simp [List.replicate_succ, ih, Nat.succ_mul, Nat.add_comm]

/--
positive-domain translation が `Qn` 未満で成立するなら、同じ block の有限反復も exact chain になる。

`c` 個の head block を並べ、最後に residual `Q` を残す。
必要な最大 residual は `c*Q` なので、`c*Q < Qn` が自然な条件である。
-/
theorem exactInverseCorridorChain_replicate
    {H : ℕ → ℕ}
    {P Q Qn c : ℕ}
    (hQPos : 0 < Q)
    (hRange : c * Q < Qn)
    (hTranslate : ∀ k : ℕ, 0 < k → k < Qn →
      H (Q + k) = P + H k) :
    ExactInverseCorridorChain H (List.replicate c (P, Q)) Q := by
  revert hRange
  induction c with
  | zero =>
      intro hRange
      simp only [List.replicate_zero, exactInverseCorridorChain_nil]
  | succ c ih =>
      intro hRange
      have hCQ : c * Q < Qn := by
        have hLe : c * Q ≤ (c + 1) * Q := by
          exact Nat.mul_le_mul_right Q (Nat.le_succ c)
        exact lt_of_le_of_lt hLe (by simpa [Nat.succ_eq_add_one] using hRange)
      have hTail := ih hCQ
      have hResidualPos : 0 < corridorQSum (List.replicate c (P, Q)) + Q := by
        omega
      have hResidualLt : corridorQSum (List.replicate c (P, Q)) + Q < Qn := by
        rw [corridorQSum_replicate]
        have hEq : c * Q + Q = (c + 1) * Q := by ring
        rw [hEq]
        simpa [Nat.succ_eq_add_one] using hRange
      have hHead := hTranslate
        (corridorQSum (List.replicate c (P, Q)) + Q)
        hResidualPos hResidualLt
      rw [List.replicate_succ]
      exact ⟨hHead, hTail⟩

/--
同じ block を正の係数 `d` 回使って endpoint に着地する場合、endpoint 補正は一度だけ。

`H(Q)=P+ε` と positive translation から
`H(dQ)=dP+ε` を得る。
-/
theorem repeatedCorridor_to_endpoint
    {H : ℕ → ℕ}
    {P Q Qn d ε : ℕ}
    (hd : 0 < d)
    (hQPos : 0 < Q)
    (hRange : (d - 1) * Q < Qn)
    (hTranslate : ∀ k : ℕ, 0 < k → k < Qn →
      H (Q + k) = P + H k)
    (hEnd : H Q = P + ε) :
    H (d * Q) = d * P + ε := by
  have C := exactInverseCorridorChain_replicate
    (H := H) (P := P) (Q := Q) (Qn := Qn)
    (c := d - 1) hQPos hRange hTranslate
  have hComp := exactInverseCorridorChain_to_endpoint
    (H := H) (P := P) (Q := Q) (ε := ε) C hEnd
  rw [corridorQSum_replicate, corridorPSum_replicate] at hComp
  have hdEq : d - 1 + 1 = d := by omega
  have hQEq : (d - 1) * Q + Q = d * Q := by
    calc
      (d - 1) * Q + Q = (d - 1 + 1) * Q := by ring
      _ = d * Q := by rw [hdEq]
  have hPEq : (d - 1) * P + P = d * P := by
    calc
      (d - 1) * P + P = (d - 1 + 1) * P := by ring
      _ = d * P := by rw [hdEq]
  rw [hQEq, hPEq] at hComp
  exact hComp

/--
height の二つの隣接 translation が分かれば、一歩差分 bit も exact に shift する。
-/
theorem upperMechanicalHeightBit_shift_of_two_translations
    {H : ℕ → ℕ}
    {P Q k : ℕ}
    (h0 : H (Q + k) = P + H k)
    (h1 : H (Q + (k + 1)) = P + H (k + 1)) :
    upperMechanicalHeightBit H (Q + k) = upperMechanicalHeightBit H k := by
  unfold upperMechanicalHeightBit
  rw [show Q + k + 1 = Q + (k + 1) by omega]
  rw [h1, h0]
  omega

/--
endpoint correction `ε∈{0,1}` と seam bit は相補的。

`H(Q)=P+ε`, `H(Q+1)=P+1` なら seam bit は `1-ε`。
従って lower endpoint `ε=0` では bit `1`、upper endpoint `ε=1` では bit `0`。
-/
theorem upperMechanicalHeightBit_endpoint_eq_one_sub
    {H : ℕ → ℕ}
    {P Q ε : ℕ}
    (hε : ε ≤ 1)
    (hEnd : H Q = P + ε)
    (hNext : H (Q + 1) = P + 1) :
    upperMechanicalHeightBit H Q = 1 - ε := by
  unfold upperMechanicalHeightBit
  rw [hEnd, hNext]
  omega

end Experimental2
end Collatz3
