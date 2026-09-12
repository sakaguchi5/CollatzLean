import CollatzLean.Collatz3.Experimental2.GenericRecordFerrers.SturmianGraphLocalStructure
import CollatzLean.Collatz3.Experimental2.GenericRecordFerrers.SturmianGraphOstrowskiBridge
import CollatzLean.Collatz3.Experimental2.GenericRecordFerrers.LazyOstrowski

import Mathlib.Tactic.Ring

/-!
# Collatz3 Experimental2: lazy Ostrowski 表現と Sturmian graph path

2012 年論文 Definition 46 / Theorem 47 に対応する finite bridge。

前段では

* Sturmian graph の Proposition 12 / 13 型局所構造、
* lazy Ostrowski 正規形の存在と一意性

を独立に閉じた。

本ファイルでは両者を接着する。

1. lazy digit prefix から graph path を実際に構成する。
2. 任意の初期 graph path から edge-count digit を読む。
3. Proposition 13 と skip-level law により、その edge-count digit が lazy 条件を満たすことを示す。
4. lazy 表現の一意性から、同じ weight の初期 path は同じ edge-count code を持つ。
5. 任意 `N` に canonical lazy path が存在するため、2012 Theorem 42/47 の
   「weight `N` の unique path code = lazy representation」を axiom なしで得る。

Lean の `SturmianPath` は arc proof を含む dependent Type なので、本ファイルでは
論文の「unique path」をまず proof-object equality ではなく edge-count code の一意性として公開する。
これは Definition 46 / Theorem 47 が数表現として実際に読む情報そのものであり、
proof irrelevance に依存した不要な path-term equalityは要求しない。
-/

namespace Collatz3
namespace Experimental2
namespace GenericRecordFerrers

namespace SturmianPath

/-- 二本の composable Sturmian path を連結する。 -/
def append
    {W : UnitOstrowskiWeightSystem}
    {u v z A B : ℕ} :
    SturmianPath W u v A →
      SturmianPath W v z B →
      SturmianPath W u z (A + B)
  | .nil _, q => by simpa using q
  | .cons edge tail, q => by
      have r := append tail q
      simpa [Nat.add_assoc] using SturmianPath.cons edge r

/-- 一つの block 内を short arc だけで `k` 個進む path。 -/
def shortRunFrom
    (W : UnitOstrowskiWeightSystem)
    (h r : ℕ) :
    (k : ℕ) →
    r + k ≤ W.a h →
    SturmianPath W
      (sturmianBlockStart W h + r)
      (sturmianBlockStart W h + r + k)
      (k * W.Q h)
  | 0, _ => by
      simpa using SturmianPath.nil (W := W) (sturmianBlockStart W h + r)
  | k + 1, hBound => by
      have hLo :
          sturmianBlockStart W h ≤ sturmianBlockStart W h + r := by omega
      have hHi :
          sturmianBlockStart W h + r < sturmianBoundary W h := by
        rw [sturmianBoundary_eq_blockStart_add]
        omega
      let e : IsSturmianArc W
          (sturmianBlockStart W h + r)
          (sturmianBlockStart W h + r + 1)
          (W.Q h) := by
        simpa [Nat.add_assoc] using IsSturmianArc.short hLo hHi
      have hTailBound : r + 1 + k ≤ W.a h := by omega
      have tail := shortRunFrom W h (r + 1) k hTailBound
      have p := SturmianPath.cons e tail
      convert p using 1 <;> simp [Nat.succ_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/--
block `h` の途中から jump で次 block に入り、その後 short arc で計 `k` 個の
level `h+1` arc を進む。
-/
def jumpThenShort
    (W : UnitOstrowskiWeightSystem)
    (h i k : ℕ)
    (hLo : sturmianBlockStart W h ≤ i)
    (hHi : i < sturmianBoundary W h)
    (hkPos : 0 < k)
    (hk : k ≤ W.a (h + 1)) :
    SturmianPath W i
      (sturmianBlockStart W (h + 1) + k)
      (k * W.Q (h + 1)) := by
  let e : IsSturmianArc W i
      (sturmianBoundary W h + 1)
      (W.Q (h + 1)) :=
    IsSturmianArc.jump hLo hHi
  have hTailBound : 1 + (k - 1) ≤ W.a (h + 1) := by omega
  have tail := shortRunFrom W (h + 1) 1 (k - 1) hTailBound
  have p := SturmianPath.cons e tail
  rw [sturmianBlockStart_succ] at p
  have hkEq : k = 1 + (k - 1) := by
    omega
  rw [sturmianBlockStart_succ, hkEq]
  simpa [Nat.add_assoc, Nat.add_mul] using p

/--
finite lazy prefix `d[0..t)` を初期状態 `0` からの graph path として実現する。

`t>0` の終点は `blockStart(t-1)+d(t-1)`。
lazy 条件 `d(t)=0 -> d(t-1)=a(t-1)` は、ある weight を飛ばすときに
前 block boundary まで到達していることを保証する。
-/
noncomputable def pathOfLazyPrefix
    (W : UnitOstrowskiWeightSystem)
    (d : ℕ → ℕ) :
    (t : ℕ) →
    (B : ∀ n < t, d n ≤ W.a n) →
    (L : ∀ n, n + 1 < t → d (n + 1) = 0 → d n = W.a n) →
    SturmianPath W 0
      (if t = 0 then 0 else sturmianBlockStart W (t - 1) + d (t - 1))
      (ostrowskiPrefixSum W.Q d t)
  | 0, _B, _L => by
      simpa using SturmianPath.nil (W := W) 0
  | 1, B, _L => by
      have hd : d 0 ≤ W.a 0 := B 0 (by omega)
      simpa using shortRunFrom W 0 0 (d 0) (by simpa using hd)
  | t + 2, B, L => by
      let Bprev : ∀ n < t + 1, d n ≤ W.a n := fun n hn => B n (by omega)
      let Lprev : ∀ n, n + 1 < t + 1 → d (n + 1) = 0 → d n = W.a n :=
        fun n hn hz => L n (by omega) hz
      have prev := pathOfLazyPrefix W d (t + 1) Bprev Lprev
      have hPrevBound : d t ≤ W.a t := B t (by omega)
      have hNewBound : d (t + 1) ≤ W.a (t + 1) := B (t + 1) (by omega)
      by_cases hNewZero : d (t + 1) = 0
      · have hPrevFull : d t = W.a t := L t (by omega) hNewZero
        have hEndPrev :
            sturmianBlockStart W t + d t = sturmianBlockStart W (t + 1) := by
          rw [hPrevFull, ← sturmianBoundary_eq_blockStart_add,
            sturmianBlockStart_succ]
        have p0 :
            SturmianPath W 0 (sturmianBlockStart W (t + 1))
              (ostrowskiPrefixSum W.Q d (t + 1)) := by
          simpa [hEndPrev] using prev
        have hValue :
            ostrowskiPrefixSum W.Q d (t + 2) =
              ostrowskiPrefixSum W.Q d (t + 1) := by
          rw [ostrowskiPrefixSum_succ, hNewZero]
          simp
        simpa [hNewZero, hValue] using p0
      · have hNewPos : 0 < d (t + 1) := Nat.pos_of_ne_zero hNewZero
        by_cases hPrevFull : d t = W.a t
        · have hEndPrev :
              sturmianBlockStart W t + d t = sturmianBlockStart W (t + 1) := by
            rw [hPrevFull, ← sturmianBoundary_eq_blockStart_add,
              sturmianBlockStart_succ]
          have prev' :
              SturmianPath W 0 (sturmianBlockStart W (t + 1))
                (ostrowskiPrefixSum W.Q d (t + 1)) := by
            simpa [hEndPrev] using prev
          have ext := shortRunFrom W (t + 1) 0 (d (t + 1))
            (by simpa using hNewBound)
          have joined := prev'.append ext
          convert joined using 1 <;>
            simp [ostrowskiPrefixSum_succ, Nat.add_assoc, Nat.add_comm]
        · have hPrevLt : d t < W.a t := by omega
          have hLo : sturmianBlockStart W t ≤ sturmianBlockStart W t + d t := by omega
          have hHi : sturmianBlockStart W t + d t < sturmianBoundary W t := by
            rw [sturmianBoundary_eq_blockStart_add]
            omega
          have ext := jumpThenShort W t
            (sturmianBlockStart W t + d t) (d (t + 1))
            hLo hHi hNewPos hNewBound
          have joined := prev.append ext
          convert joined using 1 <;>
            simp [ostrowskiPrefixSum_succ, Nat.add_assoc, Nat.add_comm]

/-- canonical lazy representation が与える実 graph path。 -/
noncomputable def pathOfLazyRepresentation
    {W : UnitOstrowskiWeightSystem}
    {N : ℕ}
    (R : LazyOstrowskiRepresentation W N) :
    InitialSturmianPathOfWeight W N := by
  let t := ostrowskiLazyLength W N
  let terminal :=
    if t = 0 then
      0
    else
      sturmianBlockStart W (t - 1) + R.digits (t - 1)
  let p :
      SturmianPath W 0 terminal
        (ostrowskiPrefixSum W.Q R.digits t) :=
    pathOfLazyPrefix W R.digits t R.bounded R.lazy
  have hValue :
      ostrowskiPrefixSum W.Q R.digits t = N := by
    simpa [t] using R.value
  refine
    { terminal := terminal
      path := ?_ }
  rw [← hValue]
  exact p

end SturmianPath

/--
初期 graph path の edge-count code が normalized finite lazy prefix を成す。
-/
theorem initialPath_lazyLength_eq_levelBound
    {W : UnitOstrowskiWeightSystem}
    {z N : ℕ}
    (P : SturmianPath W 0 z N) :
    P.levelBound = ostrowskiLazyLength W N := by
  apply lazyLength_eq_of_normalizedPrefix W
      (d := P.edgeCount)
      (t := P.levelBound)
  · intro n hn
    exact P.proposition13_edgeCount_le
  · intro n hn hZero
    exact P.lazy_previous_full_of_next_zero hn hZero
  · exact P.edgeCount_value
  · intro hPos
    exact P.edgeCount_top_pos hPos

/--
任意の初期 Sturmian graph path から、その edge-count digits を genuine lazy representation として読む。
-/
noncomputable def lazyRepresentationOfInitialPath
    {W : UnitOstrowskiWeightSystem}
    {z N : ℕ}
    (P : SturmianPath W 0 z N) :
    LazyOstrowskiRepresentation W N := by
  have hLen := initialPath_lazyLength_eq_levelBound P
  refine
    { digits := P.edgeCount
      zero_above := ?_
      bounded := ?_
      lazy := ?_
      value := ?_ }
  · intro n hn
    apply P.edgeCount_eq_zero_of_levelBound_le
    rw [hLen]
    exact hn
  · intro n hn
    exact P.proposition13_edgeCount_le
  · intro n hn hZero
    apply P.lazy_previous_full_of_next_zero
    · rw [hLen]
      exact hn
    · exact hZero
  · rw [← hLen]
    exact P.edgeCount_value

/--
Definition 46 の path-to-digits correspondence：path から読んだ digits は canonical lazy digits と一致する。
-/
theorem edgeCount_eq_canonicalLazyDigits
    {W : UnitOstrowskiWeightSystem}
    {z N : ℕ}
    (P : SturmianPath W 0 z N) :
    ∀ h, P.edgeCount h =
      (canonicalLazyOstrowskiRepresentation W N).digits h := by
  have hEq := LazyOstrowskiRepresentation.unique
    (lazyRepresentationOfInitialPath P)
    (canonicalLazyOstrowskiRepresentation W N)
  intro h
  exact congrArg (fun R => R.digits h) hEq

/--
2012 Theorem 42 の存在部分：任意 weight `N` に初期 Sturmian graph path が存在する。
-/
noncomputable def canonicalInitialSturmianPath
    (W : UnitOstrowskiWeightSystem)
    (N : ℕ) :
    InitialSturmianPathOfWeight W N :=
  SturmianPath.pathOfLazyRepresentation
    (canonicalLazyOstrowskiRepresentation W N)

/--
同じ weight を持つ二つの初期 path は edge-count code が一点ごとに一致する。
論文の unique path の proof-object independent な形式。
-/
theorem initialPaths_sameWeight_edgeCount_eq
    {W : UnitOstrowskiWeightSystem}
    {z₁ z₂ N : ℕ}
    (P : SturmianPath W 0 z₁ N)
    (Q : SturmianPath W 0 z₂ N) :
    P.edgeCount = Q.edgeCount := by
  funext h
  rw [edgeCount_eq_canonicalLazyDigits P h,
    edgeCount_eq_canonicalLazyDigits Q h]

/--
2012 Theorem 47：lazy Ostrowski digits と weight `N` の Sturmian graph path code は exact に一致する。
-/
theorem theorem47_lazy_iff_sturmianPathCode
    {W : UnitOstrowskiWeightSystem}
    {N : ℕ}
    (R : LazyOstrowskiRepresentation W N) :
    ∀ h,
      R.digits h =
        (canonicalInitialSturmianPath W N).path.edgeCount h := by
  have hLazy := LazyOstrowskiRepresentation.unique R
    (canonicalLazyOstrowskiRepresentation W N)
  intro h
  have hPath :=
    edgeCount_eq_canonicalLazyDigits (canonicalInitialSturmianPath W N).path h
  rw [congrArg (fun S => S.digits h) hLazy]
  exact hPath.symm

/--
公開まとめ：任意 `N` に path が存在し、その path の edge-count code は lazy representation に一意。
-/
theorem theorem42_47_countingCode
    (W : UnitOstrowskiWeightSystem)
    (N : ℕ) :
    ∃ P : InitialSturmianPathOfWeight W N,
      (∀ h, P.path.edgeCount h =
        (canonicalLazyOstrowskiRepresentation W N).digits h) ∧
      (∀ Q : InitialSturmianPathOfWeight W N,
        Q.path.edgeCount = P.path.edgeCount) := by
  refine ⟨canonicalInitialSturmianPath W N, ?_, ?_⟩
  · intro h
    exact edgeCount_eq_canonicalLazyDigits (canonicalInitialSturmianPath W N).path h
  · intro Q
    exact initialPaths_sameWeight_edgeCount_eq Q.path
      (canonicalInitialSturmianPath W N).path

/--
2012 Theorem 47 の iff 形。

`d` が weight `N` の lazy Ostrowski representation の digit 列であることと、
weight `N` の初期 Sturmian graph path の edge-count code として現れることは exact に同値。

左辺では `LazyOstrowskiRepresentation` が bounded / lazy adjacency / exact value / canonical support
をまとめて持つ。右辺では実 graph path を要求するため、これは単なる weighted-sum 同値ではない。
-/
theorem theorem47_lazyRepresentation_iff_exists_sturmianPath
    (W : UnitOstrowskiWeightSystem)
    (N : ℕ)
    (d : ℕ → ℕ) :
    (∃ R : LazyOstrowskiRepresentation W N, R.digits = d) ↔
      (∃ P : InitialSturmianPathOfWeight W N, P.path.edgeCount = d) := by
  constructor
  · rintro ⟨R, rfl⟩
    refine ⟨canonicalInitialSturmianPath W N, ?_⟩
    funext h
    exact (theorem47_lazy_iff_sturmianPathCode R h).symm
  · rintro ⟨P, hP⟩
    let R : LazyOstrowskiRepresentation W N :=
      lazyRepresentationOfInitialPath P.path
    refine ⟨R, ?_⟩
    exact hP

namespace RotationOstrowskiSystem

/--
任意回転 system `D` の horizontal Ostrowski basis に対する canonical Sturmian path。
既存 `horizontalWeights` をそのまま使い、新しい continued-fraction data は導入しない。
-/
noncomputable def canonicalLazySturmianGraphPath
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (N : ℕ) :
    D.InitialSturmianGraphPathOfWeight N :=
  canonicalInitialSturmianPath D.horizontalWeights N

/--
`D` の canonical Sturmian path の edge-count code は、その horizontal basis の
canonical lazy Ostrowski digits と exact に一致する。
-/
theorem canonicalLazySturmianGraphPath_edgeCount
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (N h : ℕ) :
    (D.canonicalLazySturmianGraphPath N).path.edgeCount h =
      (canonicalLazyOstrowskiRepresentation D.horizontalWeights N).digits h := by
  exact edgeCount_eq_canonicalLazyDigits (D.canonicalLazySturmianGraphPath N).path h

/--
同じ horizontal weight `N` の任意 Sturmian graph path は canonical path と同じ lazy code を持つ。
-/
theorem sturmianGraphPath_edgeCount_unique
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    {N : ℕ}
    (P : D.InitialSturmianGraphPathOfWeight N) :
    P.path.edgeCount = (D.canonicalLazySturmianGraphPath N).path.edgeCount := by
  exact initialPaths_sameWeight_edgeCount_eq
    P.path (D.canonicalLazySturmianGraphPath N).path

end RotationOstrowskiSystem

end GenericRecordFerrers
end Experimental2
end Collatz3
