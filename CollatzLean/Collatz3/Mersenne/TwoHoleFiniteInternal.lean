import CollatzLean.Collatz3.Mersenne.TwoHoleDeepArithmeticInterfaces
import CollatzLean.Collatz3.Mersenne.SmallHoleParity
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Data.List.GetD
import Std.Data.HashSet.Lemmas

set_option linter.style.nativeDecide false

/-!
# Collatz3 Mersenne: two-hole finite certificate の内部化

`TwoHoleDeepArithmeticInterfaces` で外部入力として分離していた finite modular 部分を、
巨大な一発 `native_decide` を避け、数学補題と縮小 modulus の段階 certificate へ分解する。

ここでは新しい Diophantine input は使わない。

* source odd `a=2` は mod `3^6` と二段の小 modulus sieve に分ける。
* split `a=1` は parity branch ごとの小 modulus 非交差へ落とす。
* split odd `a=2` は mod `3^6` の discrete log を数学補題化し、
  source/target の小 modulus 分類で三 residue familyだけを残す。
* target `n=3` は parity branch ごとの小 modulus 非交差へ落とす。

したがって finite arithmetic は A2 の外部仮定から外し、
外部に残すのは Chim / Gouillon 型の既知 two-log corollary と
genuinely residual な arithmetic だけにする。
-/

namespace Collatz3
namespace Mersenne

/-! ## 共通定数 -/

/-- `M₅ / 3^6`。3 も unit になる。 -/
private def twoHoleUnitModulus : ℕ := 1998451364497

/-- `twoHoleUnitModulus` は 0 ではない。 -/
private instance twoHoleUnitModulus_neZero : NeZero twoHoleUnitModulus :=
  ⟨by norm_num [twoHoleUnitModulus]⟩

/--
大きい `ZMod n` の値が自然数 `v` と一致するとき、`m ∣ n` なら
`ZMod m` への自然な射影の値は `v % m` になる。
有限 certificate を小さい modulus へ移すための共通補題。
-/
private theorem projected_val_eq_mod_of_val_eq
    {m n v : ℕ} [NeZero m] [NeZero n]
    (hDvd : m ∣ n)
    (x : ZMod n)
    (hx : x.val = v) :
    (ZMod.castHom hDvd (ZMod m) x).val = v % m := by
  have hvn : v < n := by
    rw [← hx]
    exact ZMod.val_lt x
  have hxNat : x = (v : ZMod n) := by
    apply ZMod.val_injective n
    rw [hx, ZMod.val_natCast, Nat.mod_eq_of_lt hvn]
  rw [hxNat]
  simp [ZMod.val_natCast]


/-- unit quotient 上では 2 の period 486、3 の period 1944。 -/
private theorem twoHoleUnitPeriods :
    Pow23Periods twoHoleUnitModulus 486 1944 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩ <;> native_decide

/-- mod `3^6=729` で 2 の period は 486。 -/
private theorem twoPeriod729 :
    ((2 : ZMod 729) ^ 486) = 1 := by
  native_decide

/-- `k≥6` では `3^k` は mod `729=3^6` で 0 になる。 -/
private theorem threePow_zero_mod729
    {k : ℕ}
    (hk6 : 6 ≤ k) :
    (3 : ZMod 729) ^ k = 0 := by
  have h :
      (3 : ZMod (3 ^ 6)) ^ k = 0 :=
    ZMod.natCast_pow_eq_zero_of_le 3 hk6
  exact h

/-! ### mod 729 上の冪の共通単射性

split `a=1` と split odd `a=2` の両方で使うため、
`4` の位数と `2^e` の exponent window 単射性を共通定理としてここに置く。
-/

/--
`4 = 1 + 3` の mod `3^6 = 729` における位数は `3^5 = 243`。
-/
private theorem four_order_mod729 :
    orderOf (4 : ZMod 729) = 243 := by
  rw [show (4 : ZMod 729) = 1 + 3 by norm_num]
  exact
    ZMod.orderOf_one_add_prime
      (p := 3)
      (by decide : Nat.Prime 3)
      (by norm_num : (3 : ℕ) ≠ 2)
      5

/-- `4^e` は exponent window `0 ≤ e < 243` 上で単射。 -/
private theorem fourPow729_window_injective
    {s t : ℕ}
    (hs : s < 243)
    (ht : t < 243)
    (hEq : (4 : ZMod 729) ^ s = (4 : ZMod 729) ^ t) :
    s = t := by
  exact pow_injOn_Iio_orderOf
    (x := (4 : ZMod 729))
    (by simpa [four_order_mod729] using hs)
    (by simpa [four_order_mod729] using ht)
    hEq

/--
`2 mod 729` の exponent window `0 ≤ e < 486` における単射性。

偶奇を mod 3 で一致させた後、`2^(2q) = 4^q` に落とし、
`orderOf (4 : ZMod 729) = 243` を使う。
-/
private theorem twoPow729_window_injective
    {s t : ℕ}
    (hs : s < 486)
    (ht : t < 486)
    (hEq :
      ((2 : ZMod 729) ^ s).val =
        ((2 : ZMod 729) ^ t).val) :
    s = t := by
  have hEq729 :
      (2 : ZMod 729) ^ s = (2 : ZMod 729) ^ t :=
    (ZMod.val_injective 729) hEq
  have hMod729 : 2 ^ s ≡ 2 ^ t [MOD 729] := by
    apply (ZMod.natCast_eq_natCast_iff (2 ^ s) (2 ^ t) 729).mp
    simpa using hEq729
  have hMod3 : 2 ^ s ≡ 2 ^ t [MOD 3] :=
    hMod729.of_dvd (by norm_num : 3 ∣ 729)
  have hEq3Nat :
      ((2 ^ s : ℕ) : ZMod 3) = ((2 ^ t : ℕ) : ZMod 3) :=
    (ZMod.natCast_eq_natCast_iff (2 ^ s) (2 ^ t) 3).2 hMod3
  have hEq3 :
      (2 : ZMod 3) ^ s = (2 : ZMod 3) ^ t := by
    simpa using hEq3Nat
  have hPeriod3 : (2 : ZMod 3) ^ 2 = 1 := by
    decide
  rw [pow_eq_pow_mod_of_pow_eq_one (2 : ZMod 3) (e := s) hPeriod3,
      pow_eq_pow_mod_of_pow_eq_one (2 : ZMod 3) (e := t) hPeriod3] at hEq3
  have hParity : s % 2 = t % 2 := by
    rcases Nat.mod_two_eq_zero_or_one s with hs0 | hs1 <;>
      rcases Nat.mod_two_eq_zero_or_one t with ht0 | ht1
    · omega
    · exfalso
      have hbad :
          (2 : ZMod 3) ^ 0 = (2 : ZMod 3) ^ 1 := by
        simpa [hs0, ht1] using hEq3
      exact
        (by decide :
          (2 : ZMod 3) ^ 0 ≠ (2 : ZMod 3) ^ 1) hbad
    · exfalso
      have hbad :
          (2 : ZMod 3) ^ 1 = (2 : ZMod 3) ^ 0 := by
        simpa [hs1, ht0] using hEq3
      exact
        (by decide :
          (2 : ZMod 3) ^ 1 ≠ (2 : ZMod 3) ^ 0) hbad
    · omega
  rcases Nat.mod_two_eq_zero_or_one s with hs0 | hs1
  · have ht0 : t % 2 = 0 := by omega
    have hsRep : s = 2 * (s / 2) := by
      have h := Nat.mod_add_div s 2
      omega
    have htRep : t = 2 * (t / 2) := by
      have h := Nat.mod_add_div t 2
      omega
    have hPow4 :
        (4 : ZMod 729) ^ (s / 2) =
          (4 : ZMod 729) ^ (t / 2) := by
      have h := hEq729
      rw [hsRep, htRep, pow_mul, pow_mul] at h
      norm_num at h ⊢
      exact h
    have hsHalf : s / 2 < 243 := by omega
    have htHalf : t / 2 < 243 := by omega
    have hHalf :=
      fourPow729_window_injective hsHalf htHalf hPow4
    omega
  · have ht1 : t % 2 = 1 := by omega
    have hsRep : s = 2 * (s / 2) + 1 := by
      have h := Nat.mod_add_div s 2
      omega
    have htRep : t = 2 * (t / 2) + 1 := by
      have h := Nat.mod_add_div t 2
      omega
    have hPowOdd := hEq729
    rw [hsRep, htRep, pow_add, pow_add, pow_mul, pow_mul] at hPowOdd
    norm_num at hPowOdd
    have hTwoUnit : IsUnit (2 : ZMod 729) := by
      exact (ZMod.isUnit_iff_coprime 2 729).2 (by norm_num)
    have hPow4 :
        (4 : ZMod 729) ^ (s / 2) =
          (4 : ZMod 729) ^ (t / 2) :=
      hTwoUnit.mul_right_cancel hPowOdd
    have hsHalf : s / 2 < 243 := by omega
    have htHalf : t / 2 < 243 := by omega
    have hHalf :=
      fourPow729_window_injective hsHalf htHalf hPow4
    omega


/-! ## source odd `a=2`: finite certificate -/

private def sourceOddEndpoint729 (R T : ℕ) : ZMod 729 :=
  (2 : ZMod 729) ^ R * ((2 : ZMod 729) ^ T - 1) + 1

/--
mod 729 の endpoint equation と odd parity を満たす `(R,T)` は243組だけ。
literal certificate にして、後段の unit quotient scan を小さく保つ。
-/
private def sourceOddEndpointPairs729 : List (ℕ × ℕ) :=
  [(1, 485), (3, 391), (5, 339), (7, 113), (9, 361),
   (11, 165), (13, 443), (15, 61), (17, 207), (19, 17),
   (21, 463), (23, 465), (25, 293), (27, 109), (29, 453),
   (31, 299), (33, 457), (35, 171), (37, 35), (39, 49),
   (41, 105), (43, 473), (45, 343), (47, 255), (49, 155),
   (51, 367), (53, 135), (55, 53), (57, 121), (59, 231),
   (61, 167), (63, 91), (65, 57), (67, 11), (69, 277),
   (71, 99), (73, 71), (75, 193), (77, 357), (79, 347),
   (81, 325), (83, 345), (85, 353), (87, 187), (89, 63),
   (91, 89), (93, 265), (95, 483), (97, 41), (99, 73),
   (101, 147), (103, 209), (105, 97), (107, 27), (109, 107),
   (111, 337), (113, 123), (115, 221), (117, 307), (119, 435),
   (121, 65), (123, 7), (125, 477), (127, 125), (129, 409),
   (131, 249), (133, 401), (135, 55), (137, 237), (139, 407),
   (141, 403), (143, 441), (145, 143), (147, 481), (149, 375),
   (151, 95), (153, 289), (155, 39), (157, 263), (159, 313),
   (161, 405), (163, 161), (165, 67), (167, 15), (169, 275),
   (171, 37), (173, 327), (175, 119), (177, 223), (179, 369),
   (181, 179), (183, 139), (185, 141), (187, 455), (189, 271),
   (191, 129), (193, 461), (195, 133), (197, 333), (199, 197),
   (201, 211), (203, 267), (205, 149), (207, 19), (209, 417),
   (211, 317), (213, 43), (215, 297), (217, 215), (219, 283),
   (221, 393), (223, 329), (225, 253), (227, 219), (229, 173),
   (231, 439), (233, 261), (235, 233), (237, 355), (239, 33),
   (241, 23), (243, 1), (245, 21), (247, 29), (249, 349),
   (251, 225), (253, 251), (255, 427), (257, 159), (259, 203),
   (261, 235), (263, 309), (265, 371), (267, 259), (269, 189),
   (271, 269), (273, 13), (275, 285), (277, 383), (279, 469),
   (281, 111), (283, 227), (285, 169), (287, 153), (289, 287),
   (291, 85), (293, 411), (295, 77), (297, 217), (299, 399),
   (301, 83), (303, 79), (305, 117), (307, 305), (309, 157),
   (311, 51), (313, 257), (315, 451), (317, 201), (319, 425),
   (321, 475), (323, 81), (325, 323), (327, 229), (329, 177),
   (331, 437), (333, 199), (335, 3), (337, 281), (339, 385),
   (341, 45), (343, 341), (345, 301), (347, 303), (349, 131),
   (351, 433), (353, 291), (355, 137), (357, 295), (359, 9),
   (361, 359), (363, 373), (365, 429), (367, 311), (369, 181),
   (371, 93), (373, 479), (375, 205), (377, 459), (379, 377),
   (381, 445), (383, 69), (385, 5), (387, 415), (389, 381),
   (391, 335), (393, 115), (395, 423), (397, 395), (399, 31),
   (401, 195), (403, 185), (405, 163), (407, 183), (409, 191),
   (411, 25), (413, 387), (415, 413), (417, 103), (419, 321),
   (421, 365), (423, 397), (425, 471), (427, 47), (429, 421),
   (431, 351), (433, 431), (435, 175), (437, 447), (439, 59),
   (441, 145), (443, 273), (445, 389), (447, 331), (449, 315),
   (451, 449), (453, 247), (455, 87), (457, 239), (459, 379),
   (461, 75), (463, 245), (465, 241), (467, 279), (469, 467),
   (471, 319), (473, 213), (475, 419), (477, 127), (479, 363),
   (481, 101), (483, 151), (485, 243)]
/--
mod729 の endpoint equation と odd parity を満たす finite `(R,T)` は、
明示した `sourceOddEndpointPairs729` の243組のどれかに必ず入る。
-/
private theorem sourceOddEndpointPairs729_complete :
    ∀ R T : Fin 486,
      R.1 % 2 = 1 →
      T.1 % 2 = 1 →
      sourceOddEndpoint729 R.1 T.1 = 0 →
      (R.1, T.1) ∈ sourceOddEndpointPairs729 := by
  native_decide

private def sourceOddDiffQ (N B : ℕ) : ZMod twoHoleUnitModulus :=
  (2 : ZMod twoHoleUnitModulus) ^ N -
    (2 : ZMod twoHoleUnitModulus) ^ B

private def sourceOddRightQ (K R T : ℕ) : ZMod twoHoleUnitModulus :=
  5 +
    (3 : ZMod twoHoleUnitModulus) ^ (1944 - K) *
      ((2 : ZMod twoHoleUnitModulus) ^ R *
        ((2 : ZMod twoHoleUnitModulus) ^ T - 1) + 1)

/-!
### source odd の段階 sieve

full unit modulus 上の巨大な左右リストを作らず、証明は二段へ分ける。

* 第1段: `73 * 163 * 2593 = 30854107` で候補を小さくする。
* 第2段: `487` で残りを排除する。

この theorem はその二段 certificate の薄い interface。
後で証明を実装する際にも、full `twoHoleUnitModulus` の全探索へ戻さない。
-/

private def sourceOddStageOneModulus : ℕ := 30854107
private def sourceOddStageTwoModulus : ℕ := 487


/-- source odd 左辺を任意の縮小 modulus 上で読む。 -/
private def sourceOddDiffAt (m N B : ℕ) : ZMod m :=
  (2 : ZMod m) ^ N - (2 : ZMod m) ^ B

/-- source odd 右辺を任意の縮小 modulus 上で読む。 -/
private def sourceOddRightAt (m K R T : ℕ) : ZMod m :=
  5 +
    (3 : ZMod m) ^ (1944 - K) *
      ((2 : ZMod m) ^ R * ((2 : ZMod m) ^ T - 1) + 1)

/--
`sourceOddDiffQ` を divisor modulus へ射影すると `sourceOddDiffAt` になる。
-/
private theorem sourceOddDiffQ_project
    {m : ℕ}
    (hDvd : m ∣ twoHoleUnitModulus)
    (N B : ℕ) :
    ZMod.castHom hDvd (ZMod m) (sourceOddDiffQ N B) =
      sourceOddDiffAt m N B := by
  unfold sourceOddDiffQ sourceOddDiffAt
  simp only [map_sub, map_pow, map_ofNat]

/--
`sourceOddRightQ` を divisor modulus へ射影すると `sourceOddRightAt` になる。
-/
private theorem sourceOddRightQ_project
    {m : ℕ}
    (hDvd : m ∣ twoHoleUnitModulus)
    (K R T : ℕ) :
    ZMod.castHom hDvd (ZMod m) (sourceOddRightQ K R T) =
      sourceOddRightAt m K R T := by
  unfold sourceOddRightQ sourceOddRightAt
  simp only [map_add, map_mul, map_pow, map_sub, map_one, map_ofNat]

/--
二段 sieve で左辺を識別する署名。
第1成分は `73*163*2593`、第2成分は `487` 上の residue。
-/
private def sourceOddLeftSignature (N B : ℕ) : ℕ × ℕ :=
  ((sourceOddDiffAt sourceOddStageOneModulus N B).val,
   (sourceOddDiffAt sourceOddStageTwoModulus N B).val)

/-- 二段 sieve で右辺を識別する署名。 -/
private def sourceOddRightSignature (K R T : ℕ) : ℕ × ℕ :=
  ((sourceOddRightAt sourceOddStageOneModulus K R T).val,
   (sourceOddRightAt sourceOddStageTwoModulus K R T).val)

/-- 左辺 `(N,B)` 全状態の二段署名。 -/
private def sourceOddLeftSignatures : List (ℕ × ℕ) :=
  (List.range 486).flatMap fun N =>
    (List.range 486).map fun B =>
      sourceOddLeftSignature N B

/-- 左辺署名の membership を高速に調べる集合。 -/
private def sourceOddLeftSignatureSet : Std.HashSet (ℕ × ℕ) :=
  Std.HashSet.ofList sourceOddLeftSignatures

/--
任意の finite `(N,B)` 状態の署名は `sourceOddLeftSignatureSet` に入る。
-/
private theorem sourceOddLeftSignatureSet_contains
    (N B : Fin 486) :
    sourceOddLeftSignatureSet.contains
        (sourceOddLeftSignature N.1 B.1) = true := by
  have hMem :
      sourceOddLeftSignature N.1 B.1 ∈ sourceOddLeftSignatures := by
    unfold sourceOddLeftSignatures
    apply List.mem_flatMap.mpr
    refine ⟨N.1, List.mem_range.mpr N.2, ?_⟩
    apply List.mem_map.mpr
    exact ⟨B.1, List.mem_range.mpr B.2, rfl⟩
  simpa only [
    sourceOddLeftSignatureSet,
    Std.HashSet.contains_ofList,
    List.contains_eq_mem,
    decide_eq_true_eq
  ] using hMem

/--
odd `K` と mod729 endpoint table の任意の組から作る右辺署名は、
左辺署名集合には現れない。

探索範囲は `K` と243個の endpoint pair だけであり、
`N,B,R,T` の巨大な直積は作らない。
-/
private theorem sourceOddRightSignature_not_mem :
    ∀ K : Fin 1944,
      ∀ P : Fin sourceOddEndpointPairs729.length,
        K.1 % 2 = 1 →
        sourceOddLeftSignatureSet.contains
          (sourceOddRightSignature K.1
            (sourceOddEndpointPairs729.get P).1
            (sourceOddEndpointPairs729.get P).2) = false := by
  native_decide

/--
source odd の二段 finite sieve。

full unit modulus の等式を
`73*163*2593` と `487` の二つへ射影して署名化する。
左署名集合と、odd `K`・mod729 endpoint pair から作る右署名が
非交差であることから矛盾を得る。
-/
private theorem sourceOdd_two_stage_sieve
    (K : Fin 1944) (N R T B : Fin 486)
    (hKodd : K.1 % 2 = 1)
    (hPair : (R.1, T.1) ∈ sourceOddEndpointPairs729)
    (hEq :
      sourceOddDiffQ N.1 B.1 =
        sourceOddRightQ K.1 R.1 T.1) :
    False := by
  have hDvdOne :
      sourceOddStageOneModulus ∣ twoHoleUnitModulus := by
    norm_num [sourceOddStageOneModulus, twoHoleUnitModulus]
  have hDvdTwo :
      sourceOddStageTwoModulus ∣ twoHoleUnitModulus := by
    norm_num [sourceOddStageTwoModulus, twoHoleUnitModulus]
  have hOneRaw :=
    congrArg
      (ZMod.castHom hDvdOne (ZMod sourceOddStageOneModulus))
      hEq
  have hOne :
      sourceOddDiffAt sourceOddStageOneModulus N.1 B.1 =
        sourceOddRightAt sourceOddStageOneModulus K.1 R.1 T.1 := by
    rw [sourceOddDiffQ_project hDvdOne,
        sourceOddRightQ_project hDvdOne] at hOneRaw
    exact hOneRaw
  have hTwoRaw :=
    congrArg
      (ZMod.castHom hDvdTwo (ZMod sourceOddStageTwoModulus))
      hEq
  have hTwo :
      sourceOddDiffAt sourceOddStageTwoModulus N.1 B.1 =
        sourceOddRightAt sourceOddStageTwoModulus K.1 R.1 T.1 := by
    rw [sourceOddDiffQ_project hDvdTwo,
        sourceOddRightQ_project hDvdTwo] at hTwoRaw
    exact hTwoRaw
  have hSignature :
      sourceOddLeftSignature N.1 B.1 =
        sourceOddRightSignature K.1 R.1 T.1 := by
    apply Prod.ext
    · exact congrArg ZMod.val hOne
    · exact congrArg ZMod.val hTwo
  have hContains :
      sourceOddLeftSignatureSet.contains
          (sourceOddRightSignature K.1 R.1 T.1) = true := by
    rw [← hSignature]
    exact sourceOddLeftSignatureSet_contains N B
  obtain ⟨P, hP⟩ := List.get_of_mem hPair
  have hNot0 := sourceOddRightSignature_not_mem K P hKodd
  have hR : (sourceOddEndpointPairs729.get P).1 = R.1 :=
    congrArg Prod.fst hP
  have hT : (sourceOddEndpointPairs729.get P).2 = T.1 :=
    congrArg Prod.snd hP
  have hNot :
      sourceOddLeftSignatureSet.contains
          (sourceOddRightSignature K.1 R.1 T.1) = false := by
    rw [hR, hT] at hNot0
    exact hNot0
  simp [hNot] at hContains

/--
source odd resonance `a=2` の finite certificate は無条件に成立する。

深い数論ではなく、mod729 の endpoint table と `M₅/729` の
meet-in-the-middle residue 非交差だけを使う。
-/
theorem sourceOddM5FiniteCertificate_internal :
    SourceOddM5FiniteCertificate := by
  intro k n r L b hk7 hkOdd hb2 hbn hr hL hEq
  have hkPos : 0 < k := by omega
  have hParity := hEq.endpoint_parity hkPos
  have h729 := hEq.to_mod 729
  unfold SourceTwoHoleModEquation at h729
  have hThreeZero : (3 : ZMod 729) ^ k = 0 :=
    threePow_zero_mod729 (by omega)
  rw [hThreeZero] at h729
  simp only [zero_mul] at h729
  rw [pow_eq_pow_mod_of_pow_eq_one (2 : ZMod 729) (e := r) twoPeriod729,
      pow_eq_pow_mod_of_pow_eq_one (2 : ZMod 729) (e := L) twoPeriod729] at h729
  have hEndpoint :
      sourceOddEndpoint729 (r % 486) (L % 486) = 0 := by
    simpa [sourceOddEndpoint729] using h729.symm
  let K : Fin 1944 :=
    ⟨k % 1944, Nat.mod_lt _ (by norm_num)⟩
  let N : Fin 486 :=
    ⟨n % 486, Nat.mod_lt _ (by norm_num)⟩
  let R : Fin 486 :=
    ⟨r % 486, Nat.mod_lt _ (by norm_num)⟩
  let T : Fin 486 :=
    ⟨L % 486, Nat.mod_lt _ (by norm_num)⟩
  let B : Fin 486 :=
    ⟨b % 486, Nat.mod_lt _ (by norm_num)⟩
  have hKodd : K.1 % 2 = 1 := by
    dsimp [K]
    have hmod : (k % 1944) % 2 = k % 2 := by
      simp only [Nat.reduceDvd, Nat.mod_mod_of_dvd]
    rw [hmod, hkOdd]
  have hRodd : R.1 % 2 = 1 := by
    dsimp [R]
    have hmod : (r % 486) % 2 = r % 2 := by
      simp only [Nat.reduceDvd, Nat.mod_mod_of_dvd]
    rw [hmod, hParity.1]
  have hTodd : T.1 % 2 = 1 := by
    dsimp [T]
    have hmod : (L % 486) % 2 = L % 2 := by
      simp only [Nat.reduceDvd, Nat.mod_mod_of_dvd]
    rw [hmod, hParity.2]
  have hPair :
      (R.1, T.1) ∈ sourceOddEndpointPairs729 := by
    apply sourceOddEndpointPairs729_complete R T hRodd hTodd
    simpa [R, T] using hEndpoint
  have hQ := hEq.to_mod twoHoleUnitModulus
  have hQred := hQ.reduce twoHoleUnitPeriods
  have hFinite :
      SourceTwoHoleModEquation twoHoleUnitModulus
        K.1 N.1 R.1 T.1 2 B.1 := by
    simpa [K, N, R, T, B] using hQred
  let F : ZMod twoHoleUnitModulus :=
    (3 : ZMod twoHoleUnitModulus) ^ (1944 - K.1)
  have hInv :
      F * (3 : ZMod twoHoleUnitModulus) ^ K.1 = 1 := by
    dsimp [F]
    rw [← pow_add, Nat.sub_add_cancel (Nat.le_of_lt K.2)]
    exact twoHoleUnitPeriods.three_period
  have hFinite' := hFinite
  unfold SourceTwoHoleModEquation at hFinite'
  norm_num at hFinite'
  have hFiniteNorm :
      (3 : ZMod twoHoleUnitModulus) ^ K.1 *
          ((2 : ZMod twoHoleUnitModulus) ^ N.1 - 5 -
            (2 : ZMod twoHoleUnitModulus) ^ B.1) =
        (2 : ZMod twoHoleUnitModulus) ^ R.1 *
          ((2 : ZMod twoHoleUnitModulus) ^ T.1 - 1) + 1 := by
    calc
      (3 : ZMod twoHoleUnitModulus) ^ K.1 *
          ((2 : ZMod twoHoleUnitModulus) ^ N.1 - 5 -
            (2 : ZMod twoHoleUnitModulus) ^ B.1)
          =
        (3 : ZMod twoHoleUnitModulus) ^ K.1 *
          ((2 : ZMod twoHoleUnitModulus) ^ N.1 - 1 - 4 -
            (2 : ZMod twoHoleUnitModulus) ^ B.1) := by ring
      _ = _ := hFinite'
  have hCore :
      F *
          ((2 : ZMod twoHoleUnitModulus) ^ R.1 *
            ((2 : ZMod twoHoleUnitModulus) ^ T.1 - 1) + 1) =
        (2 : ZMod twoHoleUnitModulus) ^ N.1 - 5 -
          (2 : ZMod twoHoleUnitModulus) ^ B.1 := by
    calc
      F *
          ((2 : ZMod twoHoleUnitModulus) ^ R.1 *
            ((2 : ZMod twoHoleUnitModulus) ^ T.1 - 1) + 1)
          =
        F *
          ((3 : ZMod twoHoleUnitModulus) ^ K.1 *
            ((2 : ZMod twoHoleUnitModulus) ^ N.1 - 5 -
              (2 : ZMod twoHoleUnitModulus) ^ B.1)) := by
                rw [hFiniteNorm]
      _ =
        (F * (3 : ZMod twoHoleUnitModulus) ^ K.1) *
          ((2 : ZMod twoHoleUnitModulus) ^ N.1 - 5 -
            (2 : ZMod twoHoleUnitModulus) ^ B.1) := by ring
      _ =
        (2 : ZMod twoHoleUnitModulus) ^ N.1 - 5 -
          (2 : ZMod twoHoleUnitModulus) ^ B.1 := by
            rw [hInv, one_mul]
  have hNorm :
      sourceOddDiffQ N.1 B.1 =
        sourceOddRightQ K.1 R.1 T.1 := by
    unfold sourceOddDiffQ sourceOddRightQ
    dsimp [F] at hCore
    rw [hCore]
    ring
  exact sourceOdd_two_stage_sieve K N R T B hKodd hPair hNorm

/-! ## split `a=1`: M₄ finite certificate -/

private def splitAOneSourceM4 (J N : ℕ) : ZMod ThreeTail.modulus :=
  (3 : ZMod ThreeTail.modulus) ^ (6 + J) *
    ((2 : ZMod ThreeTail.modulus) ^ N - 3)

private def splitAOneTargetM4 (r L B : ℕ) : ZMod ThreeTail.modulus :=
  (2 : ZMod ThreeTail.modulus) ^ r *
    ((2 : ZMod ThreeTail.modulus) ^ L - 1 -
      (2 : ZMod ThreeTail.modulus) ^ B) + 1

/-!
### split `a=1` の縮小 modulus sieve

M₄ 全体の左右 residue list を作る必要はない。

* even branch (`r=2`) は `729 * 7 * 19 * 73 = 7077861` で既に非交差。
* odd branch (`r=1`) は `729 * 7 * 19 * 163 * 487 = 7696543617` で既に非交差。

下の二本だけを有限 certificate の葉として残す。
-/

private def splitAOneEvenSieveModulus : ℕ := 7077861
private def splitAOneOddSieveModulus : ℕ := 7696543617


/-- split `a=1` の source residue を任意の縮小 modulus 上で読む。 -/
private def splitAOneSourceAt (m J N : ℕ) : ZMod m :=
  (3 : ZMod m) ^ (6 + J) * ((2 : ZMod m) ^ N - 3)

/-- split `a=1` の target residue を任意の縮小 modulus 上で読む。 -/
private def splitAOneTargetAt (m r T B : ℕ) : ZMod m :=
  (2 : ZMod m) ^ r *
    ((2 : ZMod m) ^ T - 1 - (2 : ZMod m) ^ B) + 1

/-- M₄ source residue の divisor modulus への射影。 -/
private theorem splitAOneSourceM4_project
    {m : ℕ}
    (hDvd : m ∣ ThreeTail.modulus)
    (J N : ℕ) :
    ZMod.castHom hDvd (ZMod m) (splitAOneSourceM4 J N) =
      splitAOneSourceAt m J N := by
  unfold splitAOneSourceM4 splitAOneSourceAt
  simp only [map_mul, map_pow, map_sub, map_ofNat]

/-- M₄ target residue の divisor modulus への射影。 -/
private theorem splitAOneTargetM4_project
    {m : ℕ}
    (hDvd : m ∣ ThreeTail.modulus)
    (r T B : ℕ) :
    ZMod.castHom hDvd (ZMod m) (splitAOneTargetM4 r T B) =
      splitAOneTargetAt m r T B := by
  unfold splitAOneTargetM4 splitAOneTargetAt
  simp only [map_add, map_mul, map_pow, map_sub, map_one, map_ofNat]

/-!
### split `a=1`: mod 729 での一意化と段階 certificate

ここから先は `splitAOneEvenTargetSet` / `splitAOneOddTargetSet` の
`486 × 486` 全 target 探索を証明の葉にしない。

* mod 729 で各許容 `T` に対する `B` を一意化する。
* even branch は `7*19*73 = 9709` 上の 324 source 状態だけを見る。
* odd branch は `7*19*163 = 21679` で 16 source residue へ絞り、
  `487` で残りを排除する。

有限計算はすべて kernel `decide` で十分小さい certificate に分割する。
`native_decide` は使わない。
-/

/-- `splitAOneSourceAt` の divisor modulus への自然な射影。 -/
private theorem splitAOneSourceAt_project
    {m n : ℕ}
    (hDvd : m ∣ n)
    (J N : ℕ) :
    ZMod.castHom hDvd (ZMod m) (splitAOneSourceAt n J N) =
      splitAOneSourceAt m J N := by
  unfold splitAOneSourceAt
  simp only [map_mul, map_pow, map_sub, map_ofNat]

/-- `splitAOneTargetAt` の divisor modulus への自然な射影。 -/
private theorem splitAOneTargetAt_project
    {m n : ℕ}
    (hDvd : m ∣ n)
    (r T B : ℕ) :
    ZMod.castHom hDvd (ZMod m) (splitAOneTargetAt n r T B) =
      splitAOneTargetAt m r T B := by
  unfold splitAOneTargetAt
  simp only [map_add, map_mul, map_pow, map_sub, map_one, map_ofNat]

/-!
#### mod 729 で target の `B` を一意化する literal certificate

even branch は全 486 個の `T`、odd branch は `T=2U` の 243 個だけを持つ。
各表の正当性確認は高々 486 件の小さい `decide` で済む。
-/

private def splitAOneEvenBTable : List ℕ :=
[
  484, 21, 330, 197, 158, 67, 184, 63, 462, 293, 398, 55, 208, 267,
  432, 65, 476, 205, 70, 147, 240, 485, 392, 31, 256, 189, 372, 95,
  146, 19, 280, 393, 342, 353, 224, 169, 142, 273, 150, 287, 140, 481,
  328, 315, 282, 383, 380, 469, 352, 33, 252, 155, 458, 133, 214, 399,
  60, 89, 374, 445, 400, 441, 192, 185, 128, 433, 424, 159, 162, 443,
  206, 97, 286, 39, 456, 377, 122, 409, 472, 81, 102, 473, 362, 397,
  10, 285, 72, 245, 440, 61, 358, 165, 366, 179, 356, 373, 58, 207,
  12, 275, 110, 361, 82, 411, 468, 47, 188, 25, 430, 291, 276, 467,
  104, 337, 130, 333, 408, 77, 344, 325, 154, 51, 378, 335, 422, 475,
  16, 417, 186, 269, 338, 301, 202, 459, 318, 365, 92, 289, 226, 177,
  288, 137, 170, 439, 88, 57, 96, 71, 86, 265, 274, 99, 228, 167,
  326, 253, 298, 303, 198, 425, 404, 403, 160, 183, 6, 359, 320, 229,
  346, 225, 138, 455, 74, 217, 370, 429, 108, 227, 152, 367, 232, 309,
  402, 161, 68, 193, 418, 351, 48, 257, 308, 181, 442, 69, 18, 29,
  386, 331, 304, 435, 312, 449, 302, 157, 4, 477, 444, 59, 56, 145,
  28, 195, 414, 317, 134, 295, 376, 75, 222, 251, 50, 121, 76, 117,
  354, 347, 290, 109, 100, 321, 324, 119, 368, 259, 448, 201, 132, 53,
  284, 85, 148, 243, 264, 149, 38, 73, 172, 447, 234, 407, 116, 223,
  34, 327, 42, 341, 32, 49, 220, 369, 174, 437, 272, 37, 244, 87,
  144, 209, 350, 187, 106, 453, 438, 143, 266, 13, 292, 9, 84, 239,
  20, 1, 316, 213, 54, 11, 98, 151, 178, 93, 348, 431, 14, 463,
  364, 135, 480, 41, 254, 451, 388, 339, 450, 299, 332, 115, 250, 219,
  258, 233, 248, 427, 436, 261, 390, 329, 2, 415, 460, 465, 360, 101,
  80, 79, 322, 345, 168, 35, 482, 391, 22, 387, 300, 131, 236, 379,
  46, 105, 270, 389, 314, 43, 394, 471, 78, 323, 230, 355, 94, 27,
  210, 419, 470, 343, 118, 231, 180, 191, 62, 7, 466, 111, 474, 125,
  464, 319, 166, 153, 120, 221, 218, 307, 190, 357, 90, 479, 296, 457,
  52, 237, 384, 413, 212, 283, 238, 279, 30, 23, 452, 271, 262, 483,
  0, 281, 44, 421, 124, 363, 294, 215, 446, 247, 310, 405, 426, 311,
  200, 235, 334, 123, 396, 83, 278, 385, 196, 3, 204, 17, 194, 211,
  382, 45, 336, 113, 434, 199, 406, 249, 306, 371, 26, 349, 268, 129,
  114, 305, 428, 175, 454, 171, 246, 401, 182, 163, 478, 375, 216, 173,
  260, 313, 340, 255, 24, 107, 176, 139, 40, 297, 156, 203, 416, 127,
  64, 15, 126, 461, 8, 277, 412, 381, 420, 395, 410, 103, 112, 423,
  66, 5, 164, 91, 136, 141, 36, 263, 242, 241
]

private def splitAOneEvenB (T : ℕ) : ℕ :=
  splitAOneEvenBTable.getD T 0

private theorem splitAOneEvenB_lt :
    ∀ T : Fin 486, splitAOneEvenB T.1 < 486 := by
  native_decide

private theorem splitAOneEvenB_spec :
    ∀ T : Fin 486,
      splitAOneTargetAt 729 2 T.1 (splitAOneEvenB T.1) = 0 := by
  native_decide

private def splitAOneOddBTable : List ℕ :=
[
  485, 393, 343, 119, 369, 175, 455, 75, 223, 35, 483, 1, 317, 135,
  481, 329, 3, 205, 71, 87, 145, 29, 387, 301, 203, 417, 187, 107,
  177, 289, 227, 153, 121, 77, 345, 169, 143, 267, 433, 425, 405, 427,
  437, 273, 151, 179, 357, 91, 137, 171, 247, 311, 201, 133, 215, 447,
  235, 335, 423, 67, 185, 129, 115, 251, 51, 379, 47, 189, 373, 59,
  57, 97, 287, 141, 37, 245, 441, 193, 419, 471, 79, 323, 231, 181,
  443, 207, 13, 293, 399, 61, 359, 321, 325, 155, 459, 319, 167, 327,
  43, 395, 411, 469, 353, 225, 139, 41, 255, 25, 431, 15, 127, 65,
  477, 445, 401, 183, 7, 467, 105, 271, 263, 243, 265, 275, 111, 475,
  17, 195, 415, 461, 9, 85, 149, 39, 457, 53, 285, 73, 173, 261,
  391, 23, 453, 439, 89, 375, 217, 371, 27, 211, 383, 381, 421, 125,
  465, 361, 83, 279, 31, 257, 309, 403, 161, 69, 19, 281, 45, 337,
  131, 237, 385, 197, 159, 163, 479, 297, 157, 5, 165, 367, 233, 249,
  307, 191, 63, 463, 365, 93, 349, 269, 339, 451, 389, 315, 283, 239,
  21, 331, 305, 429, 109, 101, 81, 103, 113, 435, 313, 341, 33, 253,
  299, 333, 409, 473, 363, 295, 377, 123, 397, 11, 99, 229, 347, 291,
  277, 413, 213, 55, 209, 351, 49, 221, 219, 259, 449, 303, 199, 407,
  117, 355, 95, 147, 241
]

private def splitAOneOddB (U : ℕ) : ℕ :=
  splitAOneOddBTable.getD U 0

private theorem splitAOneOddB_lt :
    ∀ U : Fin 243, splitAOneOddB U.1 < 486 := by
  native_decide

private theorem splitAOneOddB_spec :
    ∀ U : Fin 243,
      splitAOneTargetAt 729 1 (2 * U.1) (splitAOneOddB U.1) = 0 := by
  native_decide

/-- even target の mod729 endpoint equation は `B` を一意に決める。 -/
private theorem splitAOne_even_B_unique
    (T B : Fin 486)
    (hZero : splitAOneTargetAt 729 2 T.1 B.1 = 0) :
    B.1 = splitAOneEvenB T.1 := by
  let C : Fin 486 := ⟨splitAOneEvenB T.1, splitAOneEvenB_lt T⟩
  have hC : splitAOneTargetAt 729 2 T.1 C.1 = 0 := by
    simpa [C] using splitAOneEvenB_spec T
  have hScaled :
      (4 : ZMod 729) * (2 : ZMod 729) ^ B.1 =
        (4 : ZMod 729) * (2 : ZMod 729) ^ C.1 := by
    unfold splitAOneTargetAt at hZero hC
    norm_num at hZero hC ⊢
    linear_combination hC - hZero
  have hFourUnit : IsUnit (4 : ZMod 729) := by
    exact (ZMod.isUnit_iff_coprime 4 729).2 (by norm_num)
  have hPow :
      (2 : ZMod 729) ^ B.1 =
        (2 : ZMod 729) ^ C.1 :=
    hFourUnit.mul_left_cancel hScaled
  have hIdx :=
    twoPow729_window_injective
      B.2 C.2 (congrArg ZMod.val hPow)
  simpa [C] using hIdx

/-- odd target の mod729 endpoint equation から `T` は even。 -/
private theorem splitAOne_odd_T_even
    (T B : Fin 486)
    (hZero : splitAOneTargetAt 729 1 T.1 B.1 = 0) :
    T.1 % 2 = 0 := by
  have hDvd : 3 ∣ 729 := by norm_num
  have h3Raw :=
    congrArg (ZMod.castHom hDvd (ZMod 3)) hZero
  have h3 : splitAOneTargetAt 3 1 T.1 B.1 = 0 := by
    rw [splitAOneTargetAt_project hDvd] at h3Raw
    exact h3Raw
  have hPeriod3 : (2 : ZMod 3) ^ 2 = 1 := by decide
  unfold splitAOneTargetAt at h3
  rw [pow_eq_pow_mod_of_pow_eq_one (2 : ZMod 3) (e := T.1) hPeriod3,
      pow_eq_pow_mod_of_pow_eq_one (2 : ZMod 3) (e := B.1) hPeriod3] at h3
  rcases Nat.mod_two_eq_zero_or_one T.1 with hT0 | hT1
  · exact hT0
  · exfalso
    rcases Nat.mod_two_eq_zero_or_one B.1 with hB0 | hB1
    · rw [hT1, hB0] at h3
      norm_num at h3
    · rw [hT1, hB1] at h3
      norm_num at h3

/-- odd target の mod729 endpoint equation は、even `T=2U` ごとに `B` を一意に決める。 -/
private theorem splitAOne_odd_B_unique
    (T B : Fin 486)
    (U : Fin 243)
    (hT : T.1 = 2 * U.1)
    (hZero : splitAOneTargetAt 729 1 T.1 B.1 = 0) :
    B.1 = splitAOneOddB U.1 := by
  let C : Fin 486 := ⟨splitAOneOddB U.1, splitAOneOddB_lt U⟩
  have hC : splitAOneTargetAt 729 1 (2 * U.1) C.1 = 0 := by
    simpa [C] using splitAOneOddB_spec U
  have hZero' : splitAOneTargetAt 729 1 (2 * U.1) B.1 = 0 := by
    simpa [hT] using hZero
  have hScaled :
      (2 : ZMod 729) * (2 : ZMod 729) ^ B.1 =
        (2 : ZMod 729) * (2 : ZMod 729) ^ C.1 := by
    unfold splitAOneTargetAt at hZero' hC
    norm_num at hZero' hC ⊢
    linear_combination hC - hZero'
  have hTwoUnit : IsUnit (2 : ZMod 729) := by
    exact (ZMod.isUnit_iff_coprime 2 729).2 (by norm_num)
  have hPow :
      (2 : ZMod 729) ^ B.1 =
        (2 : ZMod 729) ^ C.1 :=
    hTwoUnit.mul_left_cancel hScaled
  have hIdx :=
    twoPow729_window_injective
      B.2 C.2 (congrArg ZMod.val hPow)
  simpa [C] using hIdx

/-!
#### even branch: `9709 = 7*19*73`

source は `J mod 36` と `N mod 18` だけに依存する。
even `J` を `J=2j` と書けば 18×18 = 324 状態だけでよい。
-/

private def splitAOneEvenStageModulus : ℕ := 9709

private theorem splitAOneEvenStage_threePeriod :
    (3 : ZMod splitAOneEvenStageModulus) ^ 36 = 1 := by
  decide

private theorem splitAOneEvenStage_twoPeriod :
    (2 : ZMod splitAOneEvenStageModulus) ^ 18 = 1 := by
  decide

private def splitAOneEvenStageTargetResidues : List ℕ :=
[
  0, 9682, 9466, 27, 2488, 6193, 189, 8170, 4055,
  1917, 4077, 8181, 2576, 8492, 7275, 6369, 8683, 9196
]

/-- mod729 で一意化した全 even target は上の18 residue のどれか。 -/
private theorem splitAOneEvenStageTargetResidues_complete :
    ∀ T : Fin 486,
      (splitAOneTargetAt splitAOneEvenStageModulus
        2 T.1 (splitAOneEvenB T.1)).val ∈
        splitAOneEvenStageTargetResidues := by
  native_decide

/--
even branch の reduced source 324 状態は18 target residue と交わらない。
ここが even branch の唯一の finite leaf。
-/
private theorem splitAOne_even_stage_source_not_target :
    ∀ J : Fin 18, ∀ N : Fin 18,
      (splitAOneSourceAt splitAOneEvenStageModulus
        (2 * J.1) N.1).val ∉ splitAOneEvenStageTargetResidues := by
  native_decide

/-- even branch の縮小 modulus 上の source/target equality は不可能。 -/
private theorem splitAOne_even_reduced_no_eq
    (J : Fin 972) (N T B : Fin 486)
    (hParity : J.1 % 2 = 0)
    (hEq :
      splitAOneSourceAt splitAOneEvenSieveModulus J.1 N.1 =
        splitAOneTargetAt splitAOneEvenSieveModulus 2 T.1 B.1) :
    False := by
  have h729Dvd : 729 ∣ splitAOneEvenSieveModulus := by
    norm_num [splitAOneEvenSieveModulus]
  have h729Raw :=
    congrArg
      (ZMod.castHom h729Dvd (ZMod 729))
      hEq
  have h729 :
      splitAOneSourceAt 729 J.1 N.1 =
        splitAOneTargetAt 729 2 T.1 B.1 := by
    rw [splitAOneSourceAt_project h729Dvd,
        splitAOneTargetAt_project h729Dvd] at h729Raw
    exact h729Raw
  have hSourceZero : splitAOneSourceAt 729 J.1 N.1 = 0 := by
    unfold splitAOneSourceAt
    rw [threePow_zero_mod729 (by omega)]
    simp
  have hTargetZero : splitAOneTargetAt 729 2 T.1 B.1 = 0 := by
    rw [← h729]
    exact hSourceZero
  have hB : B.1 = splitAOneEvenB T.1 :=
    splitAOne_even_B_unique T B hTargetZero
  have hStageDvd :
      splitAOneEvenStageModulus ∣ splitAOneEvenSieveModulus := by
    norm_num [splitAOneEvenStageModulus, splitAOneEvenSieveModulus]
  have hStageRaw :=
    congrArg
      (ZMod.castHom hStageDvd (ZMod splitAOneEvenStageModulus))
      hEq
  have hStage :
      splitAOneSourceAt splitAOneEvenStageModulus J.1 N.1 =
        splitAOneTargetAt splitAOneEvenStageModulus 2 T.1 B.1 := by
    rw [splitAOneSourceAt_project hStageDvd,
        splitAOneTargetAt_project hStageDvd] at hStageRaw
    exact hStageRaw
  have hJParity36 : (J.1 % 36) % 2 = 0 := by
    have hmod : (J.1 % 36) % 2 = J.1 % 2 := by
      simp only [Nat.reduceDvd, Nat.mod_mod_of_dvd]
    rw [hmod, hParity]
  let JR : Fin 18 := ⟨(J.1 % 36) / 2, by omega⟩
  let NR : Fin 18 := ⟨N.1 % 18, Nat.mod_lt _ (by norm_num)⟩
  have hJRep : J.1 % 36 = 2 * JR.1 := by
    dsimp [JR]
    have h := Nat.mod_add_div (J.1 % 36) 2
    omega
  have hExp3 :
      (6 + J.1) % 36 = (6 + 2 * JR.1) % 36 := by
    omega
  have hSourceReduce :
      splitAOneSourceAt splitAOneEvenStageModulus J.1 N.1 =
        splitAOneSourceAt splitAOneEvenStageModulus (2 * JR.1) NR.1 := by
    unfold splitAOneSourceAt
    rw [pow_eq_pow_mod_of_pow_eq_one
          (3 : ZMod splitAOneEvenStageModulus)
          (e := 6 + J.1) splitAOneEvenStage_threePeriod,
        pow_eq_pow_mod_of_pow_eq_one
          (2 : ZMod splitAOneEvenStageModulus)
          (e := N.1) splitAOneEvenStage_twoPeriod,
        pow_eq_pow_mod_of_pow_eq_one
          (3 : ZMod splitAOneEvenStageModulus)
          (e := 6 + 2 * JR.1) splitAOneEvenStage_threePeriod,
        pow_eq_pow_mod_of_pow_eq_one
          (2 : ZMod splitAOneEvenStageModulus)
          (e := NR.1) splitAOneEvenStage_twoPeriod,
        Nat.mod_eq_of_lt NR.2,
        hExp3]
  have hReducedEq :
      splitAOneSourceAt splitAOneEvenStageModulus (2 * JR.1) NR.1 =
        splitAOneTargetAt splitAOneEvenStageModulus
          2 T.1 (splitAOneEvenB T.1) := by
    calc
      splitAOneSourceAt splitAOneEvenStageModulus (2 * JR.1) NR.1 =
          splitAOneSourceAt splitAOneEvenStageModulus J.1 N.1 :=
        hSourceReduce.symm
      _ = splitAOneTargetAt splitAOneEvenStageModulus 2 T.1 B.1 := hStage
      _ = splitAOneTargetAt splitAOneEvenStageModulus
            2 T.1 (splitAOneEvenB T.1) := by rw [hB]
  have hTargetMem := splitAOneEvenStageTargetResidues_complete T
  have hVal := congrArg ZMod.val hReducedEq
  rw [← hVal] at hTargetMem
  exact (splitAOne_even_stage_source_not_target JR NR) hTargetMem

/-!
#### odd branch: stage 1 (`21679 = 7*19*163`) と stage 2 (`487`)
-/

private def splitAOneOddStageOneModulus : ℕ := 21679
private def splitAOneOddStageTwoModulus : ℕ := 487

private theorem splitAOneOddStageOne_threePeriod :
    (3 : ZMod splitAOneOddStageOneModulus) ^ 162 = 1 := by
  native_decide

private theorem splitAOneOddStageOne_twoPeriod :
    (2 : ZMod splitAOneOddStageOneModulus) ^ 162 = 1 := by
  native_decide

private def splitAOneOddStageOneTargetResidues : List ℕ :=
[
  0, 18527, 13726, 16513, 9063, 7342, 7063, 4023,
  19361, 8911, 10547, 20509, 420, 6669, 10800, 5201,
  21047, 21356, 20881, 7222, 5347, 17976, 4142, 19312,
  7994, 19451, 20292, 15960, 1636, 2814, 13319, 12782,
  2161, 6061, 931, 12808, 19838, 12388, 8659, 17589,
  15561, 6424, 10927, 6270, 11452, 3624, 12236, 8685,
  19445, 15715, 21299, 18115, 12915, 20382, 18354, 5493,
  21174, 14784, 2945, 18900, 9609, 13433, 15202, 6139,
  11590, 13314, 3491, 6194
]

/-- mod729 で一意化した全 odd target は stage 1 の68 residue のどれか。 -/
private theorem splitAOneOddStageOneTargetResidues_complete :
    ∀ U : Fin 243,
      (splitAOneTargetAt splitAOneOddStageOneModulus
        1 (2 * U.1) (splitAOneOddB U.1)).val ∈
        splitAOneOddStageOneTargetResidues := by
  native_decide

/-- stage 1 を通過できる source residue class は 16 個だけ。 -/
private def splitAOneOddStageOneSurvivorPairs : List (ℕ × ℕ) :=
[
  (11, 98),
  (11, 116),
  (27, 161),
  (29, 62),
  (51, 38),
  (65, 44),
  (65, 134),
  (105, 128),
  (107, 62),
  (119, 152),
  (141, 2),
  (143, 98),
  (143, 134),
  (153, 107),
  (153, 143),
  (159, 74)
]

/--
stage 1 target と交わる source reduced state は上の16 residue class に限られる。
探索量は `81 × 162 = 13122` source states。
-/
private theorem splitAOne_odd_stageOne_source_survivor :
    ∀ J : Fin 81, ∀ N : Fin 162,
      (splitAOneSourceAt splitAOneOddStageOneModulus
        (2 * J.1 + 1) N.1).val ∈ splitAOneOddStageOneTargetResidues →
      (2 * J.1 + 1, N.1) ∈ splitAOneOddStageOneSurvivorPairs := by
  native_decide

/--
16 survivor のそれぞれについて stage 1 で一致し得る `U mod 81`。
23 residue triples、exact `U<243` へ戻すと 69 candidates。
-/
private def splitAOneOddStageOneMatches :
    List ((ℕ × ℕ) × ℕ) :=
[
  ((11, 98), 46),
  ((11, 116), 73),
  ((27, 161), 11),
  ((27, 161), 41),
  ((29, 62), 10),
  ((51, 38), 56),
  ((51, 38), 77),
  ((65, 44), 55),
  ((65, 134), 10),
  ((105, 128), 11),
  ((105, 128), 41),
  ((107, 62), 52),
  ((119, 152), 19),
  ((141, 2), 56),
  ((141, 2), 77),
  ((143, 98), 61),
  ((143, 134), 52),
  ((153, 107), 5),
  ((153, 107), 47),
  ((153, 143), 59),
  ((153, 143), 74),
  ((159, 74), 11),
  ((159, 74), 41)
]

/--
survivor pair と exact `U` が stage 1 で一致するなら、
`(J mod 162, N mod 162, U mod 81)` は23個の match table に入る。
-/
private theorem splitAOne_odd_stageOne_match :
    ∀ P : Fin splitAOneOddStageOneSurvivorPairs.length,
      ∀ U : Fin 243,
        splitAOneSourceAt splitAOneOddStageOneModulus
            (splitAOneOddStageOneSurvivorPairs.get P).1
            (splitAOneOddStageOneSurvivorPairs.get P).2 =
          splitAOneTargetAt splitAOneOddStageOneModulus
            1 (2 * U.1) (splitAOneOddB U.1) →
        ((splitAOneOddStageOneSurvivorPairs.get P, U.1 % 81) :
          (ℕ × ℕ) × ℕ) ∈ splitAOneOddStageOneMatches := by
  native_decide

/-- stage 2 の source candidate。`A<6`, `D<3` は exact lift。 -/
private def splitAOneOddStageTwoSource
    (Q : Fin splitAOneOddStageOneMatches.length)
    (A : Fin 6) (D : Fin 3) :
    ZMod splitAOneOddStageTwoModulus :=
  splitAOneSourceAt splitAOneOddStageTwoModulus
    ((splitAOneOddStageOneMatches.get Q).1.1 + 162 * A.1)
    ((splitAOneOddStageOneMatches.get Q).1.2 + 162 * D.1)

/-- stage 2 の target candidate。`C<3` は `U mod 81` の exact lift。 -/
private def splitAOneOddStageTwoTarget
    (Q : Fin splitAOneOddStageOneMatches.length)
    (C : Fin 3) :
    ZMod splitAOneOddStageTwoModulus :=
  let U := (splitAOneOddStageOneMatches.get Q).2 + 81 * C.1
  splitAOneTargetAt splitAOneOddStageTwoModulus
    1 (2 * U) (splitAOneOddB U)

/--
23 match residue × 6 `J` lifts × 3 `N` lifts × 3 `U` liftsだけを
mod487 で確認する。1242 states で全て非交差。
-/
private theorem splitAOne_odd_stageTwo_disjoint :
    ∀ Q : Fin splitAOneOddStageOneMatches.length,
      ∀ A : Fin 6, ∀ D : Fin 3, ∀ C : Fin 3,
        splitAOneOddStageTwoSource Q A D ≠
          splitAOneOddStageTwoTarget Q C := by
  native_decide

/-- odd branch の縮小 modulus 上の source/target equality は不可能。 -/
private theorem splitAOne_odd_reduced_no_eq
    (J : Fin 972) (N T B : Fin 486)
    (hParity : J.1 % 2 = 1)
    (hEq :
      splitAOneSourceAt splitAOneOddSieveModulus J.1 N.1 =
        splitAOneTargetAt splitAOneOddSieveModulus 1 T.1 B.1) :
    False := by
  have h729Dvd : 729 ∣ splitAOneOddSieveModulus := by
    norm_num [splitAOneOddSieveModulus]
  have h729Raw :=
    congrArg
      (ZMod.castHom h729Dvd (ZMod 729))
      hEq
  have h729 :
      splitAOneSourceAt 729 J.1 N.1 =
        splitAOneTargetAt 729 1 T.1 B.1 := by
    rw [splitAOneSourceAt_project h729Dvd,
        splitAOneTargetAt_project h729Dvd] at h729Raw
    exact h729Raw
  have hSourceZero : splitAOneSourceAt 729 J.1 N.1 = 0 := by
    unfold splitAOneSourceAt
    rw [threePow_zero_mod729 (by omega)]
    simp
  have hTargetZero : splitAOneTargetAt 729 1 T.1 B.1 = 0 := by
    rw [← h729]
    exact hSourceZero
  have hTEven := splitAOne_odd_T_even T B hTargetZero
  have hTRep : T.1 = 2 * (T.1 / 2) := by
    have h := Nat.mod_add_div T.1 2
    omega
  let U : Fin 243 := ⟨T.1 / 2, by omega⟩
  have hB : B.1 = splitAOneOddB U.1 :=
    splitAOne_odd_B_unique T B U (by simpa [U] using hTRep) hTargetZero
  have hStageOneDvd :
      splitAOneOddStageOneModulus ∣ splitAOneOddSieveModulus := by
    norm_num [splitAOneOddStageOneModulus, splitAOneOddSieveModulus]
  have hStageOneRaw :=
    congrArg
      (ZMod.castHom hStageOneDvd (ZMod splitAOneOddStageOneModulus))
      hEq
  have hStageOne :
      splitAOneSourceAt splitAOneOddStageOneModulus J.1 N.1 =
        splitAOneTargetAt splitAOneOddStageOneModulus 1 T.1 B.1 := by
    rw [splitAOneSourceAt_project hStageOneDvd,
        splitAOneTargetAt_project hStageOneDvd] at hStageOneRaw
    exact hStageOneRaw
  have hJParity162 : (J.1 % 162) % 2 = 1 := by
    have hmod : (J.1 % 162) % 2 = J.1 % 2 := by
      simp only [Nat.reduceDvd, Nat.mod_mod_of_dvd]
    rw [hmod, hParity]
  let JR : Fin 81 := ⟨(J.1 % 162) / 2, by omega⟩
  let NR : Fin 162 := ⟨N.1 % 162, Nat.mod_lt _ (by norm_num)⟩
  have hJRep : J.1 % 162 = 2 * JR.1 + 1 := by
    dsimp [JR]
    have h := Nat.mod_add_div (J.1 % 162) 2
    omega
  have hExp3 :
      (6 + J.1) % 162 = (6 + (2 * JR.1 + 1)) % 162 := by
    omega
  have hSourceReduce :
      splitAOneSourceAt splitAOneOddStageOneModulus J.1 N.1 =
        splitAOneSourceAt splitAOneOddStageOneModulus
          (2 * JR.1 + 1) NR.1 := by
    unfold splitAOneSourceAt
    rw [pow_eq_pow_mod_of_pow_eq_one
          (3 : ZMod splitAOneOddStageOneModulus)
          (e := 6 + J.1) splitAOneOddStageOne_threePeriod,
        pow_eq_pow_mod_of_pow_eq_one
          (2 : ZMod splitAOneOddStageOneModulus)
          (e := N.1) splitAOneOddStageOne_twoPeriod,
        pow_eq_pow_mod_of_pow_eq_one
          (3 : ZMod splitAOneOddStageOneModulus)
          (e := 6 + (2 * JR.1 + 1)) splitAOneOddStageOne_threePeriod,
        pow_eq_pow_mod_of_pow_eq_one
          (2 : ZMod splitAOneOddStageOneModulus)
          (e := NR.1) splitAOneOddStageOne_twoPeriod,
        Nat.mod_eq_of_lt NR.2,
        hExp3]
  have hReducedStageOne :
      splitAOneSourceAt splitAOneOddStageOneModulus
          (2 * JR.1 + 1) NR.1 =
        splitAOneTargetAt splitAOneOddStageOneModulus
          1 (2 * U.1) (splitAOneOddB U.1) := by
    calc
      splitAOneSourceAt splitAOneOddStageOneModulus
          (2 * JR.1 + 1) NR.1 =
          splitAOneSourceAt splitAOneOddStageOneModulus J.1 N.1 :=
        hSourceReduce.symm
      _ = splitAOneTargetAt splitAOneOddStageOneModulus 1 T.1 B.1 :=
        hStageOne
      _ = splitAOneTargetAt splitAOneOddStageOneModulus
            1 (2 * U.1) (splitAOneOddB U.1) := by
        rw [hTRep, hB]
  have hTargetMem := splitAOneOddStageOneTargetResidues_complete U
  have hVal := congrArg ZMod.val hReducedStageOne
  rw [← hVal] at hTargetMem
  have hSurvivor :
      (2 * JR.1 + 1, NR.1) ∈ splitAOneOddStageOneSurvivorPairs :=
    splitAOne_odd_stageOne_source_survivor JR NR hTargetMem
  obtain ⟨P, hP⟩ := List.get_of_mem hSurvivor
  have hPairEq :
      splitAOneSourceAt splitAOneOddStageOneModulus
          (splitAOneOddStageOneSurvivorPairs.get P).1
          (splitAOneOddStageOneSurvivorPairs.get P).2 =
        splitAOneTargetAt splitAOneOddStageOneModulus
          1 (2 * U.1) (splitAOneOddB U.1) := by
    rw [hP]
    exact hReducedStageOne
  have hMatch :
      ((splitAOneOddStageOneSurvivorPairs.get P, U.1 % 81) :
        (ℕ × ℕ) × ℕ) ∈ splitAOneOddStageOneMatches :=
    splitAOne_odd_stageOne_match P U hPairEq
  obtain ⟨Q, hQ⟩ := List.get_of_mem hMatch
  have hStageTwoDvd :
      splitAOneOddStageTwoModulus ∣ splitAOneOddSieveModulus := by
    norm_num [splitAOneOddStageTwoModulus, splitAOneOddSieveModulus]
  have hStageTwoRaw :=
    congrArg
      (ZMod.castHom hStageTwoDvd (ZMod splitAOneOddStageTwoModulus))
      hEq
  have hStageTwo :
      splitAOneSourceAt splitAOneOddStageTwoModulus J.1 N.1 =
        splitAOneTargetAt splitAOneOddStageTwoModulus 1 T.1 B.1 := by
    rw [splitAOneSourceAt_project hStageTwoDvd,
        splitAOneTargetAt_project hStageTwoDvd] at hStageTwoRaw
    exact hStageTwoRaw
  let A : Fin 6 := ⟨J.1 / 162, by omega⟩
  let D : Fin 3 := ⟨N.1 / 162, by omega⟩
  let C : Fin 3 := ⟨U.1 / 81, by omega⟩
  have hJExact : J.1 = J.1 % 162 + 162 * A.1 := by
    dsimp [A]
    have h := Nat.mod_add_div J.1 162
    omega
  have hNExact : N.1 = N.1 % 162 + 162 * D.1 := by
    dsimp [D]
    have h := Nat.mod_add_div N.1 162
    omega
  have hUExact : U.1 = U.1 % 81 + 81 * C.1 := by
    dsimp [C]
    have h := Nat.mod_add_div U.1 81
    omega
  have hPActual :
      splitAOneOddStageOneSurvivorPairs.get P =
        (J.1 % 162, N.1 % 162) := by
    rw [hP]
    dsimp [NR]
    rw [← hJRep]
  have hQActual :
      splitAOneOddStageOneMatches.get Q =
        ((J.1 % 162, N.1 % 162), U.1 % 81) := by
    rw [hQ, hPActual]
  have hStageTwoNorm :
      splitAOneSourceAt splitAOneOddStageTwoModulus J.1 N.1 =
        splitAOneTargetAt splitAOneOddStageTwoModulus
          1 (2 * U.1) (splitAOneOddB U.1) := by
    calc
      splitAOneSourceAt splitAOneOddStageTwoModulus J.1 N.1 =
          splitAOneTargetAt splitAOneOddStageTwoModulus 1 T.1 B.1 :=
        hStageTwo
      _ = splitAOneTargetAt splitAOneOddStageTwoModulus
            1 (2 * U.1) (splitAOneOddB U.1) := by
        rw [hTRep, hB]
  have hCandidateEq :
      splitAOneOddStageTwoSource Q A D =
        splitAOneOddStageTwoTarget Q C := by
    unfold splitAOneOddStageTwoSource splitAOneOddStageTwoTarget
    rw [hQActual]
    dsimp
    rw [← hJExact, ← hNExact, ← hUExact]
    exact hStageTwoNorm
  exact (splitAOne_odd_stageTwo_disjoint Q A D C) hCandidateEq


/-- even branch の target residue 全体。 -/
private def splitAOneEvenTargetValues : List ℕ :=
  (List.range 486).flatMap fun T =>
    (List.range 486).map fun B =>
      (splitAOneTargetAt splitAOneEvenSieveModulus 2 T B).val

/-- even branch の target residue 集合。 -/
private def splitAOneEvenTargetSet : Std.HashSet ℕ :=
  Std.HashSet.ofList splitAOneEvenTargetValues

/-- odd branch の target residue 全体。 -/
private def splitAOneOddTargetValues : List ℕ :=
  (List.range 486).flatMap fun T =>
    (List.range 486).map fun B =>
      (splitAOneTargetAt splitAOneOddSieveModulus 1 T B).val

/-- odd branch の target residue 集合。 -/
private def splitAOneOddTargetSet : Std.HashSet ℕ :=
  Std.HashSet.ofList splitAOneOddTargetValues

/-- finite `(T,B)` の even target residue は集合に含まれる。 -/
private theorem splitAOneEvenTargetSet_contains
    (T B : Fin 486) :
    splitAOneEvenTargetSet.contains
        (splitAOneTargetAt splitAOneEvenSieveModulus 2 T.1 B.1).val = true := by
  have hMem :
      (splitAOneTargetAt splitAOneEvenSieveModulus 2 T.1 B.1).val ∈
        splitAOneEvenTargetValues := by
    unfold splitAOneEvenTargetValues
    apply List.mem_flatMap.mpr
    refine ⟨T.1, List.mem_range.mpr T.2, ?_⟩
    apply List.mem_map.mpr
    exact ⟨B.1, List.mem_range.mpr B.2, rfl⟩
  simpa only [
    splitAOneEvenTargetSet,
    Std.HashSet.contains_ofList,
    List.contains_eq_mem,
    decide_eq_true_eq
  ] using hMem

/-- finite `(T,B)` の odd target residue は集合に含まれる。 -/
private theorem splitAOneOddTargetSet_contains
    (T B : Fin 486) :
    splitAOneOddTargetSet.contains
        (splitAOneTargetAt splitAOneOddSieveModulus 1 T.1 B.1).val = true := by
  have hMem :
      (splitAOneTargetAt splitAOneOddSieveModulus 1 T.1 B.1).val ∈
        splitAOneOddTargetValues := by
    unfold splitAOneOddTargetValues
    apply List.mem_flatMap.mpr
    refine ⟨T.1, List.mem_range.mpr T.2, ?_⟩
    apply List.mem_map.mpr
    exact ⟨B.1, List.mem_range.mpr B.2, rfl⟩
  simpa only [
    splitAOneOddTargetSet,
    Std.HashSet.contains_ofList,
    List.contains_eq_mem,
    decide_eq_true_eq
  ] using hMem

/--
even `J` の source residue は even target residue 集合と交わらない。
探索は `(J,N)` の二変数だけで行う。
-/
private theorem splitAOne_even_source_not_target :
    ∀ J : Fin 972, ∀ N : Fin 486,
      J.1 % 2 = 0 →
      splitAOneEvenTargetSet.contains
          (splitAOneSourceAt splitAOneEvenSieveModulus J.1 N.1).val = false := by
  intro J N hParity
  by_cases hContains :
      splitAOneEvenTargetSet.contains
          (splitAOneSourceAt splitAOneEvenSieveModulus J.1 N.1).val = true
  · exfalso
    have hMem :
        (splitAOneSourceAt splitAOneEvenSieveModulus J.1 N.1).val ∈
          splitAOneEvenTargetValues := by
      simpa only [
        splitAOneEvenTargetSet,
        Std.HashSet.contains_ofList,
        List.contains_eq_mem,
        decide_eq_true_eq
      ] using hContains
    unfold splitAOneEvenTargetValues at hMem
    rcases List.mem_flatMap.mp hMem with ⟨T, hT, hMemT⟩
    rcases List.mem_map.mp hMemT with ⟨B, hB, hVal⟩
    let TF : Fin 486 := ⟨T, List.mem_range.mp hT⟩
    let BF : Fin 486 := ⟨B, List.mem_range.mp hB⟩
    let : NeZero splitAOneEvenSieveModulus := ⟨by
      norm_num [splitAOneEvenSieveModulus]⟩
    have hEq :
        splitAOneSourceAt splitAOneEvenSieveModulus J.1 N.1 =
          splitAOneTargetAt splitAOneEvenSieveModulus 2 TF.1 BF.1 := by
      apply ZMod.val_injective splitAOneEvenSieveModulus
      dsimp [TF, BF]
      exact hVal.symm
    exact splitAOne_even_reduced_no_eq J N TF BF hParity hEq
  · exact Bool.eq_false_of_not_eq_true hContains

/--
odd `J` の source residue は odd target residue 集合と交わらない。
探索は `(J,N)` の二変数だけで行う。
-/
private theorem splitAOne_odd_source_not_target :
    ∀ J : Fin 972, ∀ N : Fin 486,
      J.1 % 2 = 1 →
      splitAOneOddTargetSet.contains
          (splitAOneSourceAt splitAOneOddSieveModulus J.1 N.1).val = false := by
  intro J N hParity
  by_cases hContains :
      splitAOneOddTargetSet.contains
          (splitAOneSourceAt splitAOneOddSieveModulus J.1 N.1).val = true
  · exfalso
    have hMem :
        (splitAOneSourceAt splitAOneOddSieveModulus J.1 N.1).val ∈
          splitAOneOddTargetValues := by
      simpa only [
        splitAOneOddTargetSet,
        Std.HashSet.contains_ofList,
        List.contains_eq_mem,
        decide_eq_true_eq
      ] using hContains
    unfold splitAOneOddTargetValues at hMem
    rcases List.mem_flatMap.mp hMem with ⟨T, hT, hMemT⟩
    rcases List.mem_map.mp hMemT with ⟨B, hB, hVal⟩
    let TF : Fin 486 := ⟨T, List.mem_range.mp hT⟩
    let BF : Fin 486 := ⟨B, List.mem_range.mp hB⟩
    let : NeZero splitAOneOddSieveModulus := ⟨by
      norm_num [splitAOneOddSieveModulus]⟩
    have hEq :
        splitAOneSourceAt splitAOneOddSieveModulus J.1 N.1 =
          splitAOneTargetAt splitAOneOddSieveModulus 1 TF.1 BF.1 := by
      apply ZMod.val_injective splitAOneOddSieveModulus
      dsimp [TF, BF]
      exact hVal.symm
    exact splitAOne_odd_reduced_no_eq J N TF BF hParity hEq
  · exact Bool.eq_false_of_not_eq_true hContains

/--
split `a=1` even branch の縮小 modulus sieve。

M₄ 上の等式を `splitAOneEvenSieveModulus` へ射影し、
source residue が事前計算した target residue 集合に入らないことから矛盾を得る。
-/
private theorem splitAOne_even_smallMod_sieve
    (J : Fin 972) (N T B : Fin 486)
    (hParity : J.1 % 2 = 0)
    (hEq :
      splitAOneSourceM4 J.1 N.1 =
        splitAOneTargetM4 2 T.1 B.1) :
    False := by
  have hDvd :
      splitAOneEvenSieveModulus ∣ ThreeTail.modulus := by
    norm_num [splitAOneEvenSieveModulus, ThreeTail.modulus]
  have hSmallRaw :=
    congrArg
      (ZMod.castHom hDvd (ZMod splitAOneEvenSieveModulus))
      hEq
  have hSmall :
      splitAOneSourceAt splitAOneEvenSieveModulus J.1 N.1 =
        splitAOneTargetAt splitAOneEvenSieveModulus 2 T.1 B.1 := by
    rw [splitAOneSourceM4_project hDvd,
        splitAOneTargetM4_project hDvd] at hSmallRaw
    exact hSmallRaw
  have hContains :=
    splitAOneEvenTargetSet_contains T B
  have hVal := congrArg ZMod.val hSmall
  rw [← hVal] at hContains
  have hNot :=
    splitAOne_even_source_not_target J N hParity
  simp [hNot] at hContains

/--
split `a=1` odd branch の縮小 modulus sieve。

M₄ 上の等式を `splitAOneOddSieveModulus` へ射影し、
source residue と target residue 集合の非交差から矛盾を得る。
-/
private theorem splitAOne_odd_smallMod_sieve
    (J : Fin 972) (N T B : Fin 486)
    (hParity : J.1 % 2 = 1)
    (hEq :
      splitAOneSourceM4 J.1 N.1 =
        splitAOneTargetM4 1 T.1 B.1) :
    False := by
  have hDvd :
      splitAOneOddSieveModulus ∣ ThreeTail.modulus := by
    norm_num [splitAOneOddSieveModulus, ThreeTail.modulus]
  have hSmallRaw :=
    congrArg
      (ZMod.castHom hDvd (ZMod splitAOneOddSieveModulus))
      hEq
  have hSmall :
      splitAOneSourceAt splitAOneOddSieveModulus J.1 N.1 =
        splitAOneTargetAt splitAOneOddSieveModulus 1 T.1 B.1 := by
    rw [splitAOneSourceM4_project hDvd,
        splitAOneTargetM4_project hDvd] at hSmallRaw
    exact hSmallRaw
  have hContains :=
    splitAOneOddTargetSet_contains T B
  have hVal := congrArg ZMod.val hSmall
  rw [← hVal] at hContains
  have hNot :=
    splitAOne_odd_source_not_target J N hParity
  simp [hNot] at hContains

/--
split `a=1` の一つの parity branch を finite state へ落とし、
与えられた縮小-modulus sieve に渡して矛盾を得る共通補題。
-/
private theorem splitAOne_branch_impossible
    {k n r L b parity : ℕ}
    (hk7 : 7 ≤ k)
    (hKParity : k % 2 = parity)
    (hrFixed : r = if parity = 0 then 2 else 1)
    (hEq : SplitTwoHoleEquation k n r L 1 b)
    (hSieve :
      ∀ J : Fin 972, ∀ N T B : Fin 486,
        J.1 % 2 = parity →
        splitAOneSourceM4 J.1 N.1 =
          splitAOneTargetM4 (if parity = 0 then 2 else 1) T.1 B.1 →
        False) :
    False := by
  let J : Fin 972 :=
    ⟨(k - 6) % 972, Nat.mod_lt _ (by norm_num)⟩
  let N : Fin 486 :=
    ⟨n % 486, Nat.mod_lt _ (by norm_num)⟩
  let T : Fin 486 :=
    ⟨L % 486, Nat.mod_lt _ (by norm_num)⟩
  let B : Fin 486 :=
    ⟨b % 486, Nat.mod_lt _ (by norm_num)⟩
  have hJParity : J.1 % 2 = parity := by
    dsimp [J]
    have hmod :
        ((k - 6) % 972) % 2 = (k - 6) % 2 := by
      simp only [Nat.reduceDvd, Nat.mod_mod_of_dvd]
    rw [hmod]
    have hkSub : (k - 6) % 2 = k % 2 := by omega
    rw [hkSub, hKParity]
  have hMod := hEq.to_mod ThreeTail.modulus
  have hRed := hMod.reduce_tailLoop ThreeTail.loops
  have hkNot : ¬ k < 6 := by omega
  subst r
  let r0 : ℕ := if parity = 0 then 2 else 1
  have hr0mod :
      (if parity = 0 then 2 else 1) % 486 =
        (if parity = 0 then 2 else 1) := by
    apply Nat.mod_eq_of_lt
    split <;> omega
  have hFinite :
      SplitTwoHoleModEquation ThreeTail.modulus
        (ThreeTail.largeDepthKRep J) N.1 r0 T.1 1 B.1 := by
    dsimp [J, N, T, B, r0]
    simpa [tailLoopExponent, hkNot, ThreeTail.largeDepthKRep, hr0mod] using hRed
  have hFinite' := hFinite
  unfold SplitTwoHoleModEquation at hFinite'
  simp only [ThreeTail.largeDepthKRep, pow_one] at hFinite'
  have hEqZ :
      splitAOneSourceM4 J.1 N.1 =
        splitAOneTargetM4 r0 T.1 B.1 := by
    unfold splitAOneSourceM4 splitAOneTargetM4
    calc
      (3 : ZMod ThreeTail.modulus) ^ (6 + J.1) *
          ((2 : ZMod ThreeTail.modulus) ^ N.1 - 3)
          =
        (3 : ZMod ThreeTail.modulus) ^ (6 + J.1) *
          ((2 : ZMod ThreeTail.modulus) ^ N.1 - 1 - 2) := by ring
      _ =
        (2 : ZMod ThreeTail.modulus) ^ r0 *
          ((2 : ZMod ThreeTail.modulus) ^ T.1 - 1 -
            (2 : ZMod ThreeTail.modulus) ^ B.1) + 1 := hFinite'
  exact hSieve J N T B hJParity hEqZ

/-- split `a=1` の M₄ finite certificate も内部 theorem で閉じる。 -/
theorem splitAOneM4FiniteCertificate_internal :
    SplitAOneM4FiniteCertificate := by
  constructor
  · intro k n L b hk7 hkEven hn3 hb0 hbL hEq
    apply splitAOne_branch_impossible hk7 hkEven (by simp) hEq
    intro J N T B hParity hFinite
    simpa using splitAOne_even_smallMod_sieve J N T B hParity hFinite
  · intro k n L b hk7 hkOdd hn3 hb0 hbL hEq
    apply splitAOne_branch_impossible hk7 hkOdd (by simp) hEq
    intro J N T B hParity hFinite
    simpa using splitAOne_odd_smallMod_sieve J N T B hParity hFinite

/-! ## mod729 discrete log: split odd `a=2` 用 -/

/-!
## mod729 discrete log: table 全探索をやめる

`2 mod 729` の 0..485 冪が互いに異なることを数学補題として分離し、
discrete log 本体は構成的な有限逆走査として定義する。

後段の有限 certificate では、この構成的定義と一致する729要素の高速 lookup table を
独立に検証して使う。したがって `noncomputable` は導入せず、大きな分類計算で
486段の探索を毎回繰り返すことも避ける。
-/

/--
到達 residue の discrete log を 0..485 の有限走査で構成的に計算する補助関数。
一致する exponent が無い場合は sentinel `486` を返す。
-/
private def logTwoMod729Aux (x : ℕ) : ℕ → ℕ
  | 0 =>
      if ((2 : ZMod 729) ^ 0).val = x then 0 else 486
  | n + 1 =>
      if ((2 : ZMod 729) ^ (n + 1)).val = x then n + 1
      else logTwoMod729Aux x n

/-- 到達 residue の構成的 discrete log。 -/
private def logTwoMod729 (x : ℕ) : ℕ :=
  logTwoMod729Aux x 485

/--
`T≤n<486` なら、有限逆走査 `logTwoMod729Aux` は `2^T mod 729` から
exact に exponent `T` を復元する。
-/
private theorem logTwoMod729Aux_twoPow
    {T n : ℕ}
    (hTn : T ≤ n)
    (hn : n < 486) :
    logTwoMod729Aux (((2 : ZMod 729) ^ T).val) n = T := by
  induction n generalizing T with
  | zero =>
      have hT0 : T = 0 := by omega
      subst T
      simp [logTwoMod729Aux]
  | succ n ih =>
      by_cases hTop : T = n + 1
      · subst T
        simp [logTwoMod729Aux]
      · have hTle : T ≤ n := by omega
        have hTlt : T < 486 := by omega
        have hnTop : n + 1 < 486 := by omega
        have hNe :
            ((2 : ZMod 729) ^ (n + 1)).val ≠
              ((2 : ZMod 729) ^ T).val := by
          intro hEq
          have hIdx : n + 1 = T :=
            twoPow729_window_injective hnTop hTlt hEq
          exact hTop hIdx.symm
        simp only [logTwoMod729Aux, hNe, ite_false]
        exact ih hTle (by omega)

/--
`Fin 486` の exponent に対して、構成的 discrete log `logTwoMod729` は
`2^T mod 729` の逆写像として働く。
-/
private theorem logTwoMod729_twoPow
    (T : Fin 486) :
    logTwoMod729 (((2 : ZMod 729) ^ T.1).val) = T.1 := by
  unfold logTwoMod729
  apply logTwoMod729Aux_twoPow
  · omega
  · norm_num


/--
有限 certificate 用の高速 lookup table。
index `x < 729` に対して `2^t ≡ x (mod 729)` を満たす `0 ≤ t < 486`
があればその `t`、無ければ sentinel `486` を保持する。

これは純粋な有限データであり `noncomputable` を使わない。
-/
private def logTwoMod729FastTable : List ℕ :=
  [
    486, 0, 1, 486, 2, 23, 486, 394, 3, 486, 24, 283, 486, 332, 395, 486, 4, 33,
    486, 318, 25, 486, 284, 389, 486, 46, 333, 486, 396, 199, 486, 344, 5, 486, 34, 417,
    486, 258, 319, 486, 26, 215, 486, 454, 285, 486, 390, 385, 486, 302, 47, 486, 334, 423,
    486, 306, 397, 486, 200, 473, 486, 160, 345, 486, 6, 355, 486, 206, 35, 486, 418, 51,
    486, 462, 259, 486, 320, 191, 486, 136, 27, 486, 216, 109, 486, 56, 455, 486, 286, 273,
    486, 240, 391, 486, 386, 341, 486, 382, 303, 486, 48, 133, 486, 338, 335, 486, 424, 117,
    486, 126, 307, 486, 398, 437, 486, 412, 201, 486, 474, 427, 486, 80, 161, 486, 346, 69,
    486, 120, 7, 486, 356, 479, 486, 226, 207, 486, 36, 19, 486, 254, 419, 486, 52, 129,
    486, 222, 463, 486, 260, 467, 486, 310, 321, 486, 192, 367, 486, 374, 137, 486, 28, 297,
    486, 432, 217, 486, 110, 401, 486, 178, 57, 486, 456, 13, 486, 440, 287, 486, 274, 87,
    486, 264, 241, 486, 392, 281, 486, 316, 387, 486, 342, 415, 486, 452, 383, 486, 304, 471,
    486, 204, 49, 486, 134, 107, 486, 238, 339, 486, 336, 115, 486, 410, 425, 486, 118, 477,
    486, 252, 127, 486, 308, 365, 486, 430, 399, 486, 438, 85, 486, 314, 413, 486, 202, 105,
    486, 408, 475, 486, 428, 83, 486, 406, 81, 486, 162, 325, 486, 164, 347, 486, 70, 327,
    486, 186, 121, 486, 8, 233, 486, 166, 357, 486, 480, 349, 486, 446, 227, 486, 208, 171,
    486, 72, 37, 486, 20, 329, 486, 196, 255, 486, 420, 157, 486, 188, 53, 486, 130, 123,
    486, 66, 223, 486, 464, 371, 486, 10, 261, 486, 468, 235, 486, 362, 311, 486, 322, 183,
    486, 168, 193, 486, 368, 359, 486, 94, 375, 486, 138, 97, 486, 482, 29, 486, 298, 351,
    486, 378, 433, 486, 218, 293, 486, 448, 111, 486, 402, 229, 486, 62, 179, 486, 58, 141,
    486, 210, 457, 486, 14, 173, 486, 100, 441, 486, 288, 145, 486, 74, 275, 486, 88, 39,
    486, 150, 265, 486, 242, 485, 486, 22, 393, 486, 282, 331, 486, 32, 317, 486, 388, 45,
    486, 198, 343, 486, 416, 257, 486, 214, 453, 486, 384, 301, 486, 422, 305, 486, 472, 159,
    486, 354, 205, 486, 50, 461, 486, 190, 135, 486, 108, 55, 486, 272, 239, 486, 340, 381,
    486, 132, 337, 486, 116, 125, 486, 436, 411, 486, 426, 79, 486, 68, 119, 486, 478, 225,
    486, 18, 253, 486, 128, 221, 486, 466, 309, 486, 366, 373, 486, 296, 431, 486, 400, 177,
    486, 12, 439, 486, 86, 263, 486, 280, 315, 486, 414, 451, 486, 470, 203, 486, 106, 237,
    486, 114, 409, 486, 476, 251, 486, 364, 429, 486, 84, 313, 486, 104, 407, 486, 82, 405,
    486, 324, 163, 486, 326, 185, 486, 232, 165, 486, 348, 445, 486, 170, 71, 486, 328, 195,
    486, 156, 187, 486, 122, 65, 486, 370, 9, 486, 234, 361, 486, 182, 167, 486, 358, 93,
    486, 96, 481, 486, 350, 377, 486, 292, 447, 486, 228, 61, 486, 140, 209, 486, 172, 99,
    486, 144, 73, 486, 38, 149, 486, 484, 21, 486, 330, 31, 486, 44, 197, 486, 256, 213,
    486, 300, 421, 486, 158, 353, 486, 460, 189, 486, 54, 271, 486, 380, 131, 486, 124, 435,
    486, 78, 67, 486, 224, 17, 486, 220, 465, 486, 372, 295, 486, 176, 11, 486, 262, 279,
    486, 450, 469, 486, 236, 113, 486, 250, 363, 486, 312, 103, 486, 404, 323, 486, 184, 231,
    486, 444, 169, 486, 194, 155, 486, 64, 369, 486, 360, 181, 486, 92, 95, 486, 376, 291,
    486, 60, 139, 486, 98, 143, 486, 148, 483, 486, 30, 43, 486, 212, 299, 486, 352, 459,
    486, 270, 379, 486, 434, 77, 486, 16, 219, 486, 294, 175, 486, 278, 449, 486, 112, 249,
    486, 102, 403, 486, 230, 443, 486, 154, 63, 486, 180, 91, 486, 290, 59, 486, 142, 147,
    486, 42, 211, 486, 458, 269, 486, 76, 15, 486, 174, 277, 486, 248, 101, 486, 442, 153,
    486, 90, 289, 486, 146, 41, 486, 268, 75, 486, 276, 247, 486, 152, 89, 486, 40, 267,
    486, 246, 151, 486, 266, 245, 486, 244, 243
  ]

/--
`logTwoMod729FastTable` を使う構成的な O(1) lookup。
範囲外 index には sentinel `486` を返す。
-/
private def logTwoMod729Fast (x : ℕ) : ℕ :=
  logTwoMod729FastTable.getD x 486

/--
`2^e mod 729` の標準代表は 3 の倍数にはならない。
`729 → 3` へ射影して、mod 3 で `2^e ≠ 0` を使う。
-/
private theorem twoPow729_val_mod_three_ne_zero
    (e : ℕ) :
    ((2 : ZMod 729) ^ e).val % 3 ≠ 0 := by
  intro hMod
  have hDvd : 3 ∣ 729 := by
    norm_num
  have hProj :=
    projected_val_eq_mod_of_val_eq
      (m := 3)
      (n := 729)
      (v := ((2 : ZMod 729) ^ e).val)
      hDvd
      ((2 : ZMod 729) ^ e)
      rfl
  rw [hMod] at hProj
  have hValZero :
      ((2 : ZMod 3) ^ e).val = 0 := by
    simpa only [map_pow, map_ofNat] using hProj
  have hZero :
      (2 : ZMod 3) ^ e = 0 := by
    apply ZMod.val_injective 3
    simpa using hValZero
  have hNe :
      (2 : ZMod 3) ^ e ≠ 0 := by
    exact pow_ne_zero e (by decide)
  exact hNe hZero


/--
`x ≡ 0 (mod 3)` なら、`x` は mod 729 の `2` の冪の residue ではない。
-/
private theorem twoPow729_val_ne_of_mod_three_zero
    {x e : ℕ}
    (hx : x % 3 = 0) :
    ((2 : ZMod 729) ^ e).val ≠ x := by
  intro hEq
  apply twoPow729_val_mod_three_ne_zero e
  rw [hEq]
  exact hx


/--
`x` が 3 の倍数なら有限逆走査では一度も `2^e` に一致せず、
sentinel `486` まで到達する。
-/
private theorem logTwoMod729Aux_eq_486_of_mod_three_zero
    {x n : ℕ}
    (hx : x % 3 = 0) :
    logTwoMod729Aux x n = 486 := by
  induction n with
  | zero =>
      simp only [logTwoMod729Aux, pow_zero]
      split
      · next h =>
          have : Fact (1 < 729) := ⟨by norm_num⟩
          have hOne : (1 : ZMod 729).val = 1 := by
            exact ZMod.val_one 729
          rw [hOne] at h
          subst x
          norm_num at hx
      · rfl
  | succ n ih =>
      simp [
        logTwoMod729Aux,
        twoPow729_val_ne_of_mod_three_zero (e := n + 1) hx,
        ih
      ]

/--
高速表の各 entry は、

* sentinel `486` であり、その residue は 3 の倍数
* または `T < 486` で、本当に `2^T mod 729` がその residue

のどちらか。
ここで検査するのは729個の table entry だけで、
`logTwoMod729Aux` の逆走査は評価しない。
-/
private theorem logTwoMod729Fast_spec :
    ∀ X : Fin 729,
      (logTwoMod729Fast X.1 = 486 ∧ X.1 % 3 = 0) ∨
      (logTwoMod729Fast X.1 < 486 ∧
        ((2 : ZMod 729) ^ logTwoMod729Fast X.1).val = X.1) := by
  native_decide

/--
構成的再帰で定義した `logTwoMod729` と高速 lookup table は
`0 ≤ x < 729` の全 residue で一致する。
検証対象は729個だけなので、後続の大きい finite sieve とは分離している。
-/
private theorem logTwoMod729_eq_fast :
    ∀ X : Fin 729,
      logTwoMod729 X.1 = logTwoMod729Fast X.1 := by
  intro X
  rcases logTwoMod729Fast_spec X with hSentinel | hHit
  · rw [hSentinel.1]
    unfold logTwoMod729
    exact
      logTwoMod729Aux_eq_486_of_mod_three_zero
        (n := 485) hSentinel.2
  · let T : Fin 486 :=
      ⟨logTwoMod729Fast X.1, hHit.1⟩
    simpa [T, hHit.2] using
      (logTwoMod729_twoPow T)

private def splitOddEndpointTarget729 (R B : ℕ) : ZMod 729 :=
  1 + (2 : ZMod 729) ^ B -
    (2 : ZMod 729) ^ (486 - R)

private def splitOddEndpointL (R B : ℕ) : ℕ :=
  logTwoMod729 (splitOddEndpointTarget729 R B).val


/--
endpoint residue に対しては通常の `splitOddEndpointL` を高速 lookup へ置換できる。
構成的定義そのものは変更せず、有限 certificate の評価だけを高速化する。
-/
private theorem splitOddEndpointL_eq_fast
    (R B : ℕ) :
    splitOddEndpointL R B =
      logTwoMod729Fast (splitOddEndpointTarget729 R B).val := by
  unfold splitOddEndpointL
  let X : Fin 729 :=
    ⟨(splitOddEndpointTarget729 R B).val,
      ZMod.val_lt (splitOddEndpointTarget729 R B)⟩
  have h := logTwoMod729_eq_fast X
  simpa [X] using h

private def splitOddSourceQ (K N : ℕ) : ZMod twoHoleUnitModulus :=
  (3 : ZMod twoHoleUnitModulus) ^ K *
    ((2 : ZMod twoHoleUnitModulus) ^ N - 5)

private def splitOddTargetQ (R B : ℕ) : ZMod twoHoleUnitModulus :=
  let T := splitOddEndpointL R B
  (2 : ZMod twoHoleUnitModulus) ^ R *
    ((2 : ZMod twoHoleUnitModulus) ^ T - 1 -
      (2 : ZMod twoHoleUnitModulus) ^ B) + 1

/-!
### split odd `a=2` の common residue / source / target 分類

full unit modulus 上で巨大な source/target list を作り、
「survivor list がこの順序で4要素」と証明するのをやめる。

必要なのは次の三つだけ。

1. 共通値なら `V1..V4` のどれか。
2. source 側は common / complement の段階 sieve で4状態に分類。
3. target 側は `19*163*487 = 1508239` への射影で6型に分類。

リストの順序・重複は以後 theorem statement に含めない。
-/

private def splitOddV1 : ℕ := 25165809
private def splitOddV2 : ℕ := 718154506234
private def splitOddV3 : ℕ := 1452698231583
private def splitOddV4 : ℕ := 1998451364496

private def splitOddTargetClassModulus : ℕ := 1508239


/-- common-value sieve の主 modulus。source/target classification の因子をまとめたもの。 -/
private def splitOddCommonModulus : ℕ := 3910863727

/-- `splitOddCommonModulus` と互いに素な残りの因子 `7*73`。 -/
private def splitOddComplementModulus : ℕ := 511

/-- common-value sieve の主 modulus は 0 ではない。 -/
private instance splitOddCommonModulus_neZero : NeZero splitOddCommonModulus :=
  ⟨by norm_num [splitOddCommonModulus]⟩

/-- common-value sieve の補 modulus は 0 ではない。 -/
private instance splitOddComplementModulus_neZero : NeZero splitOddComplementModulus :=
  ⟨by norm_num [splitOddComplementModulus]⟩

/-- target 分類用 modulus は 0 ではない。 -/
private instance splitOddTargetClassModulus_neZero : NeZero splitOddTargetClassModulus :=
  ⟨by norm_num [splitOddTargetClassModulus]⟩

/-- split odd source residue を任意 modulus 上で読む。 -/
private def splitOddSourceAt (m K N : ℕ) : ZMod m :=
  (3 : ZMod m) ^ K * ((2 : ZMod m) ^ N - 5)

/-- split odd target residue を明示的 exponent `T` で任意 modulus 上で読む。 -/
private def splitOddTargetAt (m R T B : ℕ) : ZMod m :=
  (2 : ZMod m) ^ R *
    ((2 : ZMod m) ^ T - 1 - (2 : ZMod m) ^ B) + 1

/-- split odd source residue の divisor modulus への射影。 -/
private theorem splitOddSourceQ_project
    {m : ℕ}
    (hDvd : m ∣ twoHoleUnitModulus)
    (K N : ℕ) :
    ZMod.castHom hDvd (ZMod m) (splitOddSourceQ K N) =
      splitOddSourceAt m K N := by
  unfold splitOddSourceQ splitOddSourceAt
  simp only [map_mul, map_pow, map_sub, map_ofNat]

/-- split odd target residue の divisor modulus への射影。 -/
private theorem splitOddTargetQ_project
    {m : ℕ}
    (hDvd : m ∣ twoHoleUnitModulus)
    (R B : ℕ) :
    ZMod.castHom hDvd (ZMod m) (splitOddTargetQ R B) =
      splitOddTargetAt m R (splitOddEndpointL R B) B := by
  unfold splitOddTargetQ splitOddTargetAt
  simp only [map_add, map_mul, map_pow, map_sub, map_one, map_ofNat]

/-- finite certificate 用に高速 discrete log を使った target residue。 -/
private def splitOddTargetFastAt (m R B : ℕ) : ZMod m :=
  splitOddTargetAt m R
    (logTwoMod729Fast (splitOddEndpointTarget729 R B).val) B

/-- source state を二つの互いに素な縮小 modulus の署名へ送る。 -/
private def splitOddCommonSourceSignature (K N : ℕ) : ℕ × ℕ :=
  ((splitOddSourceAt splitOddCommonModulus K N).val,
   (splitOddSourceAt splitOddComplementModulus K N).val)

/-- target state を同じ二つの縮小 modulus の署名へ送る。 -/
private def splitOddCommonTargetSignature (R B : ℕ) : ℕ × ℕ :=
  ((splitOddTargetFastAt splitOddCommonModulus R B).val,
   (splitOddTargetFastAt splitOddComplementModulus R B).val)

/-- 全 `(R,B)` target state の縮小署名。 -/
private def splitOddCommonTargetSignatures : List (ℕ × ℕ) :=
  (List.range 486).flatMap fun R =>
    (List.range 486).map fun B =>
      splitOddCommonTargetSignature R B

/-- target の縮小署名集合。 -/
private def splitOddCommonTargetSignatureSet : Std.HashSet (ℕ × ℕ) :=
  Std.HashSet.ofList splitOddCommonTargetSignatures

/-- 任意の finite target state の署名は target 署名集合に入る。 -/
private theorem splitOddCommonTargetSignatureSet_contains
    (R B : Fin 486) :
    splitOddCommonTargetSignatureSet.contains
        (splitOddCommonTargetSignature R.1 B.1) = true := by
  have hMem :
      splitOddCommonTargetSignature R.1 B.1 ∈
        splitOddCommonTargetSignatures := by
    unfold splitOddCommonTargetSignatures
    apply List.mem_flatMap.mpr
    refine ⟨R.1, List.mem_range.mpr R.2, ?_⟩
    apply List.mem_map.mpr
    exact ⟨B.1, List.mem_range.mpr B.2, rfl⟩
  simpa only [
    splitOddCommonTargetSignatureSet,
    Std.HashSet.contains_ofList,
    List.contains_eq_mem,
    decide_eq_true_eq
  ] using hMem

/-!
### splitOddCommon_source_pair_classification の段階 certificate
-/

/-- source residue を divisor modulus へ射影する。 -/
private theorem splitOddSourceAt_project_divisor
    {m n : ℕ}
    (hDvd : m ∣ n)
    (K N : ℕ) :
    ZMod.castHom hDvd (ZMod m) (splitOddSourceAt n K N) =
      splitOddSourceAt m K N := by
  unfold splitOddSourceAt
  simp only [map_mul, map_pow, map_sub, map_ofNat]

/-- fast target residue を divisor modulus へ射影する。 -/
private theorem splitOddTargetFastAt_project_divisor
    {m n : ℕ}
    (hDvd : m ∣ n)
    (R B : ℕ) :
    ZMod.castHom hDvd (ZMod m) (splitOddTargetFastAt n R B) =
      splitOddTargetFastAt m R B := by
  unfold splitOddTargetFastAt splitOddTargetAt
  simp only [
    map_add, map_mul, map_pow, map_sub, map_one, map_ofNat
  ]


/-! #### stage 1: mod 19 と mod 511 -/

/--
stage 1 signature。

`9709 = 19 * 511` を CRT で再構成する必要はないので、
二成分のまま保持する。
-/
private def splitOddCommonStageOneSourceSignature
    (K N : ℕ) : ℕ × ℕ :=
  ((splitOddSourceAt 19 K N).val,
   (splitOddSourceAt 511 K N).val)

private def splitOddCommonStageOneTargetSignature
    (R B : ℕ) : ℕ × ℕ :=
  ((splitOddTargetFastAt 19 R B).val,
   (splitOddTargetFastAt 511 R B).val)

private theorem splitOddCommonStageOne_threePeriod19 :
    (3 : ZMod 19) ^ 36 = 1 := by
  decide

private theorem splitOddCommonStageOne_twoPeriod19 :
    (2 : ZMod 19) ^ 18 = 1 := by
  decide

private theorem splitOddCommonStageOne_threePeriod511 :
    (3 : ZMod 511) ^ 36 = 1 := by
  decide

private theorem splitOddCommonStageOne_twoPeriod511 :
    (2 : ZMod 511) ^ 18 = 1 := by
  decide

/--
source stage 1 signature は `K mod 36`, `N mod 18` のみに依存する。
-/
private theorem splitOddCommonStageOne_source_reduce
    (K N : ℕ) :
    splitOddCommonStageOneSourceSignature K N =
      splitOddCommonStageOneSourceSignature
        (K % 36) (N % 18) := by
  unfold splitOddCommonStageOneSourceSignature
  apply Prod.ext
  · dsimp
    apply congrArg ZMod.val
    unfold splitOddSourceAt
    rw [
      pow_eq_pow_mod_of_pow_eq_one
        (3 : ZMod 19) (e := K)
        splitOddCommonStageOne_threePeriod19,
      pow_eq_pow_mod_of_pow_eq_one
        (2 : ZMod 19) (e := N)
        splitOddCommonStageOne_twoPeriod19
    ]
  · dsimp
    apply congrArg ZMod.val
    unfold splitOddSourceAt
    rw [
      pow_eq_pow_mod_of_pow_eq_one
        (3 : ZMod 511) (e := K)
        splitOddCommonStageOne_threePeriod511,
      pow_eq_pow_mod_of_pow_eq_one
        (2 : ZMod 511) (e := N)
        splitOddCommonStageOne_twoPeriod511
    ]

/--
target stage 1 signature は `R mod 18`, `B mod 18` だけで決まる。

486² 個について equality だけを見る有限 certificate。
巨大 HashSet は作らない。
-/
private theorem splitOddCommonStageOne_target_reduce :
    ∀ R B : Fin 486,
      splitOddCommonStageOneTargetSignature R.1 B.1 =
        splitOddCommonStageOneTargetSignature
          (R.1 % 18) (B.1 % 18) := by
  native_decide

private def splitOddCommonStageOneTargetSignatures :
    List (ℕ × ℕ) :=
  (List.range 18).flatMap fun R =>
    (List.range 18).map fun B =>
      splitOddCommonStageOneTargetSignature R B

private def splitOddCommonStageOneTargetSet :
    Std.HashSet (ℕ × ℕ) :=
  Std.HashSet.ofList splitOddCommonStageOneTargetSignatures

private theorem splitOddCommonStageOneTargetSet_contains
    (R B : Fin 18) :
    splitOddCommonStageOneTargetSet.contains
        (splitOddCommonStageOneTargetSignature R.1 B.1) = true := by
  have hMem :
      splitOddCommonStageOneTargetSignature R.1 B.1 ∈
        splitOddCommonStageOneTargetSignatures := by
    unfold splitOddCommonStageOneTargetSignatures
    apply List.mem_flatMap.mpr
    refine ⟨R.1, List.mem_range.mpr R.2, ?_⟩
    apply List.mem_map.mpr
    exact ⟨B.1, List.mem_range.mpr B.2, rfl⟩
  simpa only [
    splitOddCommonStageOneTargetSet,
    Std.HashSet.contains_ofList,
    List.contains_eq_mem,
    decide_eq_true_eq
  ] using hMem

/-- stage 1 を通過できる source class は10個。 -/
private def splitOddCommonStageOneSurvivorPairs :
    List (ℕ × ℕ) :=
[
  (1, 5),
  (1, 11),
  (1, 17),
  (3, 2),
  (3, 3),
  (5, 2),
  (5, 6),
  (13, 2),
  (31, 2),
  (35, 1)
]

/--
odd `K` を `K=2j+1` と書けば stage 1 source は18×18状態。
-/
private theorem splitOddCommon_stageOne_source_survivor :
    ∀ J : Fin 18, ∀ N : Fin 18,
      splitOddCommonStageOneTargetSet.contains
          (splitOddCommonStageOneSourceSignature
            (2 * J.1 + 1) N.1) = true →
      (2 * J.1 + 1, N.1) ∈
        splitOddCommonStageOneSurvivorPairs := by
  native_decide

/--
stage 1 で実際に一致する
source `(K mod 36, N mod 18)` と target `(R mod 18, B mod 18)` の対応。

後段で「各 modulus ごとに別の target witness を選ぶ」ことを防ぐため、
source class だけでなく target witness も保持する。
-/
private def splitOddCommonStageOneMatches :
    List ((ℕ × ℕ) × (ℕ × ℕ)) :=
[
  ((1, 5),  (4, 1)),
  ((1, 5),  (5, 17)),
  ((1, 11), (4, 7)),
  ((1, 11), (11, 11)),
  ((1, 17), (4, 13)),
  ((1, 17), (17, 5)),
  ((3, 2),  (2, 3)),
  ((3, 2),  (4, 0)),
  ((3, 2),  (5, 15)),
  ((3, 3),  (4, 1)),
  ((3, 3),  (5, 17)),
  ((5, 2),  (2, 6)),
  ((5, 2),  (8, 12)),
  ((5, 6),  (10, 0)),
  ((5, 6),  (11, 3)),
  ((5, 6),  (14, 15)),
  ((13, 2), (1, 10)),
  ((13, 2), (3, 8)),
  ((13, 2), (5, 6)),
  ((13, 2), (7, 4)),
  ((13, 2), (9, 2)),
  ((13, 2), (11, 0)),
  ((13, 2), (13, 16)),
  ((13, 2), (15, 14)),
  ((13, 2), (17, 12)),
  ((31, 2), (5, 11)),
  ((31, 2), (16, 7)),
  ((35, 1), (1, 0)),
  ((35, 1), (3, 16)),
  ((35, 1), (5, 14)),
  ((35, 1), (7, 12)),
  ((35, 1), (9, 10)),
  ((35, 1), (11, 8)),
  ((35, 1), (13, 6)),
  ((35, 1), (15, 4)),
  ((35, 1), (17, 2))
]

/--
stage 1 survivor と reduced target が実際に一致するなら、
その組は上の36 match のどれか。
-/
private theorem splitOddCommon_stageOne_match :
    ∀ P : Fin splitOddCommonStageOneSurvivorPairs.length,
      ∀ R B : Fin 18,
        splitOddCommonStageOneSourceSignature
            (splitOddCommonStageOneSurvivorPairs.get P).1
            (splitOddCommonStageOneSurvivorPairs.get P).2 =
          splitOddCommonStageOneTargetSignature R.1 B.1 →
        ((splitOddCommonStageOneSurvivorPairs.get P),
          (R.1, B.1)) ∈ splitOddCommonStageOneMatches := by
  native_decide


/-! #### stage 2: mod 163*2593 -/

private def splitOddCommonStageTwoModulus : ℕ := 422659

private theorem splitOddCommonStageTwo_threePeriod :
    (3 : ZMod splitOddCommonStageTwoModulus) ^ 648 = 1 := by
  native_decide

private theorem splitOddCommonStageTwo_twoPeriod :
    (2 : ZMod splitOddCommonStageTwoModulus) ^ 162 = 1 := by
  native_decide

private theorem splitOddCommonStageTwo_source_reduce
    (K N : ℕ) :
    splitOddSourceAt splitOddCommonStageTwoModulus K N =
      splitOddSourceAt splitOddCommonStageTwoModulus
        (K % 648) (N % 162) := by
  unfold splitOddSourceAt
  rw [
    pow_eq_pow_mod_of_pow_eq_one
      (3 : ZMod splitOddCommonStageTwoModulus)
      (e := K) splitOddCommonStageTwo_threePeriod,
    pow_eq_pow_mod_of_pow_eq_one
      (2 : ZMod splitOddCommonStageTwoModulus)
      (e := N) splitOddCommonStageTwo_twoPeriod
  ]

/--
target stage 2 residue は `R mod 162`, `B mod 162` だけに依存する。
-/
private theorem splitOddCommonStageTwo_target_reduce :
    ∀ R B : Fin 486,
      splitOddTargetFastAt
          splitOddCommonStageTwoModulus R.1 B.1 =
        splitOddTargetFastAt
          splitOddCommonStageTwoModulus
          (R.1 % 162) (B.1 % 162) := by
  native_decide

private def splitOddCommonStageTwoTargetValues : List ℕ :=
  (List.range 162).flatMap fun R =>
    (List.range 162).map fun B =>
      (splitOddTargetFastAt
        splitOddCommonStageTwoModulus R B).val

private def splitOddCommonStageTwoTargetSet :
    Std.HashSet ℕ :=
  Std.HashSet.ofList splitOddCommonStageTwoTargetValues

private theorem splitOddCommonStageTwoTargetSet_contains
    (R B : Fin 162) :
    splitOddCommonStageTwoTargetSet.contains
        (splitOddTargetFastAt
          splitOddCommonStageTwoModulus R.1 B.1).val = true := by
  have hMem :
      (splitOddTargetFastAt
        splitOddCommonStageTwoModulus R.1 B.1).val ∈
        splitOddCommonStageTwoTargetValues := by
    unfold splitOddCommonStageTwoTargetValues
    apply List.mem_flatMap.mpr
    refine ⟨R.1, List.mem_range.mpr R.2, ?_⟩
    apply List.mem_map.mpr
    exact ⟨B.1, List.mem_range.mpr B.2, rfl⟩
  simpa only [
    splitOddCommonStageTwoTargetSet,
    Std.HashSet.contains_ofList,
    List.contains_eq_mem,
    decide_eq_true_eq
  ] using hMem

/--
stage 1 survivor の exact lift。
`A<18`, `D<9`。
-/
private def splitOddCommonStageTwoSourcePair
    (P : Fin splitOddCommonStageOneSurvivorPairs.length)
    (A : Fin 18) (D : Fin 9) :
    ℕ × ℕ :=
  ((splitOddCommonStageOneSurvivorPairs.get P).1 + 36 * A.1,
   (splitOddCommonStageOneSurvivorPairs.get P).2 + 18 * D.1)

private def splitOddCommonStageTwoSource
    (P : Fin splitOddCommonStageOneSurvivorPairs.length)
    (A : Fin 18) (D : Fin 9) :
    ZMod splitOddCommonStageTwoModulus :=
  splitOddSourceAt splitOddCommonStageTwoModulus
    (splitOddCommonStageTwoSourcePair P A D).1
    (splitOddCommonStageTwoSourcePair P A D).2

/--
stage 2 の target 全体との単純な residue intersection で残る source class。

ここではまだ stage 1 で一致した「同じ target witness」との対応を
保持していないため、7個ではなく31個残る。
-/
private def splitOddCommonStageTwoCoarseSurvivorPairs :
    List (ℕ × ℕ) :=
[
  (1, 23),
  (1, 77),
  (1, 131),
  (5, 2),
  (5, 6),
  (5, 128),
  (13, 110),
  (39, 146),
  (41, 38),
  (73, 149),
  (75, 147),
  (111, 110),
  (121, 146),
  (147, 147),
  (183, 38),
  (221, 56),
  (221, 128),
  (255, 147),
  (265, 2),
  (337, 128),
  (361, 101),
  (365, 20),
  (397, 41),
  (399, 38),
  (499, 110),
  (503, 73),
  (541, 35),
  (543, 93),
  (579, 92),
  (579, 147),
  (647, 1)
]

/--
stage 1 の10 class ×18×9 liftsだけを見る。
target witness の対応を忘れた coarse sieve なので31 classまで絞る。
-/
private theorem splitOddCommon_stageTwo_source_survivor :
    ∀ P : Fin splitOddCommonStageOneSurvivorPairs.length,
      ∀ A : Fin 18, ∀ D : Fin 9,
        splitOddCommonStageTwoTargetSet.contains
            (splitOddCommonStageTwoSource P A D).val = true →
        splitOddCommonStageTwoSourcePair P A D ∈
          splitOddCommonStageTwoCoarseSurvivorPairs := by
  native_decide


/-!
stage 2 source class と、それと同時に一致できる
`(R mod 162, B mod 162)`。

最初の13件は例外的な有限状態。
`(647,1)` branch は81状態の規則列。
-/
private def splitOddCommonStageTwoMatches :
    List ((ℕ × ℕ) × (ℕ × ℕ)) :=
[
  ((1, 23), (4, 19)),
  ((1, 23), (23, 143)),
  ((1, 77), (4, 73)),
  ((1, 77), (77, 89)),
  ((1, 131), (4, 127)),
  ((1, 131), (131, 35)),
  ((5, 2), (2, 6)),
  ((5, 2), (8, 156)),
  ((5, 6), (10, 0)),
  ((5, 6), (11, 3)),
  ((5, 6), (14, 159)),
  ((397, 41), (59, 53)),
  ((397, 41), (112, 109))
] ++
  (List.range 81).map fun q =>
    ((647, 1),
      (2 * q + 1, (162 - 2 * q) % 162))

/--
stage 1 で一致した target witness を保持したまま stage 2 へ持ち上げる。

coarse survivor と stage-1 match が同じ source residue class を表し、
stage 2 でも同じ target witness の lift と一致するなら、
その source/target pair は94個の stage-2 match table に入る。
-/
private theorem splitOddCommon_stageTwo_compatible_match :
    ∀ S : Fin splitOddCommonStageTwoCoarseSurvivorPairs.length,
      ∀ Q : Fin splitOddCommonStageOneMatches.length,
      ∀ C E : Fin 9,
        (splitOddCommonStageOneMatches.get Q).1 =
          ((splitOddCommonStageTwoCoarseSurvivorPairs.get S).1 % 36,
           (splitOddCommonStageTwoCoarseSurvivorPairs.get S).2 % 18) →
        splitOddSourceAt
            splitOddCommonStageTwoModulus
            (splitOddCommonStageTwoCoarseSurvivorPairs.get S).1
            (splitOddCommonStageTwoCoarseSurvivorPairs.get S).2 =
          splitOddTargetFastAt
            splitOddCommonStageTwoModulus
            ((splitOddCommonStageOneMatches.get Q).2.1 + 18 * C.1)
            ((splitOddCommonStageOneMatches.get Q).2.2 + 18 * E.1) →
        ((splitOddCommonStageTwoCoarseSurvivorPairs.get S),
          ((splitOddCommonStageOneMatches.get Q).2.1 + 18 * C.1,
           (splitOddCommonStageOneMatches.get Q).2.2 + 18 * E.1)) ∈
            splitOddCommonStageTwoMatches := by
  native_decide


/-! #### final stage: mod 487 -/

private def splitOddCommonFinalSource
    (Q : Fin splitOddCommonStageTwoMatches.length)
    (A D : Fin 3) :
    ZMod 487 :=
  splitOddSourceAt 487
    ((splitOddCommonStageTwoMatches.get Q).1.1 + 648 * A.1)
    ((splitOddCommonStageTwoMatches.get Q).1.2 + 162 * D.1)

private def splitOddCommonFinalTarget
    (Q : Fin splitOddCommonStageTwoMatches.length)
    (C E : Fin 3) :
    ZMod 487 :=
  splitOddTargetFastAt 487
    ((splitOddCommonStageTwoMatches.get Q).2.1 + 162 * C.1)
    ((splitOddCommonStageTwoMatches.get Q).2.2 + 162 * E.1)

/--
94 patterns ×3⁴ lifts = 7614状態。

mod 487 まで一致できる source pair は最終的に4個だけ。
-/
private theorem splitOddCommon_final_classification :
    ∀ Q : Fin splitOddCommonStageTwoMatches.length,
      ∀ A D C E : Fin 3,
        splitOddCommonFinalSource Q A D =
          splitOddCommonFinalTarget Q C E →
        (((splitOddCommonStageTwoMatches.get Q).1.1 +
              648 * A.1 = 1 ∧
            (splitOddCommonStageTwoMatches.get Q).1.2 +
              162 * D.1 = 23) ∨
         ((splitOddCommonStageTwoMatches.get Q).1.1 +
              648 * A.1 = 1 ∧
            (splitOddCommonStageTwoMatches.get Q).1.2 +
              162 * D.1 = 185) ∨
         ((splitOddCommonStageTwoMatches.get Q).1.1 +
              648 * A.1 = 1 ∧
            (splitOddCommonStageTwoMatches.get Q).1.2 +
              162 * D.1 = 347) ∨
         ((splitOddCommonStageTwoMatches.get Q).1.1 +
              648 * A.1 = 1943 ∧
            (splitOddCommonStageTwoMatches.get Q).1.2 +
              162 * D.1 = 1)) := by
  native_decide

/--
common modulus 上の equality を、その任意の divisor へ射影する。

stage 1 / stage 2 / final で同じ `ZMod.castHom` boilerplate を
繰り返さないための共通補助定理。
-/
private theorem splitOddCommon_project_common
    {m : ℕ}
    (hDvd : m ∣ splitOddCommonModulus)
    (K N R B : ℕ)
    (hCommonEq :
      splitOddSourceAt splitOddCommonModulus K N =
        splitOddTargetFastAt splitOddCommonModulus R B) :
    splitOddSourceAt m K N =
      splitOddTargetFastAt m R B := by
  have hRaw :=
    congrArg
      (ZMod.castHom hDvd (ZMod m))
      hCommonEq
  rw [
    splitOddSourceAt_project_divisor hDvd,
    splitOddTargetFastAt_project_divisor hDvd
  ] at hRaw
  exact hRaw

/--
HashSet membership から、同じ target witness `(R,B)` を取り出し、
common / complement の両 equality を同時に得る。
-/
private theorem splitOddCommon_target_witness_of_contains
    (K : Fin 1944)
    (N : Fin 486)
    (hContains :
      splitOddCommonTargetSignatureSet.contains
          (splitOddCommonSourceSignature K.1 N.1) = true) :
    ∃ RF BF : Fin 486,
      splitOddSourceAt
          splitOddCommonModulus K.1 N.1 =
        splitOddTargetFastAt
          splitOddCommonModulus RF.1 BF.1 ∧
      splitOddSourceAt
          splitOddComplementModulus K.1 N.1 =
        splitOddTargetFastAt
          splitOddComplementModulus RF.1 BF.1 := by
  have hMem :
      splitOddCommonSourceSignature K.1 N.1 ∈
        splitOddCommonTargetSignatures := by
    simpa only [
      splitOddCommonTargetSignatureSet,
      Std.HashSet.contains_ofList,
      List.contains_eq_mem,
      decide_eq_true_eq
    ] using hContains
  unfold splitOddCommonTargetSignatures at hMem
  rcases List.mem_flatMap.mp hMem with
    ⟨R, hR, hMemR⟩
  rcases List.mem_map.mp hMemR with
    ⟨B, hB, hVal⟩
  let RF : Fin 486 :=
    ⟨R, List.mem_range.mp hR⟩
  let BF : Fin 486 :=
    ⟨B, List.mem_range.mp hB⟩
  have hSignature :
      splitOddCommonSourceSignature K.1 N.1 =
        splitOddCommonTargetSignature RF.1 BF.1 := by
    dsimp [RF, BF]
    exact hVal.symm
  have hCommonVal :=
    congrArg Prod.fst hSignature
  have hComplementVal :=
    congrArg Prod.snd hSignature
  have hCommonEq :
      splitOddSourceAt
          splitOddCommonModulus K.1 N.1 =
        splitOddTargetFastAt
          splitOddCommonModulus RF.1 BF.1 := by
    apply ZMod.val_injective splitOddCommonModulus
    simpa [
      splitOddCommonSourceSignature,
      splitOddCommonTargetSignature
    ] using hCommonVal
  have hComplementEq :
      splitOddSourceAt
          splitOddComplementModulus K.1 N.1 =
        splitOddTargetFastAt
          splitOddComplementModulus RF.1 BF.1 := by
    apply ZMod.val_injective splitOddComplementModulus
    simpa [
      splitOddCommonSourceSignature,
      splitOddCommonTargetSignature
    ] using hComplementVal
  exact ⟨RF, BF, hCommonEq, hComplementEq⟩

/--
stage 1: mod 19 + complement modulus で source survivor を決め、
同じ target witness の mod 18 residue class を保存した match を作る。
-/
private theorem splitOddCommon_stageOne_match_of_witness
    (K : Fin 1944)
    (N RF BF : Fin 486)
    (hKodd : K.1 % 2 = 1)
    (hCommonEq :
      splitOddSourceAt
          splitOddCommonModulus K.1 N.1 =
        splitOddTargetFastAt
          splitOddCommonModulus RF.1 BF.1)
    (hComplementEq :
      splitOddSourceAt
          splitOddComplementModulus K.1 N.1 =
        splitOddTargetFastAt
          splitOddComplementModulus RF.1 BF.1) :
    ∃ (P : Fin splitOddCommonStageOneSurvivorPairs.length)
      (Q1 : Fin splitOddCommonStageOneMatches.length),
      splitOddCommonStageOneSurvivorPairs.get P =
          (K.1 % 36, N.1 % 18) ∧
      splitOddCommonStageOneMatches.get Q1 =
          ((K.1 % 36, N.1 % 18),
           (RF.1 % 18, BF.1 % 18)) := by
  have hDvd19 :
      19 ∣ splitOddCommonModulus := by
    norm_num [splitOddCommonModulus]
  have h19 :
      splitOddSourceAt 19 K.1 N.1 =
        splitOddTargetFastAt 19 RF.1 BF.1 :=
    splitOddCommon_project_common
      hDvd19 K.1 N.1 RF.1 BF.1 hCommonEq
  have hStageOneSignature :
      splitOddCommonStageOneSourceSignature K.1 N.1 =
        splitOddCommonStageOneTargetSignature RF.1 BF.1 := by
    apply Prod.ext
    · exact congrArg ZMod.val h19
    · exact congrArg ZMod.val hComplementEq
  have hKParity36 :
      (K.1 % 36) % 2 = 1 := by
    have hmod :
        (K.1 % 36) % 2 = K.1 % 2 := by
      simp only [Nat.reduceDvd, Nat.mod_mod_of_dvd]
    rw [hmod, hKodd]
  let JR : Fin 18 :=
    ⟨(K.1 % 36) / 2, by omega⟩
  let NR : Fin 18 :=
    ⟨N.1 % 18, Nat.mod_lt _ (by norm_num)⟩
  have hKRep :
      K.1 % 36 = 2 * JR.1 + 1 := by
    dsimp [JR]
    have h := Nat.mod_add_div (K.1 % 36) 2
    omega
  have hSourceOneReduce :
      splitOddCommonStageOneSourceSignature K.1 N.1 =
        splitOddCommonStageOneSourceSignature
          (2 * JR.1 + 1) NR.1 := by
    calc
      splitOddCommonStageOneSourceSignature K.1 N.1 =
          splitOddCommonStageOneSourceSignature
            (K.1 % 36) (N.1 % 18) :=
        splitOddCommonStageOne_source_reduce K.1 N.1
      _ =
          splitOddCommonStageOneSourceSignature
            (2 * JR.1 + 1) NR.1 := by
        rw [hKRep]
  let RR1 : Fin 18 :=
    ⟨RF.1 % 18, Nat.mod_lt _ (by norm_num)⟩
  let BR1 : Fin 18 :=
    ⟨BF.1 % 18, Nat.mod_lt _ (by norm_num)⟩
  have hTargetOneReduce :
      splitOddCommonStageOneTargetSignature RF.1 BF.1 =
        splitOddCommonStageOneTargetSignature
          RR1.1 BR1.1 := by
    simpa [RR1, BR1] using
      splitOddCommonStageOne_target_reduce RF BF
  have hReducedOne :
      splitOddCommonStageOneSourceSignature
          (2 * JR.1 + 1) NR.1 =
        splitOddCommonStageOneTargetSignature
          RR1.1 BR1.1 := by
    calc
      splitOddCommonStageOneSourceSignature
          (2 * JR.1 + 1) NR.1 =
        splitOddCommonStageOneSourceSignature K.1 N.1 :=
          hSourceOneReduce.symm
      _ =
        splitOddCommonStageOneTargetSignature RF.1 BF.1 :=
          hStageOneSignature
      _ =
        splitOddCommonStageOneTargetSignature RR1.1 BR1.1 :=
          hTargetOneReduce
  have hTargetOneMem :=
    splitOddCommonStageOneTargetSet_contains RR1 BR1
  rw [← hReducedOne] at hTargetOneMem
  have hSurvivorOne :
      (2 * JR.1 + 1, NR.1) ∈
        splitOddCommonStageOneSurvivorPairs :=
    splitOddCommon_stageOne_source_survivor
      JR NR hTargetOneMem
  obtain ⟨P, hP⟩ :=
    List.get_of_mem hSurvivorOne
  have hPActual :
      splitOddCommonStageOneSurvivorPairs.get P =
        (K.1 % 36, N.1 % 18) := by
    rw [hP]
    apply Prod.ext
    · exact hKRep.symm
    · rfl
  have hStageOneMatchEq :
      splitOddCommonStageOneSourceSignature
          (splitOddCommonStageOneSurvivorPairs.get P).1
          (splitOddCommonStageOneSurvivorPairs.get P).2 =
        splitOddCommonStageOneTargetSignature RR1.1 BR1.1 := by
    rw [hP]
    exact hReducedOne
  have hStageOneMatch :
      ((splitOddCommonStageOneSurvivorPairs.get P),
        (RR1.1, BR1.1)) ∈ splitOddCommonStageOneMatches :=
    splitOddCommon_stageOne_match
      P RR1 BR1 hStageOneMatchEq
  obtain ⟨Q1, hQ1⟩ :=
    List.get_of_mem hStageOneMatch
  have hQ1Actual :
      splitOddCommonStageOneMatches.get Q1 =
        ((K.1 % 36, N.1 % 18),
         (RF.1 % 18, BF.1 % 18)) := by
    rw [hQ1, hPActual]
  exact ⟨P, Q1, hPActual, hQ1Actual⟩

/--
stage 2 の source 側 coarse lift。

stage 1 survivor `(K mod 36, N mod 18)` から
`(K mod 648, N mod 162)` の coarse survivor を得る。
さらに、同じ target witness を mod 162 へ縮約した exact equality も返し、
次の exact-match 段階で common modulus からの射影をやり直さない。
-/
private theorem splitOddCommon_stageTwo_coarse_of_stageOne
    (K : Fin 1944)
    (N RF BF : Fin 486)
    (P : Fin splitOddCommonStageOneSurvivorPairs.length)
    (hCommonEq :
      splitOddSourceAt
          splitOddCommonModulus K.1 N.1 =
        splitOddTargetFastAt
          splitOddCommonModulus RF.1 BF.1)
    (hPActual :
      splitOddCommonStageOneSurvivorPairs.get P =
        (K.1 % 36, N.1 % 18)) :
    ∃ S : Fin splitOddCommonStageTwoCoarseSurvivorPairs.length,
      splitOddCommonStageTwoCoarseSurvivorPairs.get S =
          (K.1 % 648, N.1 % 162) ∧
      splitOddSourceAt
          splitOddCommonStageTwoModulus
          (K.1 % 648) (N.1 % 162) =
        splitOddTargetFastAt
          splitOddCommonStageTwoModulus
          (RF.1 % 162) (BF.1 % 162) := by
  have hDvdStageTwo :
      splitOddCommonStageTwoModulus ∣
        splitOddCommonModulus := by
    norm_num [
      splitOddCommonStageTwoModulus,
      splitOddCommonModulus
    ]
  have hStageTwoExact :
      splitOddSourceAt
          splitOddCommonStageTwoModulus K.1 N.1 =
        splitOddTargetFastAt
          splitOddCommonStageTwoModulus RF.1 BF.1 :=
    splitOddCommon_project_common
      hDvdStageTwo K.1 N.1 RF.1 BF.1 hCommonEq
  let A : Fin 18 :=
    ⟨(K.1 % 648) / 36, by omega⟩
  let D : Fin 9 :=
    ⟨(N.1 % 162) / 18, by omega⟩
  have hKmod36 :
      (K.1 % 648) % 36 = K.1 % 36 := by
    simp only [Nat.reduceDvd, Nat.mod_mod_of_dvd]
  have hNmod18 :
      (N.1 % 162) % 18 = N.1 % 18 := by
    simp only [Nat.reduceDvd, Nat.mod_mod_of_dvd]
  have hK648Exact :
      K.1 % 648 =
        (splitOddCommonStageOneSurvivorPairs.get P).1 +
          36 * A.1 := by
    rw [hPActual]
    dsimp [A]
    have h :=
      Nat.mod_add_div (K.1 % 648) 36
    rw [hKmod36] at h
    omega
  have hN162Exact :
      N.1 % 162 =
        (splitOddCommonStageOneSurvivorPairs.get P).2 +
          18 * D.1 := by
    rw [hPActual]
    dsimp [D]
    have h :=
      Nat.mod_add_div (N.1 % 162) 18
    rw [hNmod18] at h
    omega
  let RR2 : Fin 162 :=
    ⟨RF.1 % 162, Nat.mod_lt _ (by norm_num)⟩
  let BR2 : Fin 162 :=
    ⟨BF.1 % 162, Nat.mod_lt _ (by norm_num)⟩
  have hTargetTwoReduce :
      splitOddTargetFastAt
          splitOddCommonStageTwoModulus RF.1 BF.1 =
        splitOddTargetFastAt
          splitOddCommonStageTwoModulus RR2.1 BR2.1 := by
    simpa [RR2, BR2] using
      splitOddCommonStageTwo_target_reduce RF BF
  have hReducedStageTwoExact :
      splitOddSourceAt
          splitOddCommonStageTwoModulus
          (K.1 % 648) (N.1 % 162) =
        splitOddTargetFastAt
          splitOddCommonStageTwoModulus
          (RF.1 % 162) (BF.1 % 162) := by
    calc
      splitOddSourceAt
          splitOddCommonStageTwoModulus
          (K.1 % 648) (N.1 % 162) =
        splitOddSourceAt
          splitOddCommonStageTwoModulus K.1 N.1 :=
        (splitOddCommonStageTwo_source_reduce K.1 N.1).symm
      _ =
        splitOddTargetFastAt
          splitOddCommonStageTwoModulus RF.1 BF.1 :=
        hStageTwoExact
      _ =
        splitOddTargetFastAt
          splitOddCommonStageTwoModulus RR2.1 BR2.1 :=
        hTargetTwoReduce
      _ =
        splitOddTargetFastAt
          splitOddCommonStageTwoModulus
          (RF.1 % 162) (BF.1 % 162) := by
        rfl
  have hReducedTwo :
      splitOddCommonStageTwoSource P A D =
        splitOddTargetFastAt
          splitOddCommonStageTwoModulus RR2.1 BR2.1 := by
    calc
      splitOddCommonStageTwoSource P A D =
          splitOddSourceAt
            splitOddCommonStageTwoModulus
            (K.1 % 648) (N.1 % 162) := by
        unfold splitOddCommonStageTwoSource
        unfold splitOddCommonStageTwoSourcePair
        rw [← hK648Exact, ← hN162Exact]
      _ =
          splitOddTargetFastAt
            splitOddCommonStageTwoModulus
            (RF.1 % 162) (BF.1 % 162) :=
        hReducedStageTwoExact
      _ =
          splitOddTargetFastAt
            splitOddCommonStageTwoModulus RR2.1 BR2.1 := by
        rfl
  have hTargetTwoMem :=
    splitOddCommonStageTwoTargetSet_contains RR2 BR2
  have hValTwo :=
    congrArg ZMod.val hReducedTwo
  rw [← hValTwo] at hTargetTwoMem
  have hSurvivorTwo :
      splitOddCommonStageTwoSourcePair P A D ∈
        splitOddCommonStageTwoCoarseSurvivorPairs :=
    splitOddCommon_stageTwo_source_survivor
      P A D hTargetTwoMem
  obtain ⟨S, hS⟩ :=
    List.get_of_mem hSurvivorTwo
  have hSActual :
      splitOddCommonStageTwoCoarseSurvivorPairs.get S =
        (K.1 % 648, N.1 % 162) := by
    rw [hS]
    unfold splitOddCommonStageTwoSourcePair
    apply Prod.ext
    · exact hK648Exact.symm
    · exact hN162Exact.symm
  exact ⟨S, hSActual, hReducedStageTwoExact⟩

/--
stage 2 の target 側 exact lift。

stage 1 で保存した target residue class `(R mod 18, B mod 18)` を
同じ witness の `(R mod 162, B mod 162)` へ持ち上げ、
coarse 段階から受け取った reduced equality を使って stage 2 match を作る。
-/
private theorem splitOddCommon_stageTwo_match_of_coarse
    (K : Fin 1944)
    (N RF BF : Fin 486)
    (Q1 : Fin splitOddCommonStageOneMatches.length)
    (S : Fin splitOddCommonStageTwoCoarseSurvivorPairs.length)
    (hQ1Actual :
      splitOddCommonStageOneMatches.get Q1 =
        ((K.1 % 36, N.1 % 18),
         (RF.1 % 18, BF.1 % 18)))
    (hSActual :
      splitOddCommonStageTwoCoarseSurvivorPairs.get S =
        (K.1 % 648, N.1 % 162))
    (hReducedStageTwoExact :
      splitOddSourceAt
          splitOddCommonStageTwoModulus
          (K.1 % 648) (N.1 % 162) =
        splitOddTargetFastAt
          splitOddCommonStageTwoModulus
          (RF.1 % 162) (BF.1 % 162)) :
    ∃ Q2 : Fin splitOddCommonStageTwoMatches.length,
      splitOddCommonStageTwoMatches.get Q2 =
        ((K.1 % 648, N.1 % 162),
         (RF.1 % 162, BF.1 % 162)) := by
  let C : Fin 9 :=
    ⟨(RF.1 % 162) / 18, by omega⟩
  let E : Fin 9 :=
    ⟨(BF.1 % 162) / 18, by omega⟩
  have hRmod18 :
      (RF.1 % 162) % 18 = RF.1 % 18 := by
    simp only [Nat.reduceDvd, Nat.mod_mod_of_dvd]
  have hBmod18 :
      (BF.1 % 162) % 18 = BF.1 % 18 := by
    simp only [Nat.reduceDvd, Nat.mod_mod_of_dvd]
  have hR162 :
      RF.1 % 162 =
        RF.1 % 18 + 18 * C.1 := by
    dsimp [C]
    have h := Nat.mod_add_div (RF.1 % 162) 18
    rw [hRmod18] at h
    omega
  have hB162 :
      BF.1 % 162 =
        BF.1 % 18 + 18 * E.1 := by
    dsimp [E]
    have h := Nat.mod_add_div (BF.1 % 162) 18
    rw [hBmod18] at h
    omega
  have hCompat :
      (splitOddCommonStageOneMatches.get Q1).1 =
        ((splitOddCommonStageTwoCoarseSurvivorPairs.get S).1 % 36,
         (splitOddCommonStageTwoCoarseSurvivorPairs.get S).2 % 18) := by
    rw [hQ1Actual, hSActual]
    apply Prod.ext <;>
      simp only [Nat.reduceDvd, Nat.mod_mod_of_dvd]
  have hCompatibleEq :
      splitOddSourceAt
          splitOddCommonStageTwoModulus
          (splitOddCommonStageTwoCoarseSurvivorPairs.get S).1
          (splitOddCommonStageTwoCoarseSurvivorPairs.get S).2 =
        splitOddTargetFastAt
          splitOddCommonStageTwoModulus
          ((splitOddCommonStageOneMatches.get Q1).2.1 + 18 * C.1)
          ((splitOddCommonStageOneMatches.get Q1).2.2 + 18 * E.1) := by
    rw [hSActual, hQ1Actual]
    dsimp
    rw [← hR162, ← hB162]
    exact hReducedStageTwoExact
  have hMatchTwo :
      ((splitOddCommonStageTwoCoarseSurvivorPairs.get S),
        ((splitOddCommonStageOneMatches.get Q1).2.1 + 18 * C.1,
         (splitOddCommonStageOneMatches.get Q1).2.2 + 18 * E.1)) ∈
          splitOddCommonStageTwoMatches :=
    splitOddCommon_stageTwo_compatible_match
      S Q1 C E hCompat hCompatibleEq
  obtain ⟨Q2, hQ2⟩ :=
    List.get_of_mem hMatchTwo
  have hQ2Actual :
      splitOddCommonStageTwoMatches.get Q2 =
        ((K.1 % 648, N.1 % 162),
         (RF.1 % 162, BF.1 % 162)) := by
    rw [hQ2, hSActual, hQ1Actual]
    dsimp
    rw [← hR162, ← hB162]
  exact ⟨Q2, hQ2Actual⟩

/--
final stage: mod 487 で残った上位 base-3 digit を分類し、
元の `(K,N)` の4候補へ戻す。
-/
private theorem splitOddCommon_finish_classification
    (K : Fin 1944)
    (N RF BF : Fin 486)
    (Q2 : Fin splitOddCommonStageTwoMatches.length)
    (hCommonEq :
      splitOddSourceAt
          splitOddCommonModulus K.1 N.1 =
        splitOddTargetFastAt
          splitOddCommonModulus RF.1 BF.1)
    (hQ2Actual :
      splitOddCommonStageTwoMatches.get Q2 =
        ((K.1 % 648, N.1 % 162),
         (RF.1 % 162, BF.1 % 162))) :
    (K.1 = 1 ∧ N.1 = 23) ∨
    (K.1 = 1 ∧ N.1 = 185) ∨
    (K.1 = 1 ∧ N.1 = 347) ∨
    (K.1 = 1943 ∧ N.1 = 1) := by
  have hDvd487 :
      487 ∣ splitOddCommonModulus := by
    norm_num [splitOddCommonModulus]
  have h487 :
      splitOddSourceAt 487 K.1 N.1 =
        splitOddTargetFastAt 487 RF.1 BF.1 :=
    splitOddCommon_project_common
      hDvd487 K.1 N.1 RF.1 BF.1 hCommonEq
  let KA : Fin 3 :=
    ⟨K.1 / 648, by omega⟩
  let ND : Fin 3 :=
    ⟨N.1 / 162, by omega⟩
  let RC : Fin 3 :=
    ⟨RF.1 / 162, by omega⟩
  let BE : Fin 3 :=
    ⟨BF.1 / 162, by omega⟩
  have hKFull :
      K.1 =
        K.1 % 648 + 648 * KA.1 := by
    dsimp [KA]
    exact (Nat.mod_add_div K.1 648).symm
  have hNFull :
      N.1 =
        N.1 % 162 + 162 * ND.1 := by
    dsimp [ND]
    exact (Nat.mod_add_div N.1 162).symm
  have hRFull :
      RF.1 =
        RF.1 % 162 + 162 * RC.1 := by
    dsimp [RC]
    exact (Nat.mod_add_div RF.1 162).symm
  have hBFull :
      BF.1 =
        BF.1 % 162 + 162 * BE.1 := by
    dsimp [BE]
    exact (Nat.mod_add_div BF.1 162).symm
  have hFinalEq :
      splitOddCommonFinalSource Q2 KA ND =
        splitOddCommonFinalTarget Q2 RC BE := by
    unfold splitOddCommonFinalSource
    unfold splitOddCommonFinalTarget
    rw [hQ2Actual]
    dsimp
    rw [
      ← hKFull,
      ← hNFull,
      ← hRFull,
      ← hBFull
    ]
    exact h487
  have hClass :=
    splitOddCommon_final_classification
      Q2 KA ND RC BE hFinalEq
  rw [hQ2Actual] at hClass
  rw [← hKFull, ← hNFull] at hClass
  exact hClass

/--
odd source state の署名が target 署名集合に現れるのは4状態だけ。

探索は `(K,N)` の二変数と target HashSet membership に縮約され、
`K,N,R,B` の直積は作らない。

証明は
1. target witness の復元
2. stage 1 match
3. stage 2 coarse lift
4. stage 2 exact target lift
5. final mod 487 classification
の順に進む。
-/
private theorem splitOddCommon_source_pair_classification :
    ∀ K : Fin 1944, ∀ N : Fin 486,
      K.1 % 2 = 1 →
      splitOddCommonTargetSignatureSet.contains
          (splitOddCommonSourceSignature K.1 N.1) = true →
      (K.1 = 1 ∧ N.1 = 23) ∨
      (K.1 = 1 ∧ N.1 = 185) ∨
      (K.1 = 1 ∧ N.1 = 347) ∨
      (K.1 = 1943 ∧ N.1 = 1) := by
  intro K N hKodd hContains
  obtain ⟨RF, BF, hCommonEq, hComplementEq⟩ :=
    splitOddCommon_target_witness_of_contains
      K N hContains
  obtain ⟨P, Q1, hPActual, hQ1Actual⟩ :=
    splitOddCommon_stageOne_match_of_witness
      K N RF BF hKodd hCommonEq hComplementEq
  obtain ⟨S, hSActual, hReducedStageTwoExact⟩ :=
    splitOddCommon_stageTwo_coarse_of_stageOne
      K N RF BF P hCommonEq hPActual
  obtain ⟨Q2, hQ2Actual⟩ :=
    splitOddCommon_stageTwo_match_of_coarse
      K N RF BF Q1 S hQ1Actual hSActual hReducedStageTwoExact
  exact
    splitOddCommon_finish_classification
      K N RF BF Q2 hCommonEq hQ2Actual


/-- 4つの source state が full unit modulus 上で与える第1共通値。 -/
private theorem splitOddSourceQ_value_1_23 :
    (splitOddSourceQ 1 23).val = splitOddV1 := by
  decide

/-- 4つの source state が full unit modulus 上で与える第2共通値。 -/
private theorem splitOddSourceQ_value_1_185 :
    (splitOddSourceQ 1 185).val = splitOddV2 := by
  native_decide

/-- 4つの source state が full unit modulus 上で与える第3共通値。 -/
private theorem splitOddSourceQ_value_1_347 :
    (splitOddSourceQ 1 347).val = splitOddV3 := by
  native_decide

/-- sentinel 側 source state が full unit modulus 上で与える第4共通値。 -/
private theorem splitOddSourceQ_value_1943_1 :
    (splitOddSourceQ 1943 1).val = splitOddV4 := by
  native_decide

/--
target classification 用小 modulus 上で、高速 endpoint exponent を使った residue。
-/
private def splitOddTargetClassFastResidue (R B : ℕ) : ZMod splitOddTargetClassModulus :=
  splitOddTargetFastAt splitOddTargetClassModulus R B

/--
小 modulus 上で `V1..V4` の residue に一致する genuine target state は6状態だけ。

`R,B` の236196状態だけを調べ、`T` は高速 endpoint lookup で復元する。
-/
private theorem splitOddTarget_fast_smallMod_classification :
    ∀ R B : Fin 486,
      let T :=
        logTwoMod729Fast (splitOddEndpointTarget729 R.1 B.1).val
      T < 486 →
      let w := (splitOddTargetClassFastResidue R.1 B.1).val
      (w = splitOddV1 % splitOddTargetClassModulus ∨
       w = splitOddV2 % splitOddTargetClassModulus ∨
       w = splitOddV3 % splitOddTargetClassModulus ∨
       w = splitOddV4 % splitOddTargetClassModulus) →
      (((R.1 = 4 ∧ T = 21 ∧ B.1 = 19) ∨
        (R.1 = 23 ∧ T = 2 ∧ B.1 = 467)) ∨
       ((R.1 = 4 ∧ T = 183 ∧ B.1 = 181) ∨
        (R.1 = 185 ∧ T = 2 ∧ B.1 = 305)) ∨
       ((R.1 = 4 ∧ T = 345 ∧ B.1 = 343) ∨
        (R.1 = 347 ∧ T = 2 ∧ B.1 = 143))) := by
  native_decide

/-- target state `(R,B)=(4,19)` の full residue は `V1`。 -/
private theorem splitOddTargetQ_value_4_19 :
    (splitOddTargetQ 4 19).val = splitOddV1 := by
  native_decide

/-- target state `(R,B)=(23,467)` の full residue は `V1`。 -/
private theorem splitOddTargetQ_value_23_467 :
    (splitOddTargetQ 23 467).val = splitOddV1 := by
  native_decide

/-- target state `(R,B)=(4,181)` の full residue は `V2`。 -/
private theorem splitOddTargetQ_value_4_181 :
    (splitOddTargetQ 4 181).val = splitOddV2 := by
  native_decide

/-- target state `(R,B)=(185,305)` の full residue は `V2`。 -/
private theorem splitOddTargetQ_value_185_305 :
    (splitOddTargetQ 185 305).val = splitOddV2 := by
  native_decide

/-- target state `(R,B)=(4,343)` の full residue は `V3`。 -/
private theorem splitOddTargetQ_value_4_343 :
    (splitOddTargetQ 4 343).val = splitOddV3 := by
  native_decide

/-- target state `(R,B)=(347,143)` の full residue は `V3`。 -/
private theorem splitOddTargetQ_value_347_143 :
    (splitOddTargetQ 347 143).val = splitOddV3 := by
  native_decide

/--
source/target に共通して現れる full residue と source state を同時に4型へ分類する。

full modulus の equality を `splitOddCommonModulus` と `511` の署名へ射影し、
target 署名 HashSet に入る odd source state が4状態しかないことを使う。
一度得た `(K,N)` の情報を値だけへ弱めず、そのまま後段へ渡す。
-/
private theorem splitOdd_common_source_classification
    (K : Fin 1944) (N R B : Fin 486)
    (hKodd : K.1 % 2 = 1)
    (hEq :
      splitOddSourceQ K.1 N.1 =
        splitOddTargetQ R.1 B.1) :
    ((splitOddSourceQ K.1 N.1).val = splitOddV1 ∧
      K.1 = 1 ∧ N.1 = 23) ∨
    ((splitOddSourceQ K.1 N.1).val = splitOddV2 ∧
      K.1 = 1 ∧ N.1 = 185) ∨
    ((splitOddSourceQ K.1 N.1).val = splitOddV3 ∧
      K.1 = 1 ∧ N.1 = 347) ∨
    ((splitOddSourceQ K.1 N.1).val = splitOddV4 ∧
      K.1 = 1943 ∧ N.1 = 1) := by
  have hFast :
      splitOddEndpointL R.1 B.1 =
        logTwoMod729Fast (splitOddEndpointTarget729 R.1 B.1).val :=
    splitOddEndpointL_eq_fast R.1 B.1
  have hDvdCommon :
      splitOddCommonModulus ∣ twoHoleUnitModulus := by
    norm_num [splitOddCommonModulus, twoHoleUnitModulus]
  have hDvdComplement :
      splitOddComplementModulus ∣ twoHoleUnitModulus := by
    norm_num [splitOddComplementModulus, twoHoleUnitModulus]
  have hCommonRaw :=
    congrArg
      (ZMod.castHom hDvdCommon (ZMod splitOddCommonModulus))
      hEq
  have hCommon :
      splitOddSourceAt splitOddCommonModulus K.1 N.1 =
        splitOddTargetFastAt splitOddCommonModulus R.1 B.1 := by
    rw [splitOddSourceQ_project hDvdCommon,
        splitOddTargetQ_project hDvdCommon] at hCommonRaw
    simpa [splitOddTargetFastAt, hFast] using hCommonRaw
  have hComplementRaw :=
    congrArg
      (ZMod.castHom hDvdComplement (ZMod splitOddComplementModulus))
      hEq
  have hComplement :
      splitOddSourceAt splitOddComplementModulus K.1 N.1 =
        splitOddTargetFastAt splitOddComplementModulus R.1 B.1 := by
    rw [splitOddSourceQ_project hDvdComplement,
        splitOddTargetQ_project hDvdComplement] at hComplementRaw
    simpa [splitOddTargetFastAt, hFast] using hComplementRaw
  have hSignature :
      splitOddCommonSourceSignature K.1 N.1 =
        splitOddCommonTargetSignature R.1 B.1 := by
    apply Prod.ext
    · exact congrArg ZMod.val hCommon
    · exact congrArg ZMod.val hComplement
  have hContains :
      splitOddCommonTargetSignatureSet.contains
          (splitOddCommonSourceSignature K.1 N.1) = true := by
    rw [hSignature]
    exact splitOddCommonTargetSignatureSet_contains R B
  have hPairs :=
    splitOddCommon_source_pair_classification K N hKodd hContains
  rcases hPairs with h | h | h | h
  · exact Or.inl
      ⟨by simpa [h.1, h.2] using splitOddSourceQ_value_1_23,
       h.1, h.2⟩
  · exact Or.inr (Or.inl
      ⟨by simpa [h.1, h.2] using splitOddSourceQ_value_1_185,
       h.1, h.2⟩)
  · exact Or.inr (Or.inr (Or.inl
      ⟨by simpa [h.1, h.2] using splitOddSourceQ_value_1_347,
       h.1, h.2⟩))
  · exact Or.inr (Or.inr (Or.inr
      ⟨by simpa [h.1, h.2] using splitOddSourceQ_value_1943_1,
       h.1, h.2⟩))

/--
target 側の6型分類。

構成的 `splitOddEndpointL` を高速 lookup と同一視し、
`19*163*487` 上の residue だけで `(R,T,B)` を6状態へ絞る。
最後に6個の closed full-residue lemma で `V1,V2,V3` を復元する。
-/
private theorem splitOddTarget_classification :
    ∀ R B : Fin 486,
      let T := splitOddEndpointL R.1 B.1
      T < 486 →
      let v := (splitOddTargetQ R.1 B.1).val
      (v = splitOddV1 ∨ v = splitOddV2 ∨
        v = splitOddV3 ∨ v = splitOddV4) →
      (v = splitOddV1 ∧
        ((R.1 = 4 ∧ T = 21 ∧ B.1 = 19) ∨
         (R.1 = 23 ∧ T = 2 ∧ B.1 = 467))) ∨
      (v = splitOddV2 ∧
        ((R.1 = 4 ∧ T = 183 ∧ B.1 = 181) ∨
         (R.1 = 185 ∧ T = 2 ∧ B.1 = 305))) ∨
      (v = splitOddV3 ∧
        ((R.1 = 4 ∧ T = 345 ∧ B.1 = 343) ∨
         (R.1 = 347 ∧ T = 2 ∧ B.1 = 143))) := by
  intro R B
  dsimp
  intro hTLt hAllowed
  let Tf : ℕ :=
    logTwoMod729Fast (splitOddEndpointTarget729 R.1 B.1).val
  have hFast : splitOddEndpointL R.1 B.1 = Tf := by
    dsimp [Tf]
    exact splitOddEndpointL_eq_fast R.1 B.1
  have hTfLt : Tf < 486 := by
    simpa [hFast] using hTLt
  have hDvd :
      splitOddTargetClassModulus ∣ twoHoleUnitModulus := by
    norm_num [splitOddTargetClassModulus, twoHoleUnitModulus]
  have hSmallAllowed :
      let w := (splitOddTargetClassFastResidue R.1 B.1).val
      (w = splitOddV1 % splitOddTargetClassModulus ∨
       w = splitOddV2 % splitOddTargetClassModulus ∨
       w = splitOddV3 % splitOddTargetClassModulus ∨
       w = splitOddV4 % splitOddTargetClassModulus) := by
    dsimp only [splitOddTargetClassFastResidue, splitOddTargetFastAt]
    change
      ((splitOddTargetAt splitOddTargetClassModulus R.1 Tf B.1).val =
          splitOddV1 % splitOddTargetClassModulus ∨
       (splitOddTargetAt splitOddTargetClassModulus R.1 Tf B.1).val =
          splitOddV2 % splitOddTargetClassModulus ∨
       (splitOddTargetAt splitOddTargetClassModulus R.1 Tf B.1).val =
          splitOddV3 % splitOddTargetClassModulus ∨
       (splitOddTargetAt splitOddTargetClassModulus R.1 Tf B.1).val =
          splitOddV4 % splitOddTargetClassModulus)
    rcases hAllowed with h | h | h | h
    · have hp :=
        projected_val_eq_mod_of_val_eq
          hDvd (splitOddTargetQ R.1 B.1) h
      rw [splitOddTargetQ_project hDvd, hFast] at hp
      exact Or.inl hp
    · have hp :=
        projected_val_eq_mod_of_val_eq
          hDvd (splitOddTargetQ R.1 B.1) h
      rw [splitOddTargetQ_project hDvd, hFast] at hp
      exact Or.inr (Or.inl hp)
    · have hp :=
        projected_val_eq_mod_of_val_eq
          hDvd (splitOddTargetQ R.1 B.1) h
      rw [splitOddTargetQ_project hDvd, hFast] at hp
      exact Or.inr (Or.inr (Or.inl hp))
    · have hp :=
        projected_val_eq_mod_of_val_eq
          hDvd (splitOddTargetQ R.1 B.1) h
      rw [splitOddTargetQ_project hDvd, hFast] at hp
      exact Or.inr (Or.inr (Or.inr hp))
  have hCases :=
    splitOddTarget_fast_smallMod_classification R B hTfLt hSmallAllowed
  rcases hCases with h1 | h2 | h3
  · rcases h1 with hA | hB'
    · have hv :
          (splitOddTargetQ R.1 B.1).val = splitOddV1 := by
        simpa [hA.1, hA.2.2] using splitOddTargetQ_value_4_19
      exact Or.inl
        ⟨hv, Or.inl
          ⟨hA.1, hFast.trans hA.2.1, hA.2.2⟩⟩
    · have hv :
          (splitOddTargetQ R.1 B.1).val = splitOddV1 := by
        simpa [hB'.1, hB'.2.2] using splitOddTargetQ_value_23_467
      exact Or.inl
        ⟨hv, Or.inr
          ⟨hB'.1, hFast.trans hB'.2.1, hB'.2.2⟩⟩
  · rcases h2 with hA | hB'
    · have hv :
          (splitOddTargetQ R.1 B.1).val = splitOddV2 := by
        simpa [hA.1, hA.2.2] using splitOddTargetQ_value_4_181
      exact Or.inr (Or.inl
        ⟨hv, Or.inl
          ⟨hA.1, hFast.trans hA.2.1, hA.2.2⟩⟩)
    · have hv :
          (splitOddTargetQ R.1 B.1).val = splitOddV2 := by
        simpa [hB'.1, hB'.2.2] using splitOddTargetQ_value_185_305
      exact Or.inr (Or.inl
        ⟨hv, Or.inr
          ⟨hB'.1, hFast.trans hB'.2.1, hB'.2.2⟩⟩)
  · rcases h3 with hA | hB'
    · have hv :
          (splitOddTargetQ R.1 B.1).val = splitOddV3 := by
        simpa [hA.1, hA.2.2] using splitOddTargetQ_value_4_343
      exact Or.inr (Or.inr
        ⟨hv, Or.inl
          ⟨hA.1, hFast.trans hA.2.1, hA.2.2⟩⟩)
    · have hv :
          (splitOddTargetQ R.1 B.1).val = splitOddV3 := by
        simpa [hB'.1, hB'.2.2] using splitOddTargetQ_value_347_143
      exact Or.inr (Or.inr
        ⟨hv, Or.inr
          ⟨hB'.1, hFast.trans hB'.2.1, hB'.2.2⟩⟩)

/--
mod729 の split-odd endpoint equation が成立するとき、
構成的に復元した `splitOddEndpointL R B` は元の target exponent `T` に一致する。
-/
private theorem splitOddEndpointL_eq
    (R T B : Fin 486)
    (hZero :
      (2 : ZMod 729) ^ R.1 *
          ((2 : ZMod 729) ^ T.1 - 1 -
            (2 : ZMod 729) ^ B.1) + 1 = 0) :
    splitOddEndpointL R.1 B.1 = T.1 := by
  have hInv :
      (2 : ZMod 729) ^ (486 - R.1) *
          (2 : ZMod 729) ^ R.1 = 1 := by
    rw [← pow_add, Nat.sub_add_cancel (Nat.le_of_lt R.2)]
    exact twoPeriod729
  have hPow :
      (2 : ZMod 729) ^ T.1 =
        splitOddEndpointTarget729 R.1 B.1 := by
    unfold splitOddEndpointTarget729
    have hScaled :=
      congrArg
        (fun z : ZMod 729 =>
          (2 : ZMod 729) ^ (486 - R.1) * z)
        hZero
    rw [mul_zero, mul_add, ← mul_assoc, hInv, one_mul, mul_one] at hScaled
    calc
      (2 : ZMod 729) ^ T.1 =
          1 + (2 : ZMod 729) ^ B.1 -
            (2 : ZMod 729) ^ (486 - R.1) := by
              linear_combination hScaled
      _ = _ := by ring
  unfold splitOddEndpointL
  have hVal := congrArg ZMod.val hPow.symm
  rw [hVal]
  exact logTwoMod729_twoPow T

/--
`k≡1 (mod 1944)` と3つの source-width residue のいずれかが成立する split odd `a=2` では、
mod32 の low-bit contradiction により exit depth は `r≤4` に制限される。
-/
private theorem splitOdd_exitDepth_le_four
    {k n r L b : ℕ}
    (hk1944 : k % 1944 = 1)
    (hnResid :
      n % 486 = 23 ∨ n % 486 = 185 ∨ n % 486 = 347)
    (hEq : SplitTwoHoleEquation k n r L 2 b) :
    r ≤ 4 := by
  have hn5 : 5 ≤ n := by
    have hle := Nat.mod_le n 486
    rcases hnResid with h | h | h <;> omega
  by_contra hNot
  have hr5 : 5 ≤ r := by omega
  have hk8 : k % 8 = 1 := by
    have hmod : (k % 1944) % 8 = k % 8 := by
      simp only [Nat.reduceDvd, Nat.mod_mod_of_dvd]
    rw [hk1944] at hmod
    norm_num at hmod
    exact hmod.symm
  have hMod := hEq.to_mod 32
  unfold SplitTwoHoleModEquation at hMod
  have hThreePeriod : (3 : ZMod 32) ^ 8 = 1 := by decide
  rw [pow_eq_pow_mod_of_pow_eq_one (3 : ZMod 32) (e := k) hThreePeriod,
      hk8] at hMod
  have hNZero : (2 : ZMod 32) ^ n = 0 := by
    simpa using ZMod.natCast_pow_eq_zero_of_le 2 hn5
  have hRZero : (2 : ZMod 32) ^ r = 0 := by
    simpa using ZMod.natCast_pow_eq_zero_of_le 2 hr5
  rw [hNZero, hRZero] at hMod
  norm_num at hMod
  exact (by decide : (-15 : ZMod 32) ≠ 1) hMod

/--
unit quotient の source/target classification を合成した六つの候補。
前半三型が `r=4` の desired family、後半三型が `R=N` 型の余分な family。
-/
private def SplitOddA2MainResidueClass
    (N R T B : ℕ) : Prop :=
  (N = 23 ∧ R = 4 ∧ T = 21 ∧ B = 19) ∨
  (N = 185 ∧ R = 4 ∧ T = 183 ∧ B = 181) ∨
  (N = 347 ∧ R = 4 ∧ T = 345 ∧ B = 343) ∨
  (N = 23 ∧ R = 23 ∧ T = 2 ∧ B = 467) ∨
  (N = 185 ∧ R = 185 ∧ T = 2 ∧ B = 305) ∨
  (N = 347 ∧ R = 347 ∧ T = 2 ∧ B = 143)

/-- `r≤4` 後に残る三つの desired family。 -/
private def SplitOddA2SmallResidueClass
    (N R T B : ℕ) : Prop :=
  (N = 23 ∧ R = 4 ∧ T = 21 ∧ B = 19) ∨
  (N = 185 ∧ R = 4 ∧ T = 183 ∧ B = 181) ∨
  (N = 347 ∧ R = 4 ∧ T = 345 ∧ B = 343)

/--
source/target の有限分類を突き合わせ、六つの compatible residue family にまとめる。
`splitOddV4` は target 側に対応値を持たないのでここで排除される。
-/
private theorem splitOddA2_main_residue_of_classifications
    (K : Fin 1944) (N R T B : Fin 486)
    (hTL : splitOddEndpointL R.1 B.1 = T.1)
    (hTLt : splitOddEndpointL R.1 B.1 < 486)
    (hValEq :
      (splitOddSourceQ K.1 N.1).val =
        (splitOddTargetQ R.1 B.1).val)
    (hSourceClass :
      ((splitOddSourceQ K.1 N.1).val = splitOddV1 ∧
        K.1 = 1 ∧ N.1 = 23) ∨
      ((splitOddSourceQ K.1 N.1).val = splitOddV2 ∧
        K.1 = 1 ∧ N.1 = 185) ∨
      ((splitOddSourceQ K.1 N.1).val = splitOddV3 ∧
        K.1 = 1 ∧ N.1 = 347) ∨
      ((splitOddSourceQ K.1 N.1).val = splitOddV4 ∧
        K.1 = 1943 ∧ N.1 = 1)) :
    K.1 = 1 ∧ SplitOddA2MainResidueClass N.1 R.1 T.1 B.1 := by
  have hSourceAllowed :
      (splitOddSourceQ K.1 N.1).val = splitOddV1 ∨
      (splitOddSourceQ K.1 N.1).val = splitOddV2 ∨
      (splitOddSourceQ K.1 N.1).val = splitOddV3 ∨
      (splitOddSourceQ K.1 N.1).val = splitOddV4 := by
    rcases hSourceClass with h | h | h | h
    · exact Or.inl h.1
    · exact Or.inr (Or.inl h.1)
    · exact Or.inr (Or.inr (Or.inl h.1))
    · exact Or.inr (Or.inr (Or.inr h.1))
  have hTargetAllowed :
      (splitOddTargetQ R.1 B.1).val = splitOddV1 ∨
      (splitOddTargetQ R.1 B.1).val = splitOddV2 ∨
      (splitOddTargetQ R.1 B.1).val = splitOddV3 ∨
      (splitOddTargetQ R.1 B.1).val = splitOddV4 := by
    rw [← hValEq]
    exact hSourceAllowed
  have hTargetClass :=
    splitOddTarget_classification R B hTLt hTargetAllowed
  unfold SplitOddA2MainResidueClass
  rcases hSourceClass with hS1 | hS2 | hS3 | hS4
  · refine ⟨hS1.2.1, ?_⟩
    rcases hTargetClass with hT1 | hT2 | hT3
    · rcases hT1.2 with hA | hB'
      · exact Or.inl
          ⟨hS1.2.2, hA.1, hTL.symm.trans hA.2.1, hA.2.2⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inl
          ⟨hS1.2.2, hB'.1, hTL.symm.trans hB'.2.1, hB'.2.2⟩)))
    · have hbad : splitOddV1 = splitOddV2 := by
        calc
          splitOddV1 = (splitOddSourceQ K.1 N.1).val := hS1.1.symm
          _ = (splitOddTargetQ R.1 B.1).val := hValEq
          _ = splitOddV2 := hT2.1
      norm_num [splitOddV1, splitOddV2] at hbad
    · have hbad : splitOddV1 = splitOddV3 := by
        calc
          splitOddV1 = (splitOddSourceQ K.1 N.1).val := hS1.1.symm
          _ = (splitOddTargetQ R.1 B.1).val := hValEq
          _ = splitOddV3 := hT3.1
      norm_num [splitOddV1, splitOddV3] at hbad
  · refine ⟨hS2.2.1, ?_⟩
    rcases hTargetClass with hT1 | hT2 | hT3
    · have hbad : splitOddV2 = splitOddV1 := by
        calc
          splitOddV2 = (splitOddSourceQ K.1 N.1).val := hS2.1.symm
          _ = (splitOddTargetQ R.1 B.1).val := hValEq
          _ = splitOddV1 := hT1.1
      norm_num [splitOddV2, splitOddV1] at hbad
    · rcases hT2.2 with hA | hB'
      · exact Or.inr (Or.inl
          ⟨hS2.2.2, hA.1, hTL.symm.trans hA.2.1, hA.2.2⟩)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨hS2.2.2, hB'.1, hTL.symm.trans hB'.2.1, hB'.2.2⟩))))
    · have hbad : splitOddV2 = splitOddV3 := by
        calc
          splitOddV2 = (splitOddSourceQ K.1 N.1).val := hS2.1.symm
          _ = (splitOddTargetQ R.1 B.1).val := hValEq
          _ = splitOddV3 := hT3.1
      norm_num [splitOddV2, splitOddV3] at hbad
  · refine ⟨hS3.2.1, ?_⟩
    rcases hTargetClass with hT1 | hT2 | hT3
    · have hbad : splitOddV3 = splitOddV1 := by
        calc
          splitOddV3 = (splitOddSourceQ K.1 N.1).val := hS3.1.symm
          _ = (splitOddTargetQ R.1 B.1).val := hValEq
          _ = splitOddV1 := hT1.1
      norm_num [splitOddV3, splitOddV1] at hbad
    · have hbad : splitOddV3 = splitOddV2 := by
        calc
          splitOddV3 = (splitOddSourceQ K.1 N.1).val := hS3.1.symm
          _ = (splitOddTargetQ R.1 B.1).val := hValEq
          _ = splitOddV2 := hT2.1
      norm_num [splitOddV3, splitOddV2] at hbad
    · rcases hT3.2 with hA | hB'
      · exact Or.inr (Or.inr (Or.inl
          ⟨hS3.2.2, hA.1, hTL.symm.trans hA.2.1, hA.2.2⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ⟨hS3.2.2, hB'.1, hTL.symm.trans hB'.2.1, hB'.2.2⟩))))
  · rcases hTargetClass with hT1 | hT2 | hT3
    · have hbad : splitOddV4 = splitOddV1 := by
        calc
          splitOddV4 = (splitOddSourceQ K.1 N.1).val := hS4.1.symm
          _ = (splitOddTargetQ R.1 B.1).val := hValEq
          _ = splitOddV1 := hT1.1
      norm_num [splitOddV4, splitOddV1] at hbad
    · have hbad : splitOddV4 = splitOddV2 := by
        calc
          splitOddV4 = (splitOddSourceQ K.1 N.1).val := hS4.1.symm
          _ = (splitOddTargetQ R.1 B.1).val := hValEq
          _ = splitOddV2 := hT2.1
      norm_num [splitOddV4, splitOddV2] at hbad
    · have hbad : splitOddV4 = splitOddV3 := by
        calc
          splitOddV4 = (splitOddSourceQ K.1 N.1).val := hS4.1.symm
          _ = (splitOddTargetQ R.1 B.1).val := hValEq
          _ = splitOddV3 := hT3.1
      norm_num [splitOddV4, splitOddV3] at hbad

/-- 六候補から source width residue の三択だけを取り出す。 -/
private theorem splitOddA2_source_residue_of_main
    {N R T B : ℕ}
    (h : SplitOddA2MainResidueClass N R T B) :
    N = 23 ∨ N = 185 ∨ N = 347 := by
  unfold SplitOddA2MainResidueClass at h
  rcases h with h | h | h | h | h | h
  · exact Or.inl h.1
  · exact Or.inr (Or.inl h.1)
  · exact Or.inr (Or.inr h.1)
  · exact Or.inl h.1
  · exact Or.inr (Or.inl h.1)
  · exact Or.inr (Or.inr h.1)

/--
`R` が実際の exit depth `r` の residue で、`r≤4` なら、
六候補のうち `R=N∈{23,185,347}` の三型は不可能。
-/
private theorem splitOddA2_small_residue_of_exit_le_four
    {N R T B r : ℕ}
    (hMain : SplitOddA2MainResidueClass N R T B)
    (hR : R = r)
    (hrLe4 : r ≤ 4) :
    SplitOddA2SmallResidueClass N R T B := by
  unfold SplitOddA2MainResidueClass at hMain
  unfold SplitOddA2SmallResidueClass
  rcases hMain with h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · omega
  · omega
  · omega

/-- desired 三型では exit depth は exact に `4`。 -/
private theorem splitOddA2_exit_eq_four_of_small_residue
    {N R T B r : ℕ}
    (h : SplitOddA2SmallResidueClass N R T B)
    (hR : R = r) :
    r = 4 := by
  unfold SplitOddA2SmallResidueClass at h
  rcases h with h | h | h <;> omega

/--
split odd `a=2` の M₅ finite reduction も内部化する。

mod729 で target exponent を復元し、unit quotient で三 residue familyへ分類する。
余分に現れる三つの `R=N` 型は mod32 の low-bit contradiction で除く。
-/
theorem splitOddA2M5FiniteReduction_internal :
    SplitOddA2M5FiniteReduction := by
  intro k n r L b hk7 hkOdd hn2 hr hb0 hbL hEq
  have h729 := hEq.to_mod 729
  unfold SplitTwoHoleModEquation at h729
  have hThreeZero : (3 : ZMod 729) ^ k = 0 :=
    threePow_zero_mod729 (by omega)
  rw [hThreeZero] at h729
  simp only [zero_mul] at h729
  rw [pow_eq_pow_mod_of_pow_eq_one (2 : ZMod 729) (e := r) twoPeriod729,
      pow_eq_pow_mod_of_pow_eq_one (2 : ZMod 729) (e := L) twoPeriod729,
      pow_eq_pow_mod_of_pow_eq_one (2 : ZMod 729) (e := b) twoPeriod729] at h729
  let K : Fin 1944 :=
    ⟨k % 1944, Nat.mod_lt _ (by norm_num)⟩
  let N : Fin 486 :=
    ⟨n % 486, Nat.mod_lt _ (by norm_num)⟩
  let R : Fin 486 :=
    ⟨r % 486, Nat.mod_lt _ (by norm_num)⟩
  let T : Fin 486 :=
    ⟨L % 486, Nat.mod_lt _ (by norm_num)⟩
  let B : Fin 486 :=
    ⟨b % 486, Nat.mod_lt _ (by norm_num)⟩
  have hKodd : K.1 % 2 = 1 := by
    dsimp [K]
    have hmod : (k % 1944) % 2 = k % 2 := by
      simp only [Nat.reduceDvd, Nat.mod_mod_of_dvd]
    rw [hmod, hkOdd]
  have hEndpointZero :
      (2 : ZMod 729) ^ R.1 *
          ((2 : ZMod 729) ^ T.1 - 1 -
            (2 : ZMod 729) ^ B.1) + 1 = 0 := by
    simpa [R, T, B] using h729.symm
  have hTL : splitOddEndpointL R.1 B.1 = T.1 :=
    splitOddEndpointL_eq R T B hEndpointZero
  have hTLt : splitOddEndpointL R.1 B.1 < 486 := by
    rw [hTL]
    exact T.2
  have hQ := hEq.to_mod twoHoleUnitModulus
  have hQred := hQ.reduce twoHoleUnitPeriods
  have hFinite :
      SplitTwoHoleModEquation twoHoleUnitModulus
        K.1 N.1 R.1 T.1 2 B.1 := by
    simpa [K, N, R, T, B] using hQred
  have hFinite' := hFinite
  unfold SplitTwoHoleModEquation at hFinite'
  norm_num at hFinite'
  have hFiniteNorm :
      (3 : ZMod twoHoleUnitModulus) ^ K.1 *
          ((2 : ZMod twoHoleUnitModulus) ^ N.1 - 5) =
        (2 : ZMod twoHoleUnitModulus) ^ R.1 *
          ((2 : ZMod twoHoleUnitModulus) ^ T.1 - 1 -
            (2 : ZMod twoHoleUnitModulus) ^ B.1) + 1 := by
    calc
      (3 : ZMod twoHoleUnitModulus) ^ K.1 *
          ((2 : ZMod twoHoleUnitModulus) ^ N.1 - 5)
          =
        (3 : ZMod twoHoleUnitModulus) ^ K.1 *
          ((2 : ZMod twoHoleUnitModulus) ^ N.1 - 1 - 4) := by ring
      _ = _ := hFinite'
  have hEqQ :
      splitOddSourceQ K.1 N.1 =
        splitOddTargetQ R.1 B.1 := by
    unfold splitOddSourceQ splitOddTargetQ
    rw [hTL]
    exact hFiniteNorm
  have hValEq := congrArg ZMod.val hEqQ
  have hSourceClass :=
    splitOdd_common_source_classification K N R B hKodd hEqQ
  have hMain :=
    splitOddA2_main_residue_of_classifications
      K N R T B hTL hTLt hValEq hSourceClass
  have hk1944 : k % 1944 = 1 := by
    simpa [K] using hMain.1
  have hnResid :
      n % 486 = 23 ∨ n % 486 = 185 ∨ n % 486 = 347 := by
    have hN := splitOddA2_source_residue_of_main hMain.2
    simpa [N] using hN
  have hrLe4 :=
    splitOdd_exitDepth_le_four hk1944 hnResid hEq
  have hRsmall : r % 486 = r := by
    exact Nat.mod_eq_of_lt (by omega)
  have hRval : R.1 = r := by
    simpa [R] using hRsmall
  have hDesired : SplitOddA2SmallResidueClass N.1 R.1 T.1 B.1 :=
    splitOddA2_small_residue_of_exit_le_four hMain.2 hRval hrLe4
  have hr4 : r = 4 :=
    splitOddA2_exit_eq_four_of_small_residue hDesired hRval
  refine ⟨hr4, hk1944, ?_⟩
  unfold SplitOddA2ResidueClass
  unfold SplitOddA2SmallResidueClass at hDesired
  dsimp [N, T, B] at hDesired
  rcases hDesired with h | h | h
  · exact Or.inl ⟨h.1, h.2.2.1, h.2.2.2⟩
  · exact Or.inr (Or.inl ⟨h.1, h.2.2.1, h.2.2.2⟩)
  · exact Or.inr (Or.inr ⟨h.1, h.2.2.1, h.2.2.2⟩)

/-! ## target `n=3`: M₅ finite certificate -/

private def targetThreeHoleScaled
    (r A B : ℕ) : ZMod TwoHoleM5.modulus :=
  (2 : ZMod TwoHoleM5.modulus) ^ r *
    ((2 : ZMod TwoHoleM5.modulus) ^ A +
      (2 : ZMod TwoHoleM5.modulus) ^ B)

private def targetThreeNeed
    (r J T : ℕ) : ZMod TwoHoleM5.modulus :=
  (2 : ZMod TwoHoleM5.modulus) ^ r *
      ((2 : ZMod TwoHoleM5.modulus) ^ T - 1) + 1 -
    7 * (3 : ZMod TwoHoleM5.modulus) ^ (6 + J)

/-!
### target `n=3` の縮小 modulus sieve

M₅ 全体の hole/need list を作らず、branch ごとの小 modulus 非交差へ落とす。

* even branch (`r=1`) : `729 * 7 * 73 = 372519`
* odd branch  (`r=2`) : `729 * 7 * 163 * 2593 = 2156828877`
-/

private def targetThreeEvenSieveModulus : ℕ := 372519
private def targetThreeOddSieveModulus : ℕ := 2156828877


/-- target `n=3` の hole side を任意の縮小 modulus 上で読む。 -/
private def targetThreeHoleScaledAt
    (m r A B : ℕ) : ZMod m :=
  (2 : ZMod m) ^ r * ((2 : ZMod m) ^ A + (2 : ZMod m) ^ B)

/-- target `n=3` の need side を任意の縮小 modulus 上で読む。 -/
private def targetThreeNeedAt
    (m r J T : ℕ) : ZMod m :=
  (2 : ZMod m) ^ r * ((2 : ZMod m) ^ T - 1) + 1 -
    7 * (3 : ZMod m) ^ (6 + J)

/-- M₅ hole side の divisor modulus への射影。 -/
private theorem targetThreeHoleScaled_project
    {m : ℕ}
    (hDvd : m ∣ TwoHoleM5.modulus)
    (r A B : ℕ) :
    ZMod.castHom hDvd (ZMod m) (targetThreeHoleScaled r A B) =
      targetThreeHoleScaledAt m r A B := by
  unfold targetThreeHoleScaled targetThreeHoleScaledAt
  simp only [map_mul, map_pow, map_add, map_ofNat]

/-- M₅ need side の divisor modulus への射影。 -/
private theorem targetThreeNeed_project
    {m : ℕ}
    (hDvd : m ∣ TwoHoleM5.modulus)
    (r J T : ℕ) :
    ZMod.castHom hDvd (ZMod m) (targetThreeNeed r J T) =
      targetThreeNeedAt m r J T := by
  unfold targetThreeNeed targetThreeNeedAt
  simp only [map_sub, map_add, map_mul, map_pow, map_one, map_ofNat]

/-- even branch の hole residue 全体。 -/
private def targetThreeEvenHoleValues : List ℕ :=
  (List.range 486).flatMap fun A =>
    (List.range 486).map fun B =>
      (targetThreeHoleScaledAt targetThreeEvenSieveModulus 1 A B).val

/-- even branch hole residue の HashSet。 -/
private def targetThreeEvenHoleSet : Std.HashSet ℕ :=
  Std.HashSet.ofList targetThreeEvenHoleValues

/-- odd branch の hole residue 全体。 -/
private def targetThreeOddHoleValues : List ℕ :=
  (List.range 486).flatMap fun A =>
    (List.range 486).map fun B =>
      (targetThreeHoleScaledAt targetThreeOddSieveModulus 2 A B).val

/-- odd branch hole residue の HashSet。 -/
private def targetThreeOddHoleSet : Std.HashSet ℕ :=
  Std.HashSet.ofList targetThreeOddHoleValues

/-- finite `(A,B)` の even hole residue は集合に含まれる。 -/
private theorem targetThreeEvenHoleSet_contains
    (A B : Fin 486) :
    targetThreeEvenHoleSet.contains
        (targetThreeHoleScaledAt targetThreeEvenSieveModulus 1 A.1 B.1).val = true := by
  have hMem :
      (targetThreeHoleScaledAt targetThreeEvenSieveModulus 1 A.1 B.1).val ∈
        targetThreeEvenHoleValues := by
    unfold targetThreeEvenHoleValues
    apply List.mem_flatMap.mpr
    refine ⟨A.1, List.mem_range.mpr A.2, ?_⟩
    apply List.mem_map.mpr
    exact ⟨B.1, List.mem_range.mpr B.2, rfl⟩
  simpa only [
    targetThreeEvenHoleSet,
    Std.HashSet.contains_ofList,
    List.contains_eq_mem,
    decide_eq_true_eq
  ] using hMem

/-- finite `(A,B)` の odd hole residue は集合に含まれる。 -/
private theorem targetThreeOddHoleSet_contains
    (A B : Fin 486) :
    targetThreeOddHoleSet.contains
        (targetThreeHoleScaledAt targetThreeOddSieveModulus 2 A.1 B.1).val = true := by
  have hMem :
      (targetThreeHoleScaledAt targetThreeOddSieveModulus 2 A.1 B.1).val ∈
        targetThreeOddHoleValues := by
    unfold targetThreeOddHoleValues
    apply List.mem_flatMap.mpr
    refine ⟨A.1, List.mem_range.mpr A.2, ?_⟩
    apply List.mem_map.mpr
    exact ⟨B.1, List.mem_range.mpr B.2, rfl⟩
  simpa only [
    targetThreeOddHoleSet,
    Std.HashSet.contains_ofList,
    List.contains_eq_mem,
    decide_eq_true_eq
  ] using hMem

/-!
### target n=3: native_decide を使わない縮小 finite sieve
-/

/-- `targetThreeHoleScaledAt` を divisor modulus へ射影する。 -/
private theorem targetThreeHoleScaledAt_project_divisor
    {m n : ℕ}
    (hDvd : m ∣ n)
    (r A B : ℕ) :
    ZMod.castHom hDvd (ZMod m)
        (targetThreeHoleScaledAt n r A B) =
      targetThreeHoleScaledAt m r A B := by
  unfold targetThreeHoleScaledAt
  simp only [map_mul, map_pow, map_add, map_ofNat]

/-- `targetThreeNeedAt` を divisor modulus へ射影する。 -/
private theorem targetThreeNeedAt_project_divisor
    {m n : ℕ}
    (hDvd : m ∣ n)
    (r J T : ℕ) :
    ZMod.castHom hDvd (ZMod m)
        (targetThreeNeedAt n r J T) =
      targetThreeNeedAt m r J T := by
  unfold targetThreeNeedAt
  simp only [
    map_sub, map_add, map_mul, map_pow, map_one, map_ofNat
  ]


/-! #### even branch -/

/--
even branch の最終縮小 modulus。

`27 * 7 * 73 = 13797`。
元の `729 * 7 * 73` から 3-adic 精度を `3^3` まで落とす。
-/
private def targetThreeEvenFinalModulus : ℕ := 13797

private instance targetThreeEvenFinalModulus_neZero :
    NeZero targetThreeEvenFinalModulus :=
  ⟨by norm_num [targetThreeEvenFinalModulus]⟩

/-- even final modulus 上で 2 の period は 18。 -/
private theorem targetThreeEvenFinal_twoPeriod :
    (2 : ZMod targetThreeEvenFinalModulus) ^ 18 = 1 := by
  decide

/--
`3^(6+J)` は even final modulus 上で `J mod 12` だけに依存する。

検査するのは `J<1944` の1944点だけであり、
巨大な hole/source 直積は作らない。
-/
private theorem targetThreeEvenFinal_threeTail_reduce :
    ∀ J : Fin 1944,
      (3 : ZMod targetThreeEvenFinalModulus) ^ (6 + J.1) =
        (3 : ZMod targetThreeEvenFinalModulus) ^
          (6 + (J.1 % 12)) := by
  native_decide

/--
even `J` を `J = 2j` (`j<6`) とした reduced state。

状態数は

`6 * 18 * 18 * 18 = 34992`

だけ。この有限 leaf で全て不一致。
-/
private theorem targetThree_even_final_disjoint :
    ∀ J : Fin 6, ∀ T A B : Fin 18,
      targetThreeHoleScaledAt
          targetThreeEvenFinalModulus 1 A.1 B.1 ≠
        targetThreeNeedAt
          targetThreeEvenFinalModulus 1 (2 * J.1) T.1 := by
  native_decide

/--
even branch の元の sieve equality を `13797` へ射影し、
exponent を `J mod 12`, `T,A,B mod 18` へ縮約して排除する。
-/
private theorem targetThree_even_reduced_no_eq
    (J : Fin 1944) (T A B : Fin 486)
    (hParity : J.1 % 2 = 0)
    (hEq :
      targetThreeHoleScaledAt
          targetThreeEvenSieveModulus 1 A.1 B.1 =
        targetThreeNeedAt
          targetThreeEvenSieveModulus 1 J.1 T.1) :
    False := by
  have hDvd :
      targetThreeEvenFinalModulus ∣
        targetThreeEvenSieveModulus := by
    norm_num [
      targetThreeEvenFinalModulus,
      targetThreeEvenSieveModulus
    ]
  have hRaw :=
    congrArg
      (ZMod.castHom hDvd
        (ZMod targetThreeEvenFinalModulus))
      hEq
  have hFinal :
      targetThreeHoleScaledAt
          targetThreeEvenFinalModulus 1 A.1 B.1 =
        targetThreeNeedAt
          targetThreeEvenFinalModulus 1 J.1 T.1 := by
    rw [
      targetThreeHoleScaledAt_project_divisor hDvd,
      targetThreeNeedAt_project_divisor hDvd
    ] at hRaw
    exact hRaw
  have hJParity12 : (J.1 % 12) % 2 = 0 := by
    have hmod :
        (J.1 % 12) % 2 = J.1 % 2 := by
      simp only [Nat.reduceDvd, Nat.mod_mod_of_dvd]
    rw [hmod, hParity]
  let JR : Fin 6 :=
    ⟨(J.1 % 12) / 2, by omega⟩
  let TR : Fin 18 :=
    ⟨T.1 % 18, Nat.mod_lt _ (by norm_num)⟩
  let AR : Fin 18 :=
    ⟨A.1 % 18, Nat.mod_lt _ (by norm_num)⟩
  let BR : Fin 18 :=
    ⟨B.1 % 18, Nat.mod_lt _ (by norm_num)⟩
  have hJRep :
      J.1 % 12 = 2 * JR.1 := by
    dsimp [JR]
    have h := Nat.mod_add_div (J.1 % 12) 2
    omega
  have hHoleReduce :
      targetThreeHoleScaledAt
          targetThreeEvenFinalModulus 1 A.1 B.1 =
        targetThreeHoleScaledAt
          targetThreeEvenFinalModulus 1 AR.1 BR.1 := by
    unfold targetThreeHoleScaledAt
    rw [
      pow_eq_pow_mod_of_pow_eq_one
        (2 : ZMod targetThreeEvenFinalModulus)
        (e := A.1) targetThreeEvenFinal_twoPeriod,
      pow_eq_pow_mod_of_pow_eq_one
        (2 : ZMod targetThreeEvenFinalModulus)
        (e := B.1) targetThreeEvenFinal_twoPeriod
    ]
  have hNeedReduce :
      targetThreeNeedAt
          targetThreeEvenFinalModulus 1 J.1 T.1 =
        targetThreeNeedAt
          targetThreeEvenFinalModulus 1 (2 * JR.1) TR.1 := by
    unfold targetThreeNeedAt
    rw [
      pow_eq_pow_mod_of_pow_eq_one
        (2 : ZMod targetThreeEvenFinalModulus)
        (e := T.1) targetThreeEvenFinal_twoPeriod,
      targetThreeEvenFinal_threeTail_reduce J,
      hJRep
    ]
  have hReduced :
      targetThreeHoleScaledAt
          targetThreeEvenFinalModulus 1 AR.1 BR.1 =
        targetThreeNeedAt
          targetThreeEvenFinalModulus 1 (2 * JR.1) TR.1 := by
    calc
      targetThreeHoleScaledAt
          targetThreeEvenFinalModulus 1 AR.1 BR.1
          =
        targetThreeHoleScaledAt
          targetThreeEvenFinalModulus 1 A.1 B.1 :=
        hHoleReduce.symm
      _ =
        targetThreeNeedAt
          targetThreeEvenFinalModulus 1 J.1 T.1 :=
        hFinal
      _ =
        targetThreeNeedAt
          targetThreeEvenFinalModulus 1 (2 * JR.1) TR.1 :=
        hNeedReduce
  exact
    (targetThree_even_final_disjoint JR TR AR BR)
      hReduced


/-! #### odd branch -/

/--
odd branch stage 1。

`27 * 7 * 163 * 2593 = 79882551`。
-/
private def targetThreeOddStageOneModulus : ℕ := 79882551

/--
odd branch final modulus。

`81 * 7 * 163 * 2593 = 239647653`。
stage 1 より3-adic digitを1桁だけ増やす。
-/
private def targetThreeOddFinalModulus : ℕ := 239647653

private instance targetThreeOddStageOneModulus_neZero :
    NeZero targetThreeOddStageOneModulus :=
  ⟨by norm_num [targetThreeOddStageOneModulus]⟩

private instance targetThreeOddFinalModulus_neZero :
    NeZero targetThreeOddFinalModulus :=
  ⟨by norm_num [targetThreeOddFinalModulus]⟩

/-- odd final modulus 上で 2 の period は162。 -/
private theorem targetThreeOddFinal_twoPeriod :
    (2 : ZMod targetThreeOddFinalModulus) ^ 162 = 1 := by
  native_decide

/--
`3^(6+J)` は odd final modulus 上で `J mod 648` のみに依存する。
-/
private theorem targetThreeOddFinal_threeTail_reduce :
    ∀ J : Fin 1944,
      (3 : ZMod targetThreeOddFinalModulus) ^ (6 + J.1) =
        (3 : ZMod targetThreeOddFinalModulus) ^
          (6 + (J.1 % 648)) := by
  native_decide

/-- stage 1 の reduced hole residue 全体。 -/
private def targetThreeOddStageOneHoleValues : List ℕ :=
  (List.range 162).flatMap fun A =>
    (List.range 162).map fun B =>
      (targetThreeHoleScaledAt
        targetThreeOddStageOneModulus 2 A B).val

private def targetThreeOddStageOneHoleSet :
    Std.HashSet ℕ :=
  Std.HashSet.ofList targetThreeOddStageOneHoleValues

/-- reduced `(A,B)` の hole residue は stage 1 集合に入る。 -/
private theorem targetThreeOddStageOneHoleSet_contains
    (A B : Fin 162) :
    targetThreeOddStageOneHoleSet.contains
        (targetThreeHoleScaledAt
          targetThreeOddStageOneModulus 2 A.1 B.1).val = true := by
  have hMem :
      (targetThreeHoleScaledAt
        targetThreeOddStageOneModulus 2 A.1 B.1).val ∈
        targetThreeOddStageOneHoleValues := by
    unfold targetThreeOddStageOneHoleValues
    apply List.mem_flatMap.mpr
    refine ⟨A.1, List.mem_range.mpr A.2, ?_⟩
    apply List.mem_map.mpr
    exact ⟨B.1, List.mem_range.mpr B.2, rfl⟩
  simpa only [
    targetThreeOddStageOneHoleSet,
    Std.HashSet.contains_ofList,
    List.contains_eq_mem,
    decide_eq_true_eq
  ] using hMem

/--
stage 1 を通過する odd source `(J mod 648, T mod 162)` は7個だけ。
-/
private def targetThreeOddStageOneSurvivorPairs :
    List (ℕ × ℕ) :=
[
  (25, 24),
  (313, 73),
  (355, 109),
  (579, 79),
  (581, 157),
  (645, 6),
  (645, 7)
]

/--
odd `J = 2j+1` として stage 1 を検査する。

source states は

`324 * 162 = 52488`

だけ。
-/
private theorem targetThree_odd_stageOne_source_survivor :
    ∀ J : Fin 324, ∀ T : Fin 162,
      targetThreeOddStageOneHoleSet.contains
          (targetThreeNeedAt
            targetThreeOddStageOneModulus
            2 (2 * J.1 + 1) T.1).val = true →
      (2 * J.1 + 1, T.1) ∈
        targetThreeOddStageOneSurvivorPairs := by
  native_decide

/--
stage 1 の7 survivor を `3^4` modulus へ一桁持ち上げると
どの `(A,B) mod 162` とも一致しない。

状態数は `7 * 162 * 162 = 183708`。
-/
private theorem targetThree_odd_final_disjoint :
    ∀ P : Fin targetThreeOddStageOneSurvivorPairs.length,
      ∀ A B : Fin 162,
        targetThreeHoleScaledAt
            targetThreeOddFinalModulus 2 A.1 B.1 ≠
          targetThreeNeedAt
            targetThreeOddFinalModulus
            2
            (targetThreeOddStageOneSurvivorPairs.get P).1
            (targetThreeOddStageOneSurvivorPairs.get P).2 := by
  native_decide

/--
odd branch の元の sieve equality を

`full → final → stage 1`

へ落とし、7 survivor を final modulus で排除する。
-/
private theorem targetThree_odd_reduced_no_eq
    (J : Fin 1944) (T A B : Fin 486)
    (hParity : J.1 % 2 = 1)
    (hEq :
      targetThreeHoleScaledAt
          targetThreeOddSieveModulus 2 A.1 B.1 =
        targetThreeNeedAt
          targetThreeOddSieveModulus 2 J.1 T.1) :
    False := by
  have hFinalDvd :
      targetThreeOddFinalModulus ∣
        targetThreeOddSieveModulus := by
    norm_num [
      targetThreeOddFinalModulus,
      targetThreeOddSieveModulus
    ]
  have hFinalRaw :=
    congrArg
      (ZMod.castHom hFinalDvd
        (ZMod targetThreeOddFinalModulus))
      hEq
  have hFinal :
      targetThreeHoleScaledAt
          targetThreeOddFinalModulus 2 A.1 B.1 =
        targetThreeNeedAt
          targetThreeOddFinalModulus 2 J.1 T.1 := by
    rw [
      targetThreeHoleScaledAt_project_divisor hFinalDvd,
      targetThreeNeedAt_project_divisor hFinalDvd
    ] at hFinalRaw
    exact hFinalRaw
  have hJParity648 :
      (J.1 % 648) % 2 = 1 := by
    have hmod :
        (J.1 % 648) % 2 = J.1 % 2 := by
      simp only [Nat.reduceDvd, Nat.mod_mod_of_dvd]
    rw [hmod, hParity]
  let JR : Fin 324 :=
    ⟨(J.1 % 648) / 2, by omega⟩
  let TR : Fin 162 :=
    ⟨T.1 % 162, Nat.mod_lt _ (by norm_num)⟩
  let AR : Fin 162 :=
    ⟨A.1 % 162, Nat.mod_lt _ (by norm_num)⟩
  let BR : Fin 162 :=
    ⟨B.1 % 162, Nat.mod_lt _ (by norm_num)⟩
  have hJRep :
      J.1 % 648 = 2 * JR.1 + 1 := by
    dsimp [JR]
    have h := Nat.mod_add_div (J.1 % 648) 2
    omega
  have hHoleReduce :
      targetThreeHoleScaledAt
          targetThreeOddFinalModulus 2 A.1 B.1 =
        targetThreeHoleScaledAt
          targetThreeOddFinalModulus 2 AR.1 BR.1 := by
    unfold targetThreeHoleScaledAt
    rw [
      pow_eq_pow_mod_of_pow_eq_one
        (2 : ZMod targetThreeOddFinalModulus)
        (e := A.1) targetThreeOddFinal_twoPeriod,
      pow_eq_pow_mod_of_pow_eq_one
        (2 : ZMod targetThreeOddFinalModulus)
        (e := B.1) targetThreeOddFinal_twoPeriod
    ]
  have hNeedReduce :
      targetThreeNeedAt
          targetThreeOddFinalModulus 2 J.1 T.1 =
        targetThreeNeedAt
          targetThreeOddFinalModulus
          2 (2 * JR.1 + 1) TR.1 := by
    unfold targetThreeNeedAt
    rw [
      pow_eq_pow_mod_of_pow_eq_one
        (2 : ZMod targetThreeOddFinalModulus)
        (e := T.1) targetThreeOddFinal_twoPeriod,
      targetThreeOddFinal_threeTail_reduce J,
      hJRep
    ]
  have hReducedFinal :
      targetThreeHoleScaledAt
          targetThreeOddFinalModulus 2 AR.1 BR.1 =
        targetThreeNeedAt
          targetThreeOddFinalModulus
          2 (2 * JR.1 + 1) TR.1 := by
    calc
      targetThreeHoleScaledAt
          targetThreeOddFinalModulus 2 AR.1 BR.1
          =
        targetThreeHoleScaledAt
          targetThreeOddFinalModulus 2 A.1 B.1 :=
        hHoleReduce.symm
      _ =
        targetThreeNeedAt
          targetThreeOddFinalModulus 2 J.1 T.1 :=
        hFinal
      _ =
        targetThreeNeedAt
          targetThreeOddFinalModulus
          2 (2 * JR.1 + 1) TR.1 :=
        hNeedReduce
  have hStageDvd :
      targetThreeOddStageOneModulus ∣
        targetThreeOddFinalModulus := by
    norm_num [
      targetThreeOddStageOneModulus,
      targetThreeOddFinalModulus
    ]
  have hStageRaw :=
    congrArg
      (ZMod.castHom hStageDvd
        (ZMod targetThreeOddStageOneModulus))
      hReducedFinal
  have hStage :
      targetThreeHoleScaledAt
          targetThreeOddStageOneModulus 2 AR.1 BR.1 =
        targetThreeNeedAt
          targetThreeOddStageOneModulus
          2 (2 * JR.1 + 1) TR.1 := by
    rw [
      targetThreeHoleScaledAt_project_divisor hStageDvd,
      targetThreeNeedAt_project_divisor hStageDvd
    ] at hStageRaw
    exact hStageRaw
  have hContains :=
    targetThreeOddStageOneHoleSet_contains AR BR
  have hVal := congrArg ZMod.val hStage
  rw [hVal] at hContains
  have hSurvivor :
      (2 * JR.1 + 1, TR.1) ∈
        targetThreeOddStageOneSurvivorPairs :=
    targetThree_odd_stageOne_source_survivor
      JR TR hContains
  obtain ⟨P, hP⟩ :=
    List.get_of_mem hSurvivor
  have hCandidate :
      targetThreeHoleScaledAt
          targetThreeOddFinalModulus 2 AR.1 BR.1 =
        targetThreeNeedAt
          targetThreeOddFinalModulus
          2
          (targetThreeOddStageOneSurvivorPairs.get P).1
          (targetThreeOddStageOneSurvivorPairs.get P).2 := by
    rw [hP]
    exact hReducedFinal
  exact
    (targetThree_odd_final_disjoint P AR BR)
      hCandidate

/--
even `J` の need residue は even target hole residue 集合と交わらない。
大きな HashSet 全探索ではなく、membership witness を取り出して
`13797` の reduced sieve へ送る。
-/
private theorem targetThree_even_need_not_hole :
    ∀ J : Fin 1944, ∀ T : Fin 486,
      J.1 % 2 = 0 →
      targetThreeEvenHoleSet.contains
          (targetThreeNeedAt
            targetThreeEvenSieveModulus 1 J.1 T.1).val = false := by
  intro J T hParity
  by_cases hContains :
      targetThreeEvenHoleSet.contains
          (targetThreeNeedAt
            targetThreeEvenSieveModulus 1 J.1 T.1).val = true
  · exfalso
    have hMem :
        (targetThreeNeedAt
          targetThreeEvenSieveModulus 1 J.1 T.1).val ∈
          targetThreeEvenHoleValues := by
      simpa only [
        targetThreeEvenHoleSet,
        Std.HashSet.contains_ofList,
        List.contains_eq_mem,
        decide_eq_true_eq
      ] using hContains
    unfold targetThreeEvenHoleValues at hMem
    rcases List.mem_flatMap.mp hMem with
      ⟨A, hA, hMemA⟩
    rcases List.mem_map.mp hMemA with
      ⟨B, hB, hVal⟩
    let AF : Fin 486 :=
      ⟨A, List.mem_range.mp hA⟩
    let BF : Fin 486 :=
      ⟨B, List.mem_range.mp hB⟩
    let : NeZero targetThreeEvenSieveModulus :=
      ⟨by
        norm_num [targetThreeEvenSieveModulus]⟩
    have hEq :
        targetThreeHoleScaledAt
            targetThreeEvenSieveModulus
            1 AF.1 BF.1 =
          targetThreeNeedAt
            targetThreeEvenSieveModulus
            1 J.1 T.1 := by
      apply ZMod.val_injective targetThreeEvenSieveModulus
      dsimp [AF, BF]
      exact hVal
    exact
      targetThree_even_reduced_no_eq
        J T AF BF hParity hEq
  · exact Bool.eq_false_of_not_eq_true hContains

/--
odd `J` の need residue は odd target hole residue 集合と交わらない。
membership witness を stage 1 / final の二段 sieve へ送る。
-/
private theorem targetThree_odd_need_not_hole :
    ∀ J : Fin 1944, ∀ T : Fin 486,
      J.1 % 2 = 1 →
      targetThreeOddHoleSet.contains
          (targetThreeNeedAt
            targetThreeOddSieveModulus 2 J.1 T.1).val = false := by
  intro J T hParity
  by_cases hContains :
      targetThreeOddHoleSet.contains
          (targetThreeNeedAt
            targetThreeOddSieveModulus 2 J.1 T.1).val = true
  · exfalso
    have hMem :
        (targetThreeNeedAt
          targetThreeOddSieveModulus 2 J.1 T.1).val ∈
          targetThreeOddHoleValues := by
      simpa only [
        targetThreeOddHoleSet,
        Std.HashSet.contains_ofList,
        List.contains_eq_mem,
        decide_eq_true_eq
      ] using hContains
    unfold targetThreeOddHoleValues at hMem
    rcases List.mem_flatMap.mp hMem with
      ⟨A, hA, hMemA⟩
    rcases List.mem_map.mp hMemA with
      ⟨B, hB, hVal⟩
    let AF : Fin 486 :=
      ⟨A, List.mem_range.mp hA⟩
    let BF : Fin 486 :=
      ⟨B, List.mem_range.mp hB⟩
    let : NeZero targetThreeOddSieveModulus :=
      ⟨by
        norm_num [targetThreeOddSieveModulus]⟩
    have hEq :
        targetThreeHoleScaledAt
            targetThreeOddSieveModulus
            2 AF.1 BF.1 =
          targetThreeNeedAt
            targetThreeOddSieveModulus
            2 J.1 T.1 := by
      apply ZMod.val_injective targetThreeOddSieveModulus
      dsimp [AF, BF]
      exact hVal
    exact
      targetThree_odd_reduced_no_eq
        J T AF BF hParity hEq
  · exact Bool.eq_false_of_not_eq_true hContains
/--
target `n=3` even branch の縮小 modulus sieve。

M₅ 上の equality を `729*7*73` へ射影し、
need residue が hole residue HashSet に入らないことから矛盾を得る。
-/
private theorem targetThree_even_smallMod_sieve
    (J : Fin 1944) (T A B : Fin 486)
    (hParity : J.1 % 2 = 0)
    (hEq :
      targetThreeHoleScaled 1 A.1 B.1 =
        targetThreeNeed 1 J.1 T.1) :
    False := by
  have hDvd :
      targetThreeEvenSieveModulus ∣ TwoHoleM5.modulus := by
    norm_num [targetThreeEvenSieveModulus, TwoHoleM5.modulus]
  have hSmallRaw :=
    congrArg
      (ZMod.castHom hDvd (ZMod targetThreeEvenSieveModulus))
      hEq
  have hSmall :
      targetThreeHoleScaledAt targetThreeEvenSieveModulus 1 A.1 B.1 =
        targetThreeNeedAt targetThreeEvenSieveModulus 1 J.1 T.1 := by
    rw [targetThreeHoleScaled_project hDvd,
        targetThreeNeed_project hDvd] at hSmallRaw
    exact hSmallRaw
  have hContains :=
    targetThreeEvenHoleSet_contains A B
  have hVal := congrArg ZMod.val hSmall
  rw [hVal] at hContains
  have hNot :=
    targetThree_even_need_not_hole J T hParity
  simp [hNot] at hContains

/--
target `n=3` odd branch の縮小 modulus sieve。

M₅ 上の equality を `729*7*163*2593` へ射影し、
need residue と hole residue 集合の非交差から矛盾を得る。
-/
private theorem targetThree_odd_smallMod_sieve
    (J : Fin 1944) (T A B : Fin 486)
    (hParity : J.1 % 2 = 1)
    (hEq :
      targetThreeHoleScaled 2 A.1 B.1 =
        targetThreeNeed 2 J.1 T.1) :
    False := by
  have hDvd :
      targetThreeOddSieveModulus ∣ TwoHoleM5.modulus := by
    norm_num [targetThreeOddSieveModulus, TwoHoleM5.modulus]
  have hSmallRaw :=
    congrArg
      (ZMod.castHom hDvd (ZMod targetThreeOddSieveModulus))
      hEq
  have hSmall :
      targetThreeHoleScaledAt targetThreeOddSieveModulus 2 A.1 B.1 =
        targetThreeNeedAt targetThreeOddSieveModulus 2 J.1 T.1 := by
    rw [targetThreeHoleScaled_project hDvd,
        targetThreeNeed_project hDvd] at hSmallRaw
    exact hSmallRaw
  have hContains :=
    targetThreeOddHoleSet_contains A B
  have hVal := congrArg ZMod.val hSmall
  rw [hVal] at hContains
  have hNot :=
    targetThree_odd_need_not_hole J T hParity
  simp [hNot] at hContains

/--
target `n=3` の一つの parity branch を M₅ finite state へ落とし、
対応する縮小-modulus sieve に渡して矛盾を得る共通補題。
-/
private theorem targetThree_branch_impossible
    {k r L a b parity : ℕ}
    (hk7 : 7 ≤ k)
    (hKParity : k % 2 = parity)
    (hrFixed : r = if parity = 0 then 1 else 2)
    (hEq : TargetTwoHoleEquation k 3 r L a b)
    (hSieve :
      ∀ J : Fin 1944, ∀ T A B : Fin 486,
        J.1 % 2 = parity →
        targetThreeHoleScaled (if parity = 0 then 1 else 2) A.1 B.1 =
          targetThreeNeed (if parity = 0 then 1 else 2) J.1 T.1 →
        False) :
    False := by
  subst r
  let r0 : ℕ := if parity = 0 then 1 else 2
  have hr0mod :
      (if parity = 0 then 1 else 2) % 486 =
        (if parity = 0 then 1 else 2) := by
    apply Nat.mod_eq_of_lt
    split <;> omega
  let J : Fin 1944 :=
    ⟨(k - 6) % 1944, Nat.mod_lt _ (by norm_num)⟩
  let T : Fin 486 :=
    ⟨L % 486, Nat.mod_lt _ (by norm_num)⟩
  let A : Fin 486 :=
    ⟨a % 486, Nat.mod_lt _ (by norm_num)⟩
  let B : Fin 486 :=
    ⟨b % 486, Nat.mod_lt _ (by norm_num)⟩
  have hJParity : J.1 % 2 = parity := by
    dsimp [J]
    have hmod :
        ((k - 6) % 1944) % 2 = (k - 6) % 2 := by
      simp only [Nat.reduceDvd, Nat.mod_mod_of_dvd]
    rw [hmod]
    have hkSub : (k - 6) % 2 = k % 2 := by omega
    rw [hkSub, hKParity]
  have hMod := hEq.to_mod TwoHoleM5.modulus
  have hRed := hMod.reduce_tailLoop TwoHoleM5.loops
  have hkNot : ¬ k < 6 := by omega
  have hFinite :
      TargetTwoHoleModEquation TwoHoleM5.modulus
        (TwoHoleM5.largeDepthKRep J) 3 r0 T.1 A.1 B.1 := by
    dsimp [J, T, A, B, r0]
    simpa [tailLoopExponent, hkNot, TwoHoleM5.largeDepthKRep, hr0mod] using hRed
  have hFinite' := hFinite
  unfold TargetTwoHoleModEquation at hFinite'
  norm_num at hFinite'
  have hFiniteNorm :
      7 * (3 : ZMod TwoHoleM5.modulus) ^ (6 + J.1) =
        (2 : ZMod TwoHoleM5.modulus) ^ r0 *
          ((2 : ZMod TwoHoleM5.modulus) ^ T.1 - 1 -
            (2 : ZMod TwoHoleM5.modulus) ^ A.1 -
              (2 : ZMod TwoHoleM5.modulus) ^ B.1) + 1 := by
    calc
      7 * (3 : ZMod TwoHoleM5.modulus) ^ (6 + J.1)
          =
        (3 : ZMod TwoHoleM5.modulus) ^ (6 + J.1) * 7 := by ring
      _ = _ := by
        simpa [TwoHoleM5.largeDepthKRep] using hFinite'
  have hEqZ :
      targetThreeHoleScaled r0 A.1 B.1 =
        targetThreeNeed r0 J.1 T.1 := by
    unfold targetThreeHoleScaled targetThreeNeed
    calc
      (2 : ZMod TwoHoleM5.modulus) ^ r0 *
          ((2 : ZMod TwoHoleM5.modulus) ^ A.1 +
            (2 : ZMod TwoHoleM5.modulus) ^ B.1)
          =
        (2 : ZMod TwoHoleM5.modulus) ^ r0 *
              ((2 : ZMod TwoHoleM5.modulus) ^ T.1 - 1) + 1 -
            ((2 : ZMod TwoHoleM5.modulus) ^ r0 *
              ((2 : ZMod TwoHoleM5.modulus) ^ T.1 - 1 -
                (2 : ZMod TwoHoleM5.modulus) ^ A.1 -
                  (2 : ZMod TwoHoleM5.modulus) ^ B.1) + 1) := by ring
      _ =
        (2 : ZMod TwoHoleM5.modulus) ^ r0 *
              ((2 : ZMod TwoHoleM5.modulus) ^ T.1 - 1) + 1 -
            7 * (3 : ZMod TwoHoleM5.modulus) ^ (6 + J.1) := by
          rw [← hFiniteNorm]
  exact hSieve J T A B hJParity hEqZ

/-- `n=3`, `k≥7` の well-formed target-two は純有限 M₅ certificate で不可能。 -/
theorem TargetTwoHoleEquation.source_three_largeDepth_impossible
    {k r L a b : ℕ}
    (hk7 : 7 ≤ k)
    (hr : 0 < r)
    (ha0 : 0 < a)
    (hab : a < b)
    (hbL : b < L)
    (hEq : TargetTwoHoleEquation k 3 r L a b) :
    False := by
  rcases Nat.mod_two_eq_zero_or_one k with hkEven | hkOdd
  · have hr1 :=
      hEq.exitDepth_eq_one_of_largeSource_even
        hkEven (by omega : 3 ≤ 3) hr
    apply targetThree_branch_impossible hk7 hkEven hr1 hEq
    intro J T A B hParity hFinite
    simpa using targetThree_even_smallMod_sieve J T A B hParity hFinite
  · have hr2 :=
      hEq.exitDepth_eq_two_of_largeSource_odd
        hkOdd (by omega : 3 ≤ 3) hr ha0 hab hbL
    apply targetThree_branch_impossible hk7 hkOdd hr2 hEq
    intro J T A B hParity hFinite
    simpa using targetThree_odd_smallMod_sieve J T A B hParity hFinite

/-! ## 外部入力を four deep corollaries だけへ縮約 -/

/--
finite certificate を内部化した後に外部から必要なのは4本の
Chim / Gouillon 型特殊 corollary だけ。
-/
structure TwoHoleDeepKnownArithmetic : Prop where
  source_even_chim : ChimTwoSevenEscape
  split_source_chim : ChimSplitSourceEscape
  split_target_chim : ChimSplitTargetEscape
  split_three_two_gouillon : GouillonThreeTwoEscape

/-- 4本の deep corollary から従来 `TwoHoleKnownArithmetic` package を復元する。 -/
theorem TwoHoleDeepKnownArithmetic.toKnownArithmetic
    (K : TwoHoleDeepKnownArithmetic) :
    TwoHoleKnownArithmetic where
  source_even_chim := K.source_even_chim
  source_odd_m5 := sourceOddM5FiniteCertificate_internal
  split_a_one_m4 := splitAOneM4FiniteCertificate_internal
  split_odd_a_two_m5 := splitOddA2M5FiniteReduction_internal
  split_source_chim := K.split_source_chim
  split_target_chim := K.split_target_chim
  split_three_two_gouillon := K.split_three_two_gouillon

/--
target residual も `n=2,3` を内部で除き、small-source は `n=1` だけにする。
`n≥4` residual は既存 geometric / period-break route の finite remainder。
-/
structure TargetTwoResidualArithmeticReduced : Prop where
  source_one_impossible :
    ∀ {k r L a b : ℕ},
      7 ≤ k →
      0 < r →
      0 < a → a < b →
      b + 1 < L →
      TargetTwoHoleEquation k 1 r L a b →
      False
  large_source_impossible :
    ∀ {k n r L a b : ℕ},
      7 ≤ k →
      4 ≤ n →
      0 < r →
      0 < a → a < b →
      b + 1 < L →
      TargetTwoHoleEquation k n r L a b →
      False

/-- reduced target package から従来 target residual package を構成する。 -/
theorem TargetTwoResidualArithmeticReduced.toTargetResidualArithmetic
    (R : TargetTwoResidualArithmeticReduced) :
    TargetTwoResidualArithmetic where
  small_source_impossible := by
    intro k n r L a b hk7 hn hn3 hr ha0 hab hbDeep hEq
    have hnCases : n = 1 ∨ n = 2 ∨ n = 3 := by omega
    rcases hnCases with rfl | rfl | rfl
    · exact R.source_one_impossible hk7 hr ha0 hab hbDeep hEq
    · have hShift := hEq.source_two_to_source_one
      exact R.source_one_impossible
        (by omega : 7 ≤ k + 1) hr ha0 hab hbDeep hShift
    · exact hEq.source_three_largeDepth_impossible
        hk7 hr ha0 hab (by omega)
  large_source_impossible := by
    intro k n r L a b hk7 hn4 hr ha0 hab hbDeep hEq
    exact R.large_source_impossible
      hk7 hn4 hr ha0 hab hbDeep hEq

/-- finite 部分を剥がした後の最小 residual package。 -/
structure TwoHoleResidualArithmeticReduced : Prop where
  split_regular : SplitTwoRegularResidualArithmetic
  target : TargetTwoResidualArithmeticReduced

/--
縮約後の residual package から従来の `TwoHoleResidualArithmetic` を復元する。
split regular 部分はそのまま、target 部分は reduced-to-full の変換を用いる。
-/
theorem TwoHoleResidualArithmeticReduced.toResidualArithmetic
    (R : TwoHoleResidualArithmeticReduced) :
    TwoHoleResidualArithmetic where
  split_regular := R.split_regular
  target := R.target.toTargetResidualArithmetic

end Mersenne
end Collatz3
