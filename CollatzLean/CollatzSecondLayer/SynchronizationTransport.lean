import CollatzLean.CollatzSecondLayer.SynchronizationDrift

/-!
# prepared同期境界の隣接endpoint間伝播

上側prepared runの開始値は次chain項の下側endpointそのものである。
odd-only写像の一意性から、そのrunの指数語は実軌道tailと一致する。
これを用いて、同じ最小同期長の二項の間でboundary指数を伝播し、
prepared depthが真に増えることを証明する。
-/

namespace CollatzSecondLayer

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

namespace ExpWord.Runs

/--
実軌道値から始まる任意のactual runは、
同じ長さのorbit segmentと一致する。
-/
theorem eq_segment_of_orbit_start
    {O : OddOrbit}
    {w : ExpWord}
    {i z : ℕ}
    (h : Runs w (O.value i) z) :
    w = O.segmentWord i w.length ∧
      z = O.value (i + w.length) := by
  induction w generalizing i z with
  | nil =>
      cases h with
      | nil =>
          simp only [List.length_nil, OddOrbit.segmentWord_zero, add_zero, and_self]
  | cons e w ih =>
      cases h with
      | @cons _ _ _ y _ he hstep hy htail =>
          have hOrbitStep :
              2 ^ O.exponent i * O.value (i + 1) =
                3 * O.value i + 1 :=
            O.step i
          have hunique :=
            OddOrbit.next_data_unique
              hstep
              hOrbitStep
              hy
              (O.value_odd (i + 1))
          rcases hunique with ⟨heq, hyeq⟩
          subst e
          subst y
          obtain ⟨hword, hend⟩ :=
            ih (i := i + 1) (z := z) htail
          constructor
          · simp only [
              List.length_cons,
              OddOrbit.segmentWord_succ
            ]
            congr 1
          · rw [hend]
            congr 1
            · simp [Nat.add_comm, Nat.add_left_comm]

end ExpWord.Runs

namespace OddOrbit

/--
長さ`m+1`の二segment wordが等しければ、
最後の位置`m`の指数も等しい。
-/
theorem exponent_eq_of_segmentWord_succ_eq
    (O : OddOrbit)
    {i j m : ℕ}
    (h : O.segmentWord i (m + 1) =
      O.segmentWord j (m + 1)) :
    O.exponent (i + m) =
      O.exponent (j + m) := by
  induction m generalizing i j with
  | zero =>
      simpa using congrArg List.head? h
  | succ m ih =>
      simp only [OddOrbit.segmentWord_succ] at h
      have htail :
          O.segmentWord (i + 1) (m + 1) =
            O.segmentWord (j + 1) (m + 1) := by
        exact (List.cons.inj h).2
      have hlast :=
        ih (i := i + 1) (j := j + 1) htail
      have hi :
          (i + 1) + m = i + (m + 1) := by
        omega
      have hj :
          (j + 1) + m = j + (m + 1) := by
        omega
      simpa only [hi, hj] using hlast
/--
長さ`r`の二segment wordが等しければ、`r`未満の各位置の指数が等しい。
-/
theorem exponent_eq_of_segmentWord_eq
    (O : OddOrbit)
    {i j r m : ℕ}
    (h : O.segmentWord i r = O.segmentWord j r)
    (hm : m < r) :
    O.exponent (i + m) = O.exponent (j + m) := by
  have htake := congrArg (List.take (m + 1)) h
  have hle : m + 1 ≤ r := by omega
  rw [O.segmentWord_take_of_le hle,
      O.segmentWord_take_of_le hle] at htake
  exact O.exponent_eq_of_segmentWord_succ_eq htake

end OddOrbit

/-- 一つのSpecial chain項が持つ同期伝播データ。 -/
structure ChainSpecialSynchronizationData
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    (C : InfiniteOrderedTerminalChain S)
    (n : ℕ) where
  special : ChainSpecialC3At (chainAnalysisPacket C n)
  syncLength : ℕ
  depth : ℕ
  syncLength_eq :
    syncLength =
      (chainAnalysisPacket C n).prepared.boundary.word.length
  depth_eq :
    depth = (chainAnalysisPacket C n).carry.d
  lowerBoundaryExponent :
    depth = O.exponent (C.endpointPosition n + syncLength)
  upperBoundaryExponent :
    depth + 1 ≤
      O.exponent (C.endpointPosition (n + 1) + syncLength)
  synchronizedExponent :
    ∀ m : ℕ, m < syncLength →
      O.exponent (C.endpointPosition n + m) =
        O.exponent (C.endpointPosition (n + 1) + m)

/--
同期境界の`length`は、境界語そのもののリスト長に等しい。
-/
theorem chainSpecial_boundaryLength_eq_wordLength
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    {C : InfiniteOrderedTerminalChain S}
    (n : ℕ) :
    (chainAnalysisPacket C n).prepared.boundary.length =
      (chainAnalysisPacket C n).prepared.boundary.word.length := by
  let P := chainAnalysisPacket C n
  have hlen :=
    congrArg List.length P.prepared.boundary.word_eq
  simpa [P] using hlen.symm


/--
同期境界語は、下側endpointから始まる同じ長さの実軌道segmentである。
-/
theorem chainSpecial_lowerWord_eq_segment
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    {C : InfiniteOrderedTerminalChain S}
    (n : ℕ) :
    (chainAnalysisPacket C n).prepared.boundary.word =
      O.segmentWord
        (C.endpointPosition n)
        (chainAnalysisPacket C n).prepared.boundary.word.length := by
  let P := chainAnalysisPacket C n
  have hboundaryLength :
      P.prepared.boundary.length =
        P.prepared.boundary.word.length := by
    simpa [P] using
      chainSpecial_boundaryLength_eq_wordLength
        (C := C) n
  calc
    P.prepared.boundary.word
        =
          O.segmentWord
            P.prepared.lowerOrbit.index
            P.prepared.boundary.length :=
      P.prepared.boundary.word_eq
    _ =
        O.segmentWord
          (C.endpointPosition n)
          P.prepared.boundary.word.length := by
      rw [hboundaryLength]
      rfl


/--
同期境界語を上側endpoint値から実行したrun。
-/
theorem chainSpecial_upperRun
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    {C : InfiniteOrderedTerminalChain S}
    (n : ℕ) :
    Runs
      (chainAnalysisPacket C n).prepared.boundary.word
      (O.value (C.endpointPosition (n + 1)))
      (chainAnalysisPacket C n).prepared.upperFinish := by
  rw [C.upperEndpointValue n]
  exact
    (chainAnalysisPacket C n).prepared.upperRun


/--
同期境界語は、上側endpointから始まる
同じ長さの実軌道segmentでもある。
-/
theorem chainSpecial_upperWord_eq_segment
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    {C : InfiniteOrderedTerminalChain S}
    (n : ℕ) :
    (chainAnalysisPacket C n).prepared.boundary.word =
      O.segmentWord
        (C.endpointPosition (n + 1))
        (chainAnalysisPacket C n).prepared.boundary.word.length := by
  have hrun :
      Runs
        (chainAnalysisPacket C n).prepared.boundary.word
        (O.value (C.endpointPosition (n + 1)))
        (chainAnalysisPacket C n).prepared.upperFinish :=
    chainSpecial_upperRun (C := C) n
  have hOrbit :=
    ExpWord.Runs.eq_segment_of_orbit_start
      (O := O)
      (i := C.endpointPosition (n + 1))
      hrun
  exact hOrbit.1

/--
上側境界runの終点は、
上側endpointから境界語長だけ進んだ実軌道値である。
-/
theorem chainSpecial_upperFinish_eq_orbitValue
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    {C : InfiniteOrderedTerminalChain S}
    (n : ℕ) :
    (chainAnalysisPacket C n).prepared.upperFinish =
      O.value
        (C.endpointPosition (n + 1) +
          (chainAnalysisPacket C n).prepared.boundary.word.length) := by
  have hrun :
      Runs
        (chainAnalysisPacket C n).prepared.boundary.word
        (O.value (C.endpointPosition (n + 1)))
        (chainAnalysisPacket C n).prepared.upperFinish :=
    chainSpecial_upperRun (C := C) n
  have hOrbit :=
    ExpWord.Runs.eq_segment_of_orbit_start
      (O := O)
      (i := C.endpointPosition (n + 1))
      hrun
  exact hOrbit.2

/--
Special C3で選ばれたcarry深さは、下側同期境界の次指数に等しい。
-/
theorem chainSpecial_depth_eq_nextExponent
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    {C : InfiniteOrderedTerminalChain S}
    (n : ℕ)
    (H : ChainSpecialC3At (chainAnalysisPacket C n)) :
    (chainAnalysisPacket C n).carry.d =
      (chainAnalysisPacket C n).prepared.boundary.nextExponent := by
  let P := chainAnalysisPacket C n
  have h :=
    H.deferredCarry.depth_eq
  simpa [
    P,
    ChainAnalysisPacket.carry,
    PreparedCarryData.toCarryComparison
  ] using h


/--
Special C3のcarry深さは、下側境界直後の実軌道指数に等しい。
-/
theorem chainSpecial_lowerBoundaryExponent
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    {C : InfiniteOrderedTerminalChain S}
    (n : ℕ)
    (H : ChainSpecialC3At (chainAnalysisPacket C n)) :
    (chainAnalysisPacket C n).carry.d =
      O.exponent
        (C.endpointPosition n +
          (chainAnalysisPacket C n).prepared.boundary.word.length) := by
  let P := chainAnalysisPacket C n
  have hboundaryLength :
      P.prepared.boundary.length =
        P.prepared.boundary.word.length := by
    simpa [P] using
      chainSpecial_boundaryLength_eq_wordLength
        (C := C) n
  calc
    P.carry.d
        = P.prepared.boundary.nextExponent :=
      chainSpecial_depth_eq_nextExponent
        (C := C) n H
    _ =
        O.exponent
          (P.prepared.lowerOrbit.index +
            P.prepared.boundary.length) :=
      P.prepared.boundary.nextExponent_eq
    _ =
        O.exponent
          (C.endpointPosition n +
            P.prepared.boundary.word.length) := by
      rw [hboundaryLength]
      rfl


/--
上側境界直後の実軌道stepが与える完全2進分解。
-/
theorem chainSpecial_upperExactTwoFactor
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    {C : InfiniteOrderedTerminalChain S}
    (n : ℕ) :
    ExactTwoFactor
      (3 * (chainAnalysisPacket C n).prepared.upperFinish + 1)
      (O.exponent
        (C.endpointPosition (n + 1) +
          (chainAnalysisPacket C n).prepared.boundary.word.length))
      (O.value
        (C.endpointPosition (n + 1) +
          (chainAnalysisPacket C n).prepared.boundary.word.length + 1)) := by
  let P := chainAnalysisPacket C n
  have hupperFinish :
      P.prepared.upperFinish =
        O.value
          (C.endpointPosition (n + 1) +
            P.prepared.boundary.word.length) := by
    simpa [P] using
      chainSpecial_upperFinish_eq_orbitValue
        (C := C) n
  refine ⟨?_, O.value_odd _⟩
  rw [hupperFinish]
  simpa [Nat.add_assoc] using
    (O.step
      (C.endpointPosition (n + 1) +
        P.prepared.boundary.word.length)).symm


/--
上側同期境界直後の指数は、carry深さより少なくとも1だけ大きい。
-/
theorem chainSpecial_upperBoundaryExponent
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    {C : InfiniteOrderedTerminalChain S}
    (n : ℕ)
    (H : ChainSpecialC3At (chainAnalysisPacket C n)) :
    (chainAnalysisPacket C n).carry.d + 1 ≤
      O.exponent
        (C.endpointPosition (n + 1) +
          (chainAnalysisPacket C n).prepared.boundary.word.length) := by
  let P := chainAnalysisPacket C n
  have hactualExact :
      ExactTwoFactor
        (3 * P.prepared.upperFinish + 1)
        (O.exponent
          (C.endpointPosition (n + 1) +
            P.prepared.boundary.word.length))
        (O.value
          (C.endpointPosition (n + 1) +
            P.prepared.boundary.word.length + 1)) := by
    simpa [P] using
      chainSpecial_upperExactTwoFactor
        (C := C) n
  apply factor_exponent_le_exact_exponent hactualExact
  simpa [
    P,
    ChainAnalysisPacket.carry,
    PreparedCarryData.toCarryComparison
  ] using H.deferredCarry.extraFactor


/--
二つのendpointから始まる同期境界語が等しいため、
境界語内部の全指数も位置ごとに一致する。
-/
theorem chainSpecial_synchronizedExponent
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    {C : InfiniteOrderedTerminalChain S}
    (n : ℕ)
    {m : ℕ}
    (hm :
      m <
        (chainAnalysisPacket C n).prepared.boundary.word.length) :
    O.exponent (C.endpointPosition n + m) =
      O.exponent (C.endpointPosition (n + 1) + m) := by
  have hsegments :
      O.segmentWord
          (C.endpointPosition n)
          (chainAnalysisPacket C n).prepared.boundary.word.length
        =
      O.segmentWord
          (C.endpointPosition (n + 1))
          (chainAnalysisPacket C n).prepared.boundary.word.length := by
    rw [
      ← chainSpecial_lowerWord_eq_segment (C := C) n,
      ← chainSpecial_upperWord_eq_segment (C := C) n
    ]
  exact
    O.exponent_eq_of_segmentWord_eq hsegments hm


/--
Special chain項から同期伝播データを構成する。
-/
noncomputable def chainSpecialSynchronizationData
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    {C : InfiniteOrderedTerminalChain S}
    (n : ℕ)
    (H : ChainSpecialC3At (chainAnalysisPacket C n)) :
    ChainSpecialSynchronizationData C n := by
  let P := chainAnalysisPacket C n
  exact
    { special := H

      syncLength :=
        P.prepared.boundary.word.length

      depth :=
        P.carry.d

      syncLength_eq := rfl
      depth_eq := rfl

      lowerBoundaryExponent := by
        simpa [P] using
          chainSpecial_lowerBoundaryExponent
            (C := C) n H

      upperBoundaryExponent := by
        simpa [P] using
          chainSpecial_upperBoundaryExponent
            (C := C) n H

      synchronizedExponent := by
        intro m hm
        simpa [P] using
          chainSpecial_synchronizedExponent
            (C := C) n hm }

/--
同じ同期長`m`の二Special項の間で、すべての中間同期長が`m`より大きければ、
prepared depthは真に増える。
-/
theorem chainSpecial_depth_growth
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    {C : InfiniteOrderedTerminalChain S}
    {k l m : ℕ}
    (hkSpecial : ChainSpecialC3At (chainAnalysisPacket C k))
    (hlSpecial : ChainSpecialC3At (chainAnalysisPacket C l))
    (hbetweenSpecial :
      ∀ t : ℕ, k < t → t < l →
        ChainSpecialC3At (chainAnalysisPacket C t))
    (hkl : k < l)
    (hkLength :
      (chainAnalysisPacket C k).prepared.boundary.word.length = m)
    (hlLength :
      (chainAnalysisPacket C l).prepared.boundary.word.length = m)
    (hbetween :
      ∀ t : ℕ, k < t → t < l →
        m < (chainAnalysisPacket C t).prepared.boundary.word.length) :
    (chainAnalysisPacket C k).carry.d <
      (chainAnalysisPacket C l).carry.d := by
  let Dk := chainSpecialSynchronizationData k hkSpecial
  let Dl := chainSpecialSynchronizationData l hlSpecial
  have hkSync : Dk.syncLength = m := by
    rw [Dk.syncLength_eq, hkLength]
  have hlSync : Dl.syncLength = m := by
    rw [Dl.syncLength_eq, hlLength]
  have hstart :
      Dk.depth + 1 ≤
        O.exponent (C.endpointPosition (k + 1) + m) := by
    simpa [hkSync] using Dk.upperBoundaryExponent
  have hpropagate :
      O.exponent (C.endpointPosition (k + 1) + m) =
        O.exponent (C.endpointPosition l + m) := by
    have hwalk :
        ∀ d : ℕ,
          k + 1 + d ≤ l →
          O.exponent (C.endpointPosition (k + 1) + m) =
            O.exponent (C.endpointPosition (k + 1 + d) + m) := by
      intro d
      induction d with
      | zero =>
          intro _
          simp
      | succ d ih =>
          intro hbound
          have hprev := ih (by omega)
          let t := k + 1 + d
          have htk : k < t := by
            dsimp [t]
            omega
          have htl' : t < l := by
            dsimp [t]
            omega
          let Dt := chainSpecialSynchronizationData t
            (hbetweenSpecial t htk htl')
          have hmLt : m < Dt.syncLength := by
            rw [Dt.syncLength_eq]
            exact hbetween t htk htl'
          have hstep := Dt.synchronizedExponent m hmLt
          have htNext : t + 1 = k + 1 + (d + 1) := by
            dsimp [t]
            omega
          calc
            O.exponent (C.endpointPosition (k + 1) + m)
                = O.exponent (C.endpointPosition t + m) := by
                    simpa [t] using hprev
            _ = O.exponent (C.endpointPosition (t + 1) + m) := hstep
            _ = O.exponent
                (C.endpointPosition (k + 1 + (d + 1)) + m) := by
                  rw [htNext]
    let d := l - (k + 1)
    have hd : k + 1 + d = l := by
      dsimp [d]
      omega
    have h := hwalk d (by omega)
    simpa [hd] using h
  have hlower :
      Dl.depth =
        O.exponent (C.endpointPosition l + m) := by
    simpa [hlSync] using Dl.lowerBoundaryExponent
  have hdepth : Dk.depth < Dl.depth := by
    rw [hlower, ← hpropagate]
    omega
  simpa [Dk.depth_eq, Dl.depth_eq] using hdepth

/-- eventually Special tailから`ChainSynchronizationLaw`を自動構成する。 -/
noncomputable def chainSynchronizationLawOfEventuallySpecial
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    {C : InfiniteOrderedTerminalChain S}
    (E : EventuallyChainSpecialData C) :
    ChainSynchronizationLaw C where
  specialTail := E
  depthGrowth := by
    intro k l m hkStart hkl hkLength hlLength hbetween
    apply chainSpecial_depth_growth
      (E.special k hkStart)
      (E.special l (by omega))
      (by
        intro t hkt htl
        exact E.special t (by omega))
      hkl hkLength hlLength hbetween

end CollatzSecondLayer
