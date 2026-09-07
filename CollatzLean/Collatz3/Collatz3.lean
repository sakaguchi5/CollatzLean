import CollatzLean.Collatz3.Arithmetic.Pow23
import CollatzLean.Collatz3.Arithmetic.Signed
import CollatzLean.Collatz3.Arithmetic.ModTwoPow

import CollatzLean.Collatz3.Core.Word
import CollatzLean.Collatz3.Core.AffineTransfer
import CollatzLean.Collatz3.Core.WordTransfer
import CollatzLean.Collatz3.Core.EndpointEquation

import CollatzLean.Collatz3.Canonical.OddEndpointResidue
import CollatzLean.Collatz3.Canonical.REQ
import CollatzLean.Collatz3.Canonical.LiftClassification

import CollatzLean.Collatz3.Semantics.OddStep
import CollatzLean.Collatz3.Semantics.Runs
import CollatzLean.Collatz3.Semantics.ReachOne
import CollatzLean.Collatz3.Semantics.OrbitReturn
import CollatzLean.Collatz3.Semantics.PeriodicOrbit

import CollatzLean.Collatz3.Combinatorics.WordRepetition

import CollatzLean.Collatz3.Bridge.RunsToCanonical
import CollatzLean.Collatz3.Bridge.ReachOneConsequences
import CollatzLean.Collatz3.Bridge.PeriodicOrbitConsequences

set_option linter.style.header false
/-!
# Collatz3: thin definitions + derived theorems kernel

旧体系を import しない。
基礎 affine/canonical kernel に、1 到達・actual 周期・文字列反復の薄い語彙と
それらの derived consequences を一方向に追加する。
-/
