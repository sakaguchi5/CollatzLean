import CollatzLean.Collatz3.Experimental2.YoungFerrersRestricted.PlateauDecomposition
import CollatzLean.Collatz3.Experimental2.YoungFerrersRestricted.RecordFerrersPlateau
import CollatzLean.Collatz3.Experimental2.YoungFerrersRestricted.Conjugate
import CollatzLean.Collatz3.Experimental2.YoungFerrersRestricted.Area
import CollatzLean.Collatz3.Experimental2.YoungFerrersRestricted.Durfee
import CollatzLean.Collatz3.Experimental2.YoungFerrersRestricted.Dominance
import CollatzLean.Collatz3.Experimental2.YoungFerrersRestricted.GenuineConjugate
import CollatzLean.Collatz3.Experimental2.YoungFerrersRestricted.GenuineDurfee
import CollatzLean.Collatz3.Experimental2.YoungFerrersRestricted.ClassicalDominance

-- F1: genuine Frobenius row/column coordinates
import CollatzLean.Collatz3.Experimental2.YoungFerrersRestricted.FrobeniusCoordinates

-- F2: successive rank vector
import CollatzLean.Collatz3.Experimental2.YoungFerrersRestricted.SuccessiveRank

-- F3: successive rank から作る canonical basis recurrence
import CollatzLean.Collatz3.Experimental2.YoungFerrersRestricted.BasisRecurrence

-- F4: basis arm の componentwise minimality と weight 一意性
import CollatzLean.Collatz3.Experimental2.YoungFerrersRestricted.BasisMinimality

-- F5: actual Young 面積に対する basis lower bound
import CollatzLean.Collatz3.Experimental2.YoungFerrersRestricted.RecordFerrersBasisBound

-- F6: actual area と basis weight の parity obstruction
import CollatzLean.Collatz3.Experimental2.YoungFerrersRestricted.BasisParity

-- F7: basis equality と no-simultaneous-diagonal-corner characterization
import CollatzLean.Collatz3.Experimental2.YoungFerrersRestricted.BasisCharacterization

-- F8: Frobenius diagonal corner を canonical widths / rank-drop boundaries へ exact に戻す
import CollatzLean.Collatz3.Experimental2.YoungFerrersRestricted.RecordFerrersDiagonalBoundary

-- F9: rank drop の算術正規形・normalization 不変性・gcd modulus
import CollatzLean.Collatz3.Experimental2.YoungFerrersRestricted.RankDropArithmetic

-- F10: canonical collision の gcd obstruction と area gap >= 2
import CollatzLean.Collatz3.Experimental2.YoungFerrersRestricted.CollisionArithmetic

-- F11: 任意無理回転の floor 公式（Collatz 特殊化は Bridge 層）
import CollatzLean.Collatz3.Experimental2.YoungFerrersRestricted.MechanicalCollisionSpecialization

-- F12: actual-basis 面積差の exact weighted-slack 分解
import CollatzLean.Collatz3.Experimental2.YoungFerrersRestricted.BasisExcessDecomposition

-- F13: diagonal boundary collision と slack の exact bridge、gap >= 2*t
import CollatzLean.Collatz3.Experimental2.YoungFerrersRestricted.DiagonalSlackCollision

set_option linter.style.header false
