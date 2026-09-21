import PeriodicTable
open A5O.Periodic
/-! Each declaration below is FALSE or ILL-TYPED and must be rejected.
    A clean compile of this file would mean the main file proves nothing. -/

-- NC1: perturb the formula reading by one.
theorem nc1 : formulaReading 5 Ar O = 97 := by decide
-- NC2: the chat's original "three orders of magnitude".
theorem nc2 : coRatioBare / coRatioPocket = 10 ^ 3 := by decide
-- NC3: equate oxygen's atomic number with the mass-8 gap (type error).
theorem nc3 : O.Z = gap8 := rfl
-- NC4: claim the direct triplet–singlet reaction is allowed.
theorem nc4 : pathExists 0 0 = true := by decide
-- NC5: iron under the aluminium reading.
theorem nc5 : sumReading Al O = Fe.Z.val := by decide
-- NC6: bare heme carries oxygen after first contact.
theorem nc6 : (bind .O2 (bind .O2 bareHeme)).sixth = some .O2 := by decide
-- NC7: Z = 138 inside the point-nucleus limit.
theorem nc7 : 138 * 1000 < alphaInvMilli := by decide
-- NC8: ungated oxidase never leaks.
theorem nc8 : ∀ e : Fin 5, outcome false e ≠ .reactiveOxygen := by decide
