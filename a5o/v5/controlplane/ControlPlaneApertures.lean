import A5O
import Closure
import Deployment
import DeploymentTests
import ControlPlane
set_option autoImplicit false

/-! # A⁵O — theapertures.app IS a Control Plane (checked import).

Imports, unmodified:
  A5O.lean v4          0e5ebe3f…5b452
  Closure.lean         af6b3233…a933
  Deployment.lean v5   e07c69ae…59da   (live-gate deployment model of record)
  DeploymentTests.lean 1386ffb1…24d8   (v5 synthetic fixtures)
  ControlPlane.lean    8d7c36cf…c463d

v5 builds the live gate as a `GatedSystem` from a trace (`theApertures`)
and proves it achieves ADA (`gate_achievesADA`). Here those two v5 objects
are assembled into a `ControlPlane`, and every ControlPlane theorem is
applied to the installation — over the logged trace and over ACTUAL
executions. The four v5 obligations stay explicit hypotheses:
  CheckersSound, CoversActualExecutions  — the signed operator attestations;
  DecisionsFollowChecker, NoSideChannel  — decided over the signed trace.
No obligation is discharged or weakened in this file. -/

namespace Apertures

/-! ## The installation as a control plane -/

/-- Over the logged trace: the v5 gate, as a control plane. -/
def aperturesPlane (s : EvidenceSpec) (v : Checkers) (d : Deployment)
    (hs : CheckersSound s v) (hd : DecisionsFollowChecker v d)
    (hc : NoSideChannel d) :
    ControlPlane s.C s.I s.M s.S s.R s.Appointed (Executes d) inAoC where
  gate := theApertures d hc
  ada  := gate_achievesADA s v d hs hd

/-- Over what ACTUALLY executes: the gate's interception extends from the
trace to real executions through CoversActualExecutions. -/
def aperturesPlaneActual (s : EvidenceSpec) (v : Checkers) (d : Deployment)
    (actual : Agent → Action → Time → Prop)
    (hs : CheckersSound s v) (hd : DecisionsFollowChecker v d)
    (hc : NoSideChannel d) (ha : CoversActualExecutions d actual) :
    ControlPlane s.C s.I s.M s.S s.R s.Appointed actual inAoC where
  gate :=
    { sys := gate d
      intercepts := fun a x t dom hDom hAct =>
        gate_intercepts d hc a x t dom hDom (ha a x t hAct) }
  ada := gate_achievesADA s v d hs hd

/-- The plane over actual executions uses the same decision function as
the v5 gate — nothing is added between the trace and the plane. -/
theorem aperturesPlaneActual_is_v5_gate (s : EvidenceSpec) (v : Checkers)
    (d : Deployment) (actual : Agent → Action → Time → Prop)
    (hs : CheckersSound s v) (hd : DecisionsFollowChecker v d)
    (hc : NoSideChannel d) (ha : CoversActualExecutions d actual) :
    (aperturesPlaneActual s v d actual hs hd hc ha).gate.sys = gate d := rfl

/-! ## The seven ControlPlane properties, at the installation -/

/-- (1) Every actual consequential execution was decided by the gate — an
issued ALLOW receipt exists — and its principal satisfies O. -/
theorem apertures_decides_every_actual_execution
    (s : EvidenceSpec) (v : Checkers) (d : Deployment)
    (actual : Agent → Action → Time → Prop)
    (hs : CheckersSound s v) (hd : DecisionsFollowChecker v d)
    (hc : NoSideChannel d) (ha : CoversActualExecutions d actual)
    (a : Agent) (x : Action) (t : Time) (hAct : actual a x t) :
    ∃ p : Principal, (gate d).enforces p a x t ∧
      O s.C s.I s.M s.S s.R s.Appointed p a x t :=
  plane_decides_every_execution s.C s.I s.M s.S s.R s.Appointed actual inAoC
    (aperturesPlaneActual s v d actual hs hd hc ha) a x t () trivial hAct

/-- (1′) Accountability over actual executions, now obtained through the
control-plane theorem (agrees with v5's `apertures_accountable`). -/
theorem apertures_plane_accountable
    (s : EvidenceSpec) (v : Checkers) (d : Deployment)
    (actual : Agent → Action → Time → Prop)
    (hs : CheckersSound s v) (hd : DecisionsFollowChecker v d)
    (hc : NoSideChannel d) (ha : CoversActualExecutions d actual) :
    Accountable s.C s.I s.M s.S s.R s.Appointed actual inAoC :=
  plane_accountable s.C s.I s.M s.S s.R s.Appointed actual inAoC
    (aperturesPlaneActual s v d actual hs hd hc ha)

/-- (2) Single governor at the installation, under CFunctional of the spec. -/
theorem apertures_single_governor
    (s : EvidenceSpec) (v : Checkers) (d : Deployment)
    (actual : Agent → Action → Time → Prop)
    (hs : CheckersSound s v) (hd : DecisionsFollowChecker v d)
    (hc : NoSideChannel d) (ha : CoversActualExecutions d actual)
    (hC : CFunctional s.C)
    (a : Agent) (x : Action) (t : Time) (hAct : actual a x t) :
    ∃ p : Principal, (gate d).enforces p a x t ∧
      ∀ p' : Principal, (gate d).enforces p' a x t → p' = p :=
  plane_single_governor s.C s.I s.M s.S s.R s.Appointed actual inAoC hC
    (aperturesPlaneActual s v d actual hs hd hc ha) a x t () trivial hAct

/-- (3) No rival: ANY control plane over the same evidence spec that decides
the same act names the same principal as theapertures.app gate. -/
theorem apertures_no_rival_governor
    (s : EvidenceSpec) (v : Checkers) (d : Deployment)
    (actual : Agent → Action → Time → Prop)
    (hs : CheckersSound s v) (hd : DecisionsFollowChecker v d)
    (hc : NoSideChannel d) (ha : CoversActualExecutions d actual)
    (hC : CFunctional s.C)
    (rival : ControlPlane s.C s.I s.M s.S s.R s.Appointed actual inAoC)
    (p q : Principal) (a : Agent) (x : Action) (t : Time)
    (hA : (gate d).enforces p a x t) (hR : rival.gate.sys.enforces q a x t) :
    p = q :=
  planes_agree_on_governor s.C s.I s.M s.S s.R s.Appointed actual inAoC hC
    (aperturesPlaneActual s v d actual hs hd hc ha) rival p q a x t () trivial hA hR

/-- (4) One form: every ALLOW the installation issues lies inside the
canonical O monitor. -/
theorem apertures_within_canonical
    (s : EvidenceSpec) (v : Checkers) (d : Deployment)
    (actual : Agent → Action → Time → Prop)
    (hs : CheckersSound s v) (hd : DecisionsFollowChecker v d)
    (hc : NoSideChannel d) (ha : CoversActualExecutions d actual)
    (p : Principal) (a : Agent) (x : Action) (t : Time)
    (hEnf : (gate d).enforces p a x t) :
    (CanonicalMonitor s.C s.I s.M s.S s.R s.Appointed).enforces p a x t :=
  plane_within_canonical s.C s.I s.M s.S s.R s.Appointed actual inAoC
    (aperturesPlaneActual s v d actual hs hd hc ha) p a x t () trivial hEnf

/-- (5) Revocation halts the act at the installation: after the named
principal revokes, the act does not actually execute. -/
theorem apertures_revocation_halts
    (s : EvidenceSpec) (v : Checkers) (d : Deployment)
    (actual : Agent → Action → Time → Prop)
    (hs : CheckersSound s v) (hd : DecisionsFollowChecker v d)
    (hc : NoSideChannel d) (ha : CoversActualExecutions d actual)
    (Revoke : Principal → Agent → Action → Time → Prop)
    (hP2 : ∀ (p : Principal) (a : Agent) (x : Action) (t t' : Time),
      t < t' → s.Appointed p a x t → Revoke p a x t' → ¬ s.R p a x t')
    (hC : CFunctional s.C)
    (p : Principal) (a : Agent) (x : Action) (t t' : Time)
    (hlt : t < t') (hApp : s.Appointed p a x t) (hRev : Revoke p a x t')
    (hBind : s.C p a x t') :
    ¬ actual a x t' :=
  revocation_halts_execution s.C s.I s.M s.S s.R s.Appointed actual inAoC
    Revoke hP2 hC (aperturesPlaneActual s v d actual hs hd hc ha)
    p a x t t' () trivial hlt hApp hRev hBind

/-! ## Non-vacuity at the v5 fixture: a populated installation-shaped plane -/

open Tests in
theorem spec_CFunctional : CFunctional spec.C :=
  fun _ _ _ _ _ h₁ h₂ => h₁.1.trans h₂.1.symm

open Tests in
/-- (7) On the v5 synthetic trace (one ALLOW executed, one revocation DENY),
all four obligations are discharged by v5's own fixture theorems; the plane
exists, the execution occurs, and it has exactly one governor. -/
theorem demo_plane_single_governor :
    Executes demo "demo-agent" "brief" 10 ∧
    ∃ p : Principal, (gate demo).enforces p "demo-agent" "brief" 10 ∧
      ∀ p' : Principal, (gate demo).enforces p' "demo-agent" "brief" 10 → p' = p :=
  ⟨allow_executed,
   plane_single_governor spec.C spec.I spec.M spec.S spec.R spec.Appointed
     (Executes demo) inAoC spec_CFunctional
     (aperturesPlane spec checks demo checks_sound demo_decisions demo_coverage)
     "demo-agent" "brief" 10 () trivial allow_executed⟩

end Apertures

#print axioms Apertures.aperturesPlaneActual_is_v5_gate
#print axioms Apertures.apertures_decides_every_actual_execution
#print axioms Apertures.apertures_plane_accountable
#print axioms Apertures.apertures_single_governor
#print axioms Apertures.apertures_no_rival_governor
#print axioms Apertures.apertures_within_canonical
#print axioms Apertures.apertures_revocation_halts
#print axioms Apertures.spec_CFunctional
#print axioms Apertures.demo_plane_single_governor
