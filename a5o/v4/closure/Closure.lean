import A5O
set_option autoImplicit false

/-! # A⁵O — Closure of the two open items on the v4 record.
Companion to A5O.lean v4 (SHA-256 0e5ebe3f…5b452), which is imported unmodified.

Item 1 — Independence of the appointment conjunct, stated against v4's own O.
Item 2 — Sufficiency, with interception stated as a property of the system
         rather than a hypothesis on the theorem. -/

-- ============================================================
-- Part A. The occurrence model (repaired), bridged to v4's O.
-- ============================================================
namespace Occurrence

structure Artifact where
  agent : Nat
  appointer_field : Nat
  appointment_ref : Nat
  scope : Nat
  bound : Bool
  ident : Bool
  mandate : Bool
  revoked : Bool

structure Appt where
  appointer : Nat
  appointee : Nat
  scope : Nat
  moment : Nat

def Ledger := Nat → Option Appt

def C_bind (a : Artifact) : Prop := a.bound = true
def C_ident (a : Artifact) : Prop := a.ident = true
def C_mandate (a : Artifact) : Prop := a.mandate = true
def C_scope (a : Artifact) : Prop := a.scope ≠ 0
def C_revoc (a : Artifact) : Prop := a.revoked = false

def Descriptive (a : Artifact) : Prop :=
  C_bind a ∧ C_ident a ∧ C_mandate a ∧ C_scope a ∧ C_revoc a

def AppointedIn (L : Ledger) (t : Nat) (a : Artifact) : Prop :=
  ∃ e : Appt,
    L a.appointment_ref = some e ∧
    e.appointee = a.agent ∧
    e.appointer = a.appointer_field ∧
    e.scope = a.scope ∧
    e.moment ≤ t

def a0 : Artifact :=
  { agent := 1, appointer_field := 1, appointment_ref := 1, scope := 1,
    bound := true, ident := true, mandate := true, revoked := false }
def e0 : Appt := { appointer := 1, appointee := 1, scope := 1, moment := 0 }
def L1 : Ledger := fun _ => some e0
def L0 : Ledger := fun _ => none

theorem descriptive_a0 : Descriptive a0 :=
  ⟨rfl, rfl, rfl, fun h => Nat.noConfusion h, rfl⟩
theorem appointed_L1 : AppointedIn L1 0 a0 :=
  ⟨e0, rfl, rfl, rfl, rfl, Nat.le_refl 0⟩
theorem not_appointed_L0 : ¬ AppointedIn L0 0 a0 := by
  intro h
  obtain ⟨e, hL, _⟩ := h
  exact nomatch hL

theorem appointment_not_artifact_derivable (P : Artifact → Prop) :
    ¬ (∀ (L : Ledger) (t : Nat) (a : Artifact), P a ↔ AppointedIn L t a) := by
  intro h
  have hP : P a0 := (h L1 0 a0).mpr appointed_L1
  exact not_appointed_L0 ((h L0 0 a0).mp hP)

theorem five_not_appointment :
    ¬ (∀ (L : Ledger) (t : Nat) (a : Artifact), Descriptive a ↔ AppointedIn L t a) :=
  appointment_not_artifact_derivable Descriptive

theorem bearer_witness : Descriptive a0 ∧ ¬ AppointedIn L0 0 a0 :=
  ⟨descriptive_a0, not_appointed_L0⟩

def ArtifactOnly (Auth : Ledger → Nat → Artifact → Prop) : Prop :=
  ∃ P : Artifact → Prop, ∀ L t a, Auth L t a ↔ P a

theorem artifact_only_authorizes_unappointed
    (Auth : Ledger → Nat → Artifact → Prop)
    (hA : ArtifactOnly Auth)
    (hNontrivial : ∃ L t a, Auth L t a) :
    ∃ L t a, Auth L t a ∧ ¬ AppointedIn L t a := by
  obtain ⟨P, hP⟩ := hA
  obtain ⟨L, t, a, hAuth⟩ := hNontrivial
  refine ⟨L0, t, a, (hP L0 t a).mpr ((hP L t a).mp hAuth), ?_⟩
  intro hApp
  obtain ⟨e, hL, _⟩ := hApp
  exact nomatch hL

theorem sound_authorizer_not_artifact_only
    (Auth : Ledger → Nat → Artifact → Prop)
    (hSound : ∀ L t a, Auth L t a → AppointedIn L t a)
    (hNontrivial : ∃ L t a, Auth L t a) :
    ¬ ArtifactOnly Auth := by
  intro hA
  obtain ⟨L, t, a, hAuth, hNot⟩ :=
    artifact_only_authorizes_unappointed Auth hA hNontrivial
  exact hNot (hSound L t a hAuth)

theorem appointment_precedes_check (L : Ledger) (t : Nat) (a : Artifact)
    (h : AppointedIn L t a) :
    ∃ e : Appt, L a.appointment_ref = some e ∧ e.moment ≤ t := by
  obtain ⟨e, hL, _, _, _, ht⟩ := h
  exact ⟨e, hL, ht⟩

-- ---- Bridge: instantiate v4's six predicates at this model. ----
-- Principal := Nat (the appointer named in the artifact), Agent := Artifact
-- (the presented document), Action := Nat (scope), Time := Ledger × Nat
-- (the world's record of occurrences and the moment of check).

abbrev World := Ledger × Nat

def vC : Nat → Artifact → Nat → World → Prop := fun p a _ _ => a.bound = true ∧ a.appointer_field = p
def vI : Nat → Prop := fun _ => True
def vM : Artifact → Nat → Prop := fun a _ => a.mandate = true
def vS : Artifact → Nat → Prop := fun a x => a.scope = x ∧ x ≠ 0
def vR : Nat → Artifact → Nat → World → Prop := fun _ a _ _ => a.revoked = false
def vApp : Nat → Artifact → Nat → World → Prop :=
  fun p a _ w => AppointedIn w.1 w.2 a ∧ a.appointer_field = p

/-- The five non-appointment conjuncts of v4's O, at this instance. -/
def Five (p : Nat) (a : Artifact) (x : Nat) (w : World) : Prop :=
  vC p a x w ∧ vI p ∧ vM a x ∧ vS a x ∧ vR p a x w

/-- v4's O at this instance is definitionally Five ∧ vApp. -/
theorem O_is_five_and_app (p : Nat) (a : Artifact) (x : Nat) (w : World) :
    O vC vI vM vS vR vApp p a x w ↔ (Five p a x w ∧ vApp p a x w) := by
  unfold O Five
  exact ⟨fun ⟨c, i, m, s, r, ap⟩ => ⟨⟨c, i, m, s, r⟩, ap⟩,
         fun ⟨⟨c, i, m, s, r⟩, ap⟩ => ⟨c, i, m, s, r, ap⟩⟩

theorem five_a0 : Five 1 a0 1 (L0, 0) :=
  ⟨⟨rfl, rfl⟩, trivial, rfl, ⟨rfl, fun h => Nat.noConfusion h⟩, rfl⟩

theorem not_app_a0 : ¬ vApp 1 a0 1 (L0, 0) :=
  fun ⟨h, _⟩ => not_appointed_L0 h

/-- ITEM 1 CLOSED AGAINST v4: at a concrete instance of v4's own O,
the five other conjuncts hold and the appointment conjunct fails, so
Appointed is not derivable from C ∧ I ∧ M ∧ S ∧ R in v4's O. -/
theorem v4_appointment_independent :
    ∃ (p : Nat) (a : Artifact) (x : Nat) (w : World),
      Five p a x w ∧ ¬ O vC vI vM vS vR vApp p a x w :=
  ⟨1, a0, 1, (L0, 0), five_a0,
   fun hO => not_app_a0 ((O_is_five_and_app 1 a0 1 (L0, 0)).mp hO).2⟩

end Occurrence

-- ============================================================
-- Part B. Sufficiency with interception as a system property.
-- ============================================================
section Sufficiency
variable {Principal Agent Action Time AoC : Type}
variable (C : Principal → Agent → Action → Time → Prop)
variable (I : Principal → Prop)
variable (M : Agent → Action → Prop)
variable (S : Agent → Action → Prop)
variable (R : Principal → Agent → Action → Time → Prop)
variable (Appointed : Principal → Agent → Action → Time → Prop)
variable (Executes : Agent → Action → Time → Prop)
variable (inAoC : Action → AoC → Prop)

/-- Accountability over what actually executes (from Sufficiency.lean, signed 2026-09-09). -/
def Accountable : Prop :=
  ∀ (A : Agent) (X : Action) (t : Time) (domain : AoC),
    inAoC X domain → Executes A X t →
    ∃ P : Principal, O C I M S R Appointed P A X t

/-- A GATED system is a v4 ADASystem carrying, as part of its definition,
the property that nothing executes in an area of consequence unless the
system enforced it for some principal. This is the gate in the execution
path — the property theapertures.app implements. -/
structure GatedSystem where
  sys : ADASystem Principal Agent Action Time
  intercepts : ∀ (A : Agent) (X : Action) (t : Time) (domain : AoC),
    inAoC X domain → Executes A X t → ∃ P : Principal, sys.enforces P A X t

/-- ITEM 2 CLOSED: for a gated system, achieving ADA (v4's necessity
predicate) SUFFICES for accountability over execution. No extra hypothesis. -/
theorem gated_sufficiency
    (G : GatedSystem Executes inAoC)
    (hADA : achievesADA C I M S R Appointed inAoC G.sys) :
    Accountable C I M S R Appointed Executes inAoC :=
  fun A X t domain hDom hExec =>
    let ⟨P, hEnf⟩ := G.intercepts A X t domain hDom hExec
    ⟨P, hADA P A X t domain hDom hEnf⟩

end Sufficiency

-- Boundary (from Sufficiency.lean): an ungated system can achieve ADA and
-- still fail accountability. Retained so the closure is honest about its scope.
section Boundary
def cmC : Unit → Unit → Unit → Unit → Prop := fun _ _ _ _ => True
def cmI : Unit → Prop := fun _ => True
def cmM : Unit → Unit → Prop := fun _ _ => True
def cmS : Unit → Unit → Prop := fun _ _ => True
def cmR : Unit → Unit → Unit → Unit → Prop := fun _ _ _ _ => True
def cmAppointed : Unit → Unit → Unit → Unit → Prop := fun _ _ _ _ => False
def cmExecutes : Unit → Unit → Unit → Prop := fun _ _ _ => True
def cmInAoC : Unit → Unit → Prop := fun _ _ => True
def SilentSystem : ADASystem Unit Unit Unit Unit := ⟨fun _ _ _ _ => False⟩

theorem ungated_ADA_does_not_suffice :
    achievesADA cmC cmI cmM cmS cmR cmAppointed cmInAoC SilentSystem ∧
    ¬ Accountable cmC cmI cmM cmS cmR cmAppointed cmExecutes cmInAoC :=
  ⟨fun _ _ _ _ _ _ hEnf => hEnf.elim,
   fun h => let ⟨_, hO⟩ := h () () () () trivial trivial; hO.2.2.2.2.2⟩

/-- And the silent system cannot be given the gate: no GatedSystem wraps it. -/
theorem silent_not_gatable :
    ¬ ∃ G : GatedSystem cmExecutes cmInAoC, G.sys = SilentSystem := by
  intro ⟨G, hG⟩
  obtain ⟨_, hEnf⟩ := G.intercepts () () () () trivial trivial
  rw [hG] at hEnf
  exact hEnf
end Boundary

#print axioms Occurrence.five_not_appointment
#print axioms Occurrence.sound_authorizer_not_artifact_only
#print axioms Occurrence.v4_appointment_independent
#print axioms gated_sufficiency
#print axioms ungated_ADA_does_not_suffice
#print axioms silent_not_gatable
