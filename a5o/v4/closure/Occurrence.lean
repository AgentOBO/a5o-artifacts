/-
A⁵O — Appointment as Occurrence
Categorical independence of the appointment conjunct.
Core Lean 4 only. No Mathlib. No axioms beyond the kernel.
-/

structure Artifact where
  agent : Nat
  appointer_field : Nat
  appointment_ref : Nat
  scope : Nat
  bound : Bool
  ident : Bool
  mandate : Bool
  revoked : Bool

structure Appointment where
  appointer : Nat
  appointee : Nat
  scope : Nat
  moment : Nat

def Ledger := Nat → Option Appointment

def C_bind (a : Artifact) : Prop := a.bound = true
def C_ident (a : Artifact) : Prop := a.ident = true
def C_mandate (a : Artifact) : Prop := a.mandate = true
def C_scope (a : Artifact) : Prop := a.scope ≠ 0
def C_revoc (a : Artifact) : Prop := a.revoked = false

def Descriptive (a : Artifact) : Prop :=
  C_bind a ∧ C_ident a ∧ C_mandate a ∧ C_scope a ∧ C_revoc a

def Appointed (L : Ledger) (t : Nat) (a : Artifact) : Prop :=
  ∃ e : Appointment,
    L a.appointment_ref = some e ∧
    e.appointee = a.agent ∧
    e.appointer = a.appointer_field ∧
    e.scope = a.scope ∧
    e.moment ≤ t

def a0 : Artifact :=
  { agent := 1, appointer_field := 1, appointment_ref := 1, scope := 1,
    bound := true, ident := true, mandate := true, revoked := false }

def e0 : Appointment := { appointer := 1, appointee := 1, scope := 1, moment := 0 }

def L1 : Ledger := fun _ => some e0
def L0 : Ledger := fun _ => none

theorem descriptive_a0 : Descriptive a0 :=
  ⟨rfl, rfl, rfl, fun h => Nat.noConfusion h, rfl⟩

theorem appointed_L1 : Appointed L1 0 a0 :=
  ⟨e0, rfl, rfl, rfl, rfl, Nat.le_refl 0⟩

theorem not_appointed_L0 : ¬ Appointed L0 0 a0 := by
  intro h
  obtain ⟨e, hL, _⟩ := h
  exact nomatch hL

theorem appointment_not_artifact_derivable (P : Artifact → Prop) :
    ¬ (∀ (L : Ledger) (t : Nat) (a : Artifact), P a ↔ Appointed L t a) := by
  intro h
  have hP : P a0 := (h L1 0 a0).mpr appointed_L1
  exact not_appointed_L0 ((h L0 0 a0).mp hP)

theorem five_not_appointment :
    ¬ (∀ (L : Ledger) (t : Nat) (a : Artifact), Descriptive a ↔ Appointed L t a) :=
  appointment_not_artifact_derivable Descriptive

theorem bearer_witness : Descriptive a0 ∧ ¬ Appointed L0 0 a0 :=
  ⟨descriptive_a0, not_appointed_L0⟩

def ArtifactOnly (Auth : Ledger → Nat → Artifact → Prop) : Prop :=
  ∃ P : Artifact → Prop, ∀ L t a, Auth L t a ↔ P a

theorem artifact_only_authorizes_unappointed
    (Auth : Ledger → Nat → Artifact → Prop)
    (hA : ArtifactOnly Auth)
    (hNontrivial : ∃ L t a, Auth L t a) :
    ∃ L t a, Auth L t a ∧ ¬ Appointed L t a := by
  obtain ⟨P, hP⟩ := hA
  obtain ⟨L, t, a, hAuth⟩ := hNontrivial
  refine ⟨L0, t, a, (hP L0 t a).mpr ((hP L t a).mp hAuth), ?_⟩
  intro hApp
  obtain ⟨e, hL, _⟩ := hApp
  exact nomatch hL

theorem sound_authorizer_not_artifact_only
    (Auth : Ledger → Nat → Artifact → Prop)
    (hSound : ∀ L t a, Auth L t a → Appointed L t a)
    (hNontrivial : ∃ L t a, Auth L t a) :
    ¬ ArtifactOnly Auth := by
  intro hA
  obtain ⟨L, t, a, hAuth, hNot⟩ :=
    artifact_only_authorizes_unappointed Auth hA hNontrivial
  exact hNot (hSound L t a hAuth)

theorem appointment_precedes_check (L : Ledger) (t : Nat) (a : Artifact)
    (h : Appointed L t a) : ∃ e : Appointment, L a.appointment_ref = some e ∧ e.moment ≤ t := by
  obtain ⟨e, hL, _, _, _, ht⟩ := h
  exact ⟨e, hL, ht⟩

#print axioms appointment_not_artifact_derivable
#print axioms five_not_appointment
#print axioms bearer_witness
#print axioms artifact_only_authorizes_unappointed
#print axioms sound_authorizer_not_artifact_only
#print axioms appointment_precedes_check
