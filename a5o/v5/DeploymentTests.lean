import Deployment
set_option autoImplicit false
/-! Synthetic fixtures only: not signatures, attestations, or production logs.
Each synthetic semantic predicate has a failing case. -/
namespace Apertures.Tests
open Apertures

def spec : EvidenceSpec where
  C := fun p a x _ => p = "demo-principal" ∧ a = "demo-agent" ∧ x = "brief"
  I := fun p => p = "demo-principal"
  M := fun a x => a = "demo-agent" ∧ x = "brief"
  S := fun a x => a = "demo-agent" ∧ x = "brief"
  R := fun _ _ _ t => t < 20
  Appointed := fun p a x t =>
    p = "demo-principal" ∧ a = "demo-agent" ∧ x = "brief" ∧ 5 <= t

def checks : Checkers where
  binding := fun q => decide
    (q.principal = "demo-principal" ∧ q.agent = "demo-agent" ∧ q.action = "brief")
  identity := fun p => decide (p = "demo-principal")
  mandate := fun a x => decide (a = "demo-agent" ∧ x = "brief")
  scope := fun a x => decide (a = "demo-agent" ∧ x = "brief")
  revocation := fun q => decide (q.at_ < 20)
  appointment := fun q => decide
    (q.principal = "demo-principal" ∧ q.agent = "demo-agent" ∧ q.action = "brief" ∧ 5 <= q.at_)

theorem checks_sound : CheckersSound spec checks := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q h
    unfold checks Checkers.binding at h
    unfold spec EvidenceSpec.C
    exact of_decide_eq_true h
  · intro p h
    unfold checks Checkers.identity at h
    unfold spec EvidenceSpec.I
    exact of_decide_eq_true h
  · intro a x h
    unfold checks Checkers.mandate at h
    unfold spec EvidenceSpec.M
    exact of_decide_eq_true h
  · intro a x h
    unfold checks Checkers.scope at h
    unfold spec EvidenceSpec.S
    exact of_decide_eq_true h
  · intro q h
    unfold checks Checkers.revocation at h
    unfold spec EvidenceSpec.R
    exact of_decide_eq_true h
  · intro q h
    unfold checks Checkers.appointment at h
    unfold spec EvidenceSpec.Appointed
    exact of_decide_eq_true h

def allowRequest : Request := ⟨1, "demo-principal", "demo-agent", "brief", 10⟩
def denyRequest : Request := { allowRequest with id := 2, at_ := 20 }
def allowReceipt : Receipt := issue checks allowRequest
def denyReceipt : Receipt := issue checks denyRequest
def allowedExecution : Execution := ⟨1, "demo-agent", "brief", 10⟩
def demo : Deployment := ⟨[allowReceipt, denyReceipt], [allowedExecution]⟩

theorem allow_decision : decision checks allowRequest = true := by decide
theorem revocation_denies : decision checks denyRequest = false := by decide
theorem appointment_before_start_denies :
    decision checks { allowRequest with at_ := 4 } = false := by decide

theorem demo_decisions : DecisionsFollowChecker checks demo := by
  intro r hr
  unfold demo at hr
  have h : r = allowReceipt ∨ r = denyReceipt := by
    cases hr with
    | head => exact Or.inl rfl
    | tail _ hr' => cases hr' with
      | head => exact Or.inr rfl
      | tail _ hr'' => cases hr''
  cases h with
  | inl h => subst r; rfl
  | inr h => subst r; rfl

theorem demo_coverage : NoSideChannel demo := by
  intro e he
  unfold demo at he
  have h : e = allowedExecution := by
    cases he with
    | head => rfl
    | tail _ he' => cases he'
  subst e
  refine ⟨allowReceipt, ?_, ⟨rfl, rfl, rfl, rfl⟩, by decide⟩
  unfold demo
  exact List.Mem.head _

theorem demo_unique_ids : UniqueReceiptIds demo := by
  intro r r' hr hr' hId
  unfold demo at hr hr'
  have h : r = allowReceipt ∨ r = denyReceipt := by
    cases hr with
    | head => exact Or.inl rfl
    | tail _ h1 => cases h1 with
      | head => exact Or.inr rfl
      | tail _ h2 => cases h2
  have h' : r' = allowReceipt ∨ r' = denyReceipt := by
    cases hr' with
    | head => exact Or.inl rfl
    | tail _ h1 => cases h1 with
      | head => exact Or.inr rfl
      | tail _ h2 => cases h2
  cases h with
  | inl h =>
    subst r
    cases h' with
    | inl h' => subst r'; rfl
    | inr h' =>
      subst r'
      exact False.elim ((by decide : allowReceipt.request.id ≠ denyReceipt.request.id) hId)
  | inr h =>
    subst r
    cases h' with
    | inl h' =>
      subst r'
      exact False.elim ((by decide : denyReceipt.request.id ≠ allowReceipt.request.id) hId)
    | inr h' => subst r'; rfl

theorem allow_executed : Executes demo "demo-agent" "brief" 10 :=
  ⟨allowedExecution, by unfold demo; exact List.Mem.head _, rfl, rfl, rfl⟩

theorem allow_satisfies_O :
    O spec.C spec.I spec.M spec.S spec.R spec.Appointed
      "demo-principal" "demo-agent" "brief" 10 :=
  decision_sound spec checks checks_sound allowRequest allow_decision

/-- A closed, populated witness: the proposed premises have a nonempty model. -/
theorem nonvacuous_model_exists :
    ∃ (s : EvidenceSpec) (v : Checkers) (d : Deployment),
      CheckersSound s v ∧ DecisionsFollowChecker v d ∧ NoSideChannel d ∧
      UniqueReceiptIds d ∧ ∃ a x t, Executes d a x t :=
  ⟨spec, checks, demo, checks_sound, demo_decisions, demo_coverage, demo_unique_ids,
    "demo-agent", "brief", 10, allow_executed⟩

theorem synthetic_accountability :
    Accountable spec.C spec.I spec.M spec.S spec.R spec.Appointed
      (Executes demo) inAoC :=
  apertures_accountable spec checks demo (Executes demo)
    checks_sound demo_decisions demo_coverage (fun _ _ _ h => h)

theorem deny_receipt_cannot_match_execution :
    ∀ e, e ∈ demo.executions -> ¬ Matches denyReceipt e :=
  deny_not_executed demo demo_coverage demo_unique_ids denyReceipt
    (by unfold demo; exact List.Mem.tail _ (List.Mem.head _)) (by decide)

theorem missing_binding_denies :
    decision { checks with binding := fun _ => false } allowRequest = false := by decide
theorem missing_identity_denies :
    decision { checks with identity := fun _ => false } allowRequest = false := by decide
theorem missing_mandate_denies :
    decision { checks with mandate := fun _ _ => false } allowRequest = false := by decide
theorem missing_scope_denies :
    decision { checks with scope := fun _ _ => false } allowRequest = false := by decide
theorem missing_revocation_denies :
    decision { checks with revocation := fun _ => false } allowRequest = false := by decide
theorem missing_appointment_denies :
    decision { checks with appointment := fun _ => false } allowRequest = false := by decide

theorem all_six_have_failing_cases :
    (¬ spec.C "unknown" "demo-agent" "brief" 10) ∧
    (¬ spec.I "unknown") ∧ (¬ spec.M "demo-agent" "delete") ∧
    (¬ spec.S "demo-agent" "delete") ∧
    (¬ spec.R "demo-principal" "demo-agent" "brief" 20) ∧
    (¬ spec.Appointed "demo-principal" "demo-agent" "brief" 4) := by
  unfold spec EvidenceSpec.C EvidenceSpec.I EvidenceSpec.M EvidenceSpec.S
    EvidenceSpec.R EvidenceSpec.Appointed; decide

theorem wrong_request_id_rejected :
    ¬ Matches allowReceipt { allowedExecution with request_id := 99 } := by
  unfold Matches; decide
theorem wrong_agent_rejected :
    ¬ Matches allowReceipt { allowedExecution with agent := "other" } := by
  unfold Matches; decide
theorem wrong_action_rejected :
    ¬ Matches allowReceipt { allowedExecution with action := "delete" } := by
  unfold Matches; decide
theorem wrong_time_rejected :
    ¬ Matches allowReceipt { allowedExecution with at_ := 11 } := by
  unfold Matches; decide

def phantom : Execution := ⟨99, "other", "delete", 30⟩
theorem phantom_not_listed : ¬ (phantom ∈ demo.executions) := by decide

theorem phantom_not_executed : ¬ Executes demo "other" "delete" 30 := by
  intro hExec
  obtain ⟨e, he, ha, _hx, _ht⟩ := hExec
  unfold demo at he
  have h : e = allowedExecution := by
    cases he with
    | head => rfl
    | tail _ he' => cases he'
  subst e
  exact (by decide : allowedExecution.agent ≠ "other") ha

/-- Bypasses remain representable and fail the coverage requirement. -/
def bypass : Deployment := ⟨[], [allowedExecution]⟩
theorem bypass_violates_coverage : ¬ NoSideChannel bypass := by
  intro h
  obtain ⟨r, hr, _hm, _ha⟩ := h allowedExecution (by unfold bypass; exact List.Mem.head _)
  unfold bypass at hr
  cases hr

/-- An ALLOW flag without correct checker provenance does not suffice. -/
def forgedReceipt : Receipt := ⟨denyRequest, true⟩
def forgedExecution : Execution := ⟨2, "demo-agent", "brief", 20⟩
def forgedTrace : Deployment := ⟨[forgedReceipt], [forgedExecution]⟩

theorem forged_trace_has_coverage : NoSideChannel forgedTrace := by
  intro e he
  unfold forgedTrace at he
  have h : e = forgedExecution := by
    cases he with
    | head => rfl
    | tail _ he' => cases he'
  subst e
  refine ⟨forgedReceipt, ?_, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩
  unfold forgedTrace
  exact List.Mem.head _

theorem forged_allow_fails_checker_fidelity : ¬ DecisionsFollowChecker checks forgedTrace := by
  intro h
  have bad : (true : Bool) = false :=
    h forgedReceipt (by unfold forgedTrace; exact List.Mem.head _)
  exact Bool.noConfusion bad

def extraActual : Agent -> Action -> Time -> Prop :=
  fun a x t => a = "other" ∧ x = "delete" ∧ t = 30

theorem trace_coverage_is_not_real_world_coverage :
    NoSideChannel demo ∧ ¬ CoversActualExecutions demo extraActual :=
  ⟨demo_coverage, fun h =>
    phantom_not_executed (h "other" "delete" 30 ⟨rfl, rfl, rfl⟩)⟩

/-- Returning true is not evidence of a checker's semantic soundness. -/
def lyingChecks : Checkers where
  binding := fun _ => true
  identity := fun _ => true
  mandate := fun _ _ => true
  scope := fun _ _ => true
  revocation := fun _ => true
  appointment := fun _ => true

theorem lying_checks_not_sound : ¬ CheckersSound spec lyingChecks := by
  intro h
  exact (by unfold spec EvidenceSpec.I; decide : ¬ spec.I "unknown")
    (h.identity "unknown" rfl)

def duplicateDeny : Receipt := ⟨allowRequest, false⟩
def ambiguous : Deployment := ⟨[allowReceipt, duplicateDeny], [allowedExecution]⟩

theorem ambiguous_trace_coverage : NoSideChannel ambiguous := by
  intro e he
  unfold ambiguous at he
  have h : e = allowedExecution := by
    cases he with
    | head => rfl
    | tail _ he' => cases he'
  subst e
  refine ⟨allowReceipt, ?_, ⟨rfl, rfl, rfl, rfl⟩, by decide⟩
  unfold ambiguous
  exact List.Mem.head _

theorem ambiguous_ids_not_unique : ¬ UniqueReceiptIds ambiguous := by
  intro h
  have hEq := h allowReceipt duplicateDeny
    (by unfold ambiguous; exact List.Mem.head _)
    (by unfold ambiguous; exact List.Mem.tail _ (List.Mem.head _)) rfl
  have bad : (true : Bool) = false := congrArg (fun r : Receipt => r.allow) hEq
  exact Bool.noConfusion bad

theorem deny_can_match_without_unique_ids :
    NoSideChannel ambiguous ∧ (¬ UniqueReceiptIds ambiguous) ∧
      Matches duplicateDeny allowedExecution :=
  ⟨ambiguous_trace_coverage, ambiguous_ids_not_unique, by unfold Matches; decide⟩

end Apertures.Tests
