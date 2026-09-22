import A5O
import Closure
set_option autoImplicit false

/-!
# A5O deployment repair candidate

A proposed interface, NOT an extraction or verification of the production server.
No live observation, signature validation, or successful Lean build is claimed.
The unchanged A5O.lean and Closure.lean are reused.

Separate: arbitrary data from issued receipts; executions from decisions;
checker outputs from semantic properties; trace coverage from actual coverage.
All evidence obligations remain explicit. No default-True security predicates,
new axioms, or proof placeholders are supplied here.
-/
namespace Apertures

abbrev Principal := String
abbrev Agent := String
abbrev Action := String
abbrev Time := Nat

/-- `at` is the modeled authorization/execution commit index. Adapters must
justify this interpretation, including freshness and concurrent revocation.
Request ids and principal identities are distinct fields. -/
structure Request where
  id : Nat
  principal : Principal
  agent : Agent
  action : Action
  at_ : Time
  deriving DecidableEq, Repr

/-- Constructing a value is NOT evidence that the server issued it. -/
structure Receipt where
  request : Request
  allow : Bool
  deriving DecidableEq, Repr

/-- Independent execution data: no ALLOW condition is built into its type. -/
structure Execution where
  request_id : Nat
  agent : Agent
  action : Action
  at_ : Time
  deriving DecidableEq, Repr

/-- A finite trace supplied by an adapter. Completeness is not assumed. -/
structure Deployment where
  issued : List Receipt
  executions : List Execution
  deriving DecidableEq, Repr

/-- Independent semantic meanings; no field has a default. Defining these
predicates does not establish their truth or adequacy. Production meanings
must be reviewed; callers could still choose overly weak predicates. -/
structure EvidenceSpec where
  C : Principal -> Agent -> Action -> Time -> Prop
  I : Principal -> Prop
  M : Agent -> Action -> Prop
  S : Agent -> Action -> Prop
  R : Principal -> Agent -> Action -> Time -> Prop
  Appointed : Principal -> Agent -> Action -> Time -> Prop

/-- Executable checker interface, not implementations of cryptography,
identity verification, or a live ledger. Closures may consult evidence stores.
M and S retain the time-independent arities of the supplied A5O interface. -/
structure Checkers where
  binding : Request -> Bool
  identity : Principal -> Bool
  mandate : Agent -> Action -> Bool
  scope : Agent -> Action -> Bool
  revocation : Request -> Bool
  appointment : Request -> Bool

structure CheckResult where
  binding : Bool
  identity : Bool
  mandate : Bool
  scope : Bool
  revocation : Bool
  appointment : Bool
  deriving DecidableEq, Repr

def runChecks (v : Checkers) (q : Request) : CheckResult :=
  ⟨v.binding q, v.identity q.principal, v.mandate q.agent q.action,
    v.scope q.agent q.action, v.revocation q, v.appointment q⟩

def allPass (c : CheckResult) : Bool :=
  c.binding && c.identity && c.mandate && c.scope && c.revocation && c.appointment

/-- Exhaustive Boolean-case proof term; does not use native evaluation. -/
theorem allPass_iff (c : CheckResult) :
    allPass c = true <->
      c.binding = true ∧ c.identity = true ∧ c.mandate = true ∧
      c.scope = true ∧ c.revocation = true ∧ c.appointment = true := by
  cases c with
  | mk b i m s r ap =>
    cases b <;> cases i <;> cases m <;> cases s <;> cases r <;> cases ap <;> decide

def decision (v : Checkers) (q : Request) : Bool := allPass (runChecks v q)
def issue (v : Checkers) (q : Request) : Receipt := ⟨q, decision v q⟩

/-- Six separate obligations. The caller must provide proofs, not declarations
that these are axioms. No completeness of the checker is assumed. -/
structure CheckersSound (s : EvidenceSpec) (v : Checkers) : Prop where
  binding : ∀ q, v.binding q = true -> s.C q.principal q.agent q.action q.at_
  identity : ∀ p, v.identity p = true -> s.I p
  mandate : ∀ a x, v.mandate a x = true -> s.M a x
  scope : ∀ a x, v.scope a x = true -> s.S a x
  revocation : ∀ q, v.revocation q = true -> s.R q.principal q.agent q.action q.at_
  appointment : ∀ q, v.appointment q = true -> s.Appointed q.principal q.agent q.action q.at_

theorem decision_sound (s : EvidenceSpec) (v : Checkers)
    (hs : CheckersSound s v) (q : Request) (h : decision v q = true) :
    O s.C s.I s.M s.S s.R s.Appointed q.principal q.agent q.action q.at_ := by
  have hc := (allPass_iff (runChecks v q)).mp h
  exact ⟨hs.binding q hc.1, hs.identity q.principal hc.2.1,
    hs.mandate q.agent q.action hc.2.2.1,
    hs.scope q.agent q.action hc.2.2.2.1,
    hs.revocation q hc.2.2.2.2.1,
    hs.appointment q hc.2.2.2.2.2⟩

theorem invalid_request_denied (s : EvidenceSpec) (v : Checkers)
    (hs : CheckersSound s v) (q : Request)
    (hBad : ¬ O s.C s.I s.M s.S s.R s.Appointed q.principal q.agent q.action q.at_) :
    decision v q = false := by
  cases hd : decision v q with
  | false => rfl
  | true => exact False.elim (hBad (decision_sound s v hs q hd))

theorem no_identity_denied (s : EvidenceSpec) (v : Checkers)
    (hs : CheckersSound s v) (q : Request) (h : ¬ s.I q.principal) :
    decision v q = false :=
  invalid_request_denied s v hs q (fun ho => h ho.2.1)

theorem no_binding_denied (s : EvidenceSpec) (v : Checkers)
    (hs : CheckersSound s v) (q : Request)
    (h : ¬ s.C q.principal q.agent q.action q.at_) : decision v q = false :=
  invalid_request_denied s v hs q (fun ho => h ho.1)

theorem no_mandate_denied (s : EvidenceSpec) (v : Checkers)
    (hs : CheckersSound s v) (q : Request) (h : ¬ s.M q.agent q.action) :
    decision v q = false :=
  invalid_request_denied s v hs q (fun ho => h ho.2.2.1)

theorem no_scope_denied (s : EvidenceSpec) (v : Checkers)
    (hs : CheckersSound s v) (q : Request) (h : ¬ s.S q.agent q.action) :
    decision v q = false :=
  invalid_request_denied s v hs q (fun ho => h ho.2.2.2.1)

theorem revoked_request_denied (s : EvidenceSpec) (v : Checkers)
    (hs : CheckersSound s v) (q : Request)
    (hRevoked : ¬ s.R q.principal q.agent q.action q.at_) : decision v q = false :=
  invalid_request_denied s v hs q (fun ho => hRevoked ho.2.2.2.2.1)

theorem no_appointment_denied (s : EvidenceSpec) (v : Checkers)
    (hs : CheckersSound s v) (q : Request)
    (h : ¬ s.Appointed q.principal q.agent q.action q.at_) : decision v q = false :=
  invalid_request_denied s v hs q (fun ho => h ho.2.2.2.2.2)

/-- Listed decision flags must be linked to the actual checker outputs. -/
def DecisionsFollowChecker (v : Checkers) (d : Deployment) : Prop :=
  ∀ r, r ∈ d.issued -> r.allow = decision v r.request

def Matches (r : Receipt) (e : Execution) : Prop :=
  r.request.id = e.request_id ∧ r.request.agent = e.agent ∧
  r.request.action = e.action ∧ r.request.at_ = e.at_

/-- No authorization condition appears here: a bypass remains representable. -/
def Executes (d : Deployment) (a : Agent) (x : Action) (t : Time) : Prop :=
  ∃ e : Execution, e ∈ d.executions ∧ e.agent = a ∧ e.action = x ∧ e.at_ = t

/-- Cover all actions. True here broadens the domain, not a security predicate. -/
def inAoC : Action -> Unit -> Prop := fun _ _ => True

/-- Only LISTED executions/receipts are quantified. This does not establish
that every real execution was logged. That obligation is separate below. -/
def NoSideChannel (d : Deployment) : Prop :=
  ∀ e, e ∈ d.executions ->
    ∃ r : Receipt, r ∈ d.issued ∧ Matches r e ∧ r.allow = true

/-- For the per-request DENY theorem, not existential accountability. -/
def UniqueReceiptIds (d : Deployment) : Prop :=
  ∀ r r', r ∈ d.issued -> r' ∈ d.issued ->
    r.request.id = r'.request.id -> r = r'

def gate (d : Deployment) : ADASystem Principal Agent Action Time :=
  ⟨fun p a x t => ∃ r : Receipt,
    r ∈ d.issued ∧ r.request.principal = p ∧ r.request.agent = a ∧
    r.request.action = x ∧ r.request.at_ = t ∧ r.allow = true⟩

theorem gate_intercepts (d : Deployment) (h : NoSideChannel d) :
    ∀ (a : Agent) (x : Action) (t : Time) (domain : Unit),
      inAoC x domain -> Executes d a x t ->
      ∃ p : Principal, (gate d).enforces p a x t := by
  intro a x t domain _hDomain hExec
  obtain ⟨e, he, ha, hx, ht⟩ := hExec
  obtain ⟨r, hr, hm, hAllow⟩ := h e he
  exact ⟨r.request.principal, r, hr, rfl, hm.2.1.trans ha,
    hm.2.2.1.trans hx, hm.2.2.2.trans ht, hAllow⟩

def theApertures (d : Deployment) (h : NoSideChannel d) :
    @GatedSystem Principal Agent Action Time Unit (Executes d) inAoC :=
  ⟨gate d, gate_intercepts d h⟩

theorem gate_achievesADA (s : EvidenceSpec) (v : Checkers) (d : Deployment)
    (hs : CheckersSound s v) (hd : DecisionsFollowChecker v d) :
    achievesADA s.C s.I s.M s.S s.R s.Appointed inAoC (gate d) := by
  intro p a x t domain _hDomain hEnforced
  obtain ⟨r, hr, hp, ha, hx, ht, hAllow⟩ := hEnforced
  have hO := decision_sound s v hs r.request ((hd r hr).symm.trans hAllow)
  rw [hp, ha, hx, ht] at hO
  exact hO

theorem trace_accountable (s : EvidenceSpec) (v : Checkers) (d : Deployment)
    (hs : CheckersSound s v) (hd : DecisionsFollowChecker v d)
    (hc : NoSideChannel d) :
    Accountable s.C s.I s.M s.S s.R s.Appointed (Executes d) inAoC :=
  gated_sufficiency s.C s.I s.M s.S s.R s.Appointed (Executes d) inAoC
    (theApertures d hc) (gate_achievesADA s v d hs hd)

/-- Completeness relative to an INDEPENDENT actual-execution relation. -/
def CoversActualExecutions (d : Deployment)
    (actual : Agent -> Action -> Time -> Prop) : Prop :=
  ∀ a x t, actual a x t -> Executes d a x t

/-- Production-facing conditional theorem. No evidence argument is asserted
for the live installation. An adapter must establish all four obligations. -/
theorem apertures_accountable (s : EvidenceSpec) (v : Checkers) (d : Deployment)
    (actual : Agent -> Action -> Time -> Prop)
    (hs : CheckersSound s v) (hd : DecisionsFollowChecker v d)
    (hc : NoSideChannel d) (ha : CoversActualExecutions d actual) :
    Accountable s.C s.I s.M s.S s.R s.Appointed actual inAoC :=
  fun a x t domain hDomain hExec =>
    trace_accountable s v d hs hd hc a x t domain hDomain (ha a x t hExec)

/-- Unique ids prevent a conflicting ALLOW from masking an issued DENY. -/
theorem deny_not_executed (d : Deployment) (hc : NoSideChannel d)
    (hu : UniqueReceiptIds d) (r : Receipt) (hr : r ∈ d.issued)
    (hDeny : r.allow = false) :
    ∀ e, e ∈ d.executions -> ¬ Matches r e := by
  intro e he hm
  obtain ⟨r', hr', hm', hAllow⟩ := hc e he
  have hEq : r = r' := hu r r' hr hr' (hm.1.trans hm'.1.symm)
  rw [hEq] at hDeny
  exact Bool.noConfusion (hDeny.symm.trans hAllow)

end Apertures
