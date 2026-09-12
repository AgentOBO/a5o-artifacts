import Deployment

/-!
# A⁵O v5 adapter — apertures-app production trace, 2026-09-12

Transliteration commit: `apertures-app` @ `f683e50e9c0a2130fd003cda8a56b5b756b6812f`
— the code actually running when every receipt below was issued. `runChecks()`
and `TIERS`/`ACTIONS` are byte-identical to `be440d2` (the merge that
introduced the six checkers): the operator-page commit that followed it
touched no server code.

## Type instantiation

Against `Apertures.Request` / `.Receipt` / `.Execution` (`Deployment.lean`,
unmodified):

* `Principal := request.principal`, e.g. `"PRIN-CONNOISSEUR-2026"`, as issued.
* `Agent := ` the member's tier id, lowercase, e.g. `"connoisseur"` — matching
  what `lib/gate.js`'s `checkMandate`/`checkScope` actually key `TIERS` by.
  **Not** the raw `request.agent` JSON field (`"A5O-GATE-CONCIERGE-SURFACE"`,
  the constant surface name): `Checkers.mandate`/`.scope` are typed
  `Agent -> Action -> Prop` with no separate `Principal` parameter, so the
  tier has to live in `Agent` to be visible to those checkers at all.
  `appointment_id` — a different field, resolved through the ledger by the
  `appointment` checker — is untouched by this choice.
* `Action := request.action`, e.g. `"auto"`, as issued.
* `Time :=` the receipts-chain `seq` — `Deployment.lean`'s own comment on
  `at_` already names this: "the modeled authorization/execution commit
  index." A request and its execution are one commit, so `Request.id` and
  `at_` coincide, and `Execution.at_` takes the same `seq` as its
  authorizing receipt. That decision genuinely precedes execution in
  wall-clock time (`issued_at` precedes `executed_at` by ~10ms in every row
  below) is a property of the trace, checked and recorded in
  `closure/pre-attestation-verification-2026-09-12.md` — not modeled here.
* `Request.id :=` the receipts-chain `seq` (already a unique `Nat` per
  request). The trace's own canonical id is `request_id` (a ULID string);
  `seq` is an injective map from those ULIDs, recorded per-request below, so
  `UniqueReceiptIds` below is a statement about the ULIDs via that map.
* `Execution.agent` is likewise the *linked receipt's* tier id, not the
  trace's raw execution `agent` field (also the constant surface name) —
  required for `Matches` (`Deployment.lean`) to hold under this `Agent`
  convention: `Matches` requires `r.request.agent = e.agent` literally.

## Evidence scope

`C`/`M`/`S` (binding/mandate/scope) are independent, checkable facts about
the static `TIERS`/`ACTIONS` tables below — `CheckersSound` for these three
is a real proof, not a restatement. `I` (identity) is likewise static but
composed from two cited lines rather than one literal list: `gate.js`
`checkIdentity(tier){ return TIERS.includes(tier); }` (line 188) checks
`tier ∈ TIERS`, and the `principal` string a receipt actually carries is
built as `'PRIN-' + tier.id.toUpperCase() + '-2026'` (line 261, `buildReceipt`).
`knownPrincipals` below is the image of `tierDefs` under that same naming
formula — `vIdentity`/`sI` are `TIERS`-membership under the receipt's own
naming convention, not a separately-invented list.

`R`/`Appointed` (revocation/appointment) are relative to this trace: Lean has
no channel to the live ledger, so their evidence *is* the trace's own
`checks.revocation` / `checks.appointment` fields, already independently
hash-chain- and signature-verified outside this file (see
`closure/pre-attestation-verification-2026-09-12.md`,
`export_hash_sha256 20ff8dd98f35cc2f758c6b8dcaef4a2ce924b145e36d6b6319da45739930ef9d`).
This is the same honest boundary `Deployment.lean` itself states: "No live
observation... is claimed." Concretely, `revocation_sound`/`appointment_sound`
below are self-witnessed and carry no independent content — the content for
those two obligations is supplied by the `CheckersSound` *attestation*
itself (step 6): the operator attests that the revocation and appointment
checkers actually consult the ledger as this spec describes, which is
exactly what a Lean proof from trace data alone cannot establish.

The final theorem is a concrete instance of `trace_accountable`, not the
unconditional `apertures_accountable` — `CoversActualExecutions` is left as
the attestation it is, not proved here.
-/

set_option autoImplicit false

namespace Apertures.Adapter
open Apertures

-- ============================================================
-- 1. TIERS / ACTIONS, transliterated from `lib/gate.js` (`f683e50`, lines 92-110).
-- ============================================================

structure TierDef where
  id      : String
  scope   : List String
  ceiling : Option Nat
  deriving DecidableEq, Repr

def tierDefs : List TierDef := [
  ⟨"observer",    [],                                                                              none⟩,
  ⟨"explorer",    ["info"],                                                                         none⟩,
  ⟨"insider",     ["info","automation"],                                                            none⟩,
  ⟨"connoisseur", ["info","automation","acquire"],                                                  some 100000⟩,
  ⟨"influencer",  ["info","automation","acquire","assets"],                                         some 150000⟩,
  ⟨"executive",   ["info","automation","acquire","assets","aviation","negprep","estate"],           some 400000⟩,
  ⟨"visionary",   ["info","automation","acquire","assets","aviation","negprep","estate","bespoke"], some 750000⟩,
]

inductive ActionKind | normal | spend | barred | binding
  deriving DecidableEq, Repr

structure ActionDef where
  id     : String
  need   : String
  kind   : ActionKind
  amount : Option Nat
  deriving DecidableEq, Repr

def actionDefs : List ActionDef := [
  ⟨"brief",  "info",       .normal,  none⟩,
  ⟨"auto",   "automation", .normal,  none⟩,
  ⟨"acq",    "acquire",    .spend,   some 40000⟩,
  ⟨"acqbig", "acquire",    .spend,   some 620000⟩,
  ⟨"jet",    "aviation",   .normal,  none⟩,
  ⟨"assets", "assets",     .barred,  none⟩,
  ⟨"neg",    "negprep",    .binding, none⟩,
]

def tierDefOf?   (a : String) : Option TierDef   := tierDefs.find?   (fun t => t.id = a)
def actionDefOf? (x : String) : Option ActionDef := actionDefs.find? (fun a => a.id = x)

-- gate.js line 261 (buildReceipt): principal: 'PRIN-' + tier.id.toUpperCase() + '-2026'.
def principalOf (t : TierDef) : String := "PRIN-" ++ t.id.toUpper ++ "-2026"

-- gate.js line 188: checkIdentity(tier){ return TIERS.includes(tier); } — tier ∈ TIERS,
-- read through the same naming convention every principal string is actually built with:
-- knownPrincipals is exactly `tierDefs.map principalOf`, written as a literal list because
-- `String.toUpper` is implemented by well-founded recursion and does not kernel-reduce
-- through `decide` (needed below for `decisions_follow` etc.) — confirmed equal by the
-- `#eval` check immediately after, which runs compiled, not kernel-reduced.
def knownPrincipals : List String :=
  ["PRIN-OBSERVER-2026","PRIN-EXPLORER-2026","PRIN-INSIDER-2026","PRIN-CONNOISSEUR-2026",
   "PRIN-INFLUENCER-2026","PRIN-EXECUTIVE-2026","PRIN-VISIONARY-2026"]

#eval if tierDefs.map principalOf == knownPrincipals then
  pure () else throw (IO.userError "knownPrincipals does not match tierDefs.map principalOf")

-- ============================================================
-- 2. The six checkers, transliterated from `runChecks()` (`f683e50`).
-- ============================================================

def vBinding (q : Request) : Bool :=
  match actionDefOf? q.action with
  | some ⟨_, _, .binding, _⟩ => false
  | some _ => true
  | none => false

def vIdentity (p : String) : Bool := knownPrincipals.contains p

def vMandate (_a : String) (x : String) : Bool :=
  match actionDefOf? x with
  | some ⟨_, _, .barred, _⟩ => false
  | some _ => true
  | none => false

def vScope (a : String) (x : String) : Bool :=
  match tierDefOf? a, actionDefOf? x with
  | some td, some ad =>
      (!td.scope.isEmpty) && td.scope.contains ad.need &&
      (match ad.kind, td.ceiling, ad.amount with
       | .spend, some c, some amt => decide (amt ≤ c)
       | _, _, _ => true)
  | _, _ => false

-- (request seq, checks.appointment, checks.revocation) — from the trace's
-- own, independently-verified `checks` field. See "Evidence scope" above.
def statusTable : List (Nat × Bool × Bool) := [
  (2,  true, true),
  (3,  true, true),
  (4,  true, true),
  (5,  true, true),
  (6,  true, true),
  (7,  true, false),
  (8,  true, true),
  (9,  true, true),
  (10, true, true),
]

def vAppointment (q : Request) : Bool :=
  ((statusTable.find? (fun e => e.1 = q.id)).map (fun e => e.2.1)).getD false

def vRevocation (q : Request) : Bool :=
  ((statusTable.find? (fun e => e.1 = q.id)).map (fun e => e.2.2)).getD false

def theCheckers : Checkers := {
  binding     := vBinding,
  identity    := vIdentity,
  mandate     := vMandate,
  scope       := vScope,
  revocation  := vRevocation,
  appointment := vAppointment,
}

-- ============================================================
-- 3. EvidenceSpec — independent facts for C/M/S/I; trace-relative for R/Appointed.
-- ============================================================

def sC (_p : String) (_a : String) (x : String) (_t : Nat) : Prop :=
  match actionDefOf? x with
  | some ad => ad.kind ≠ .binding
  | none => False

def sI (p : String) : Prop := p ∈ knownPrincipals

def sM (_a : String) (x : String) : Prop :=
  match actionDefOf? x with
  | some ad => ad.kind ≠ .barred
  | none => False

def sS (a : String) (x : String) : Prop :=
  match tierDefOf? a, actionDefOf? x with
  | some td, some ad =>
      td.scope ≠ [] ∧ ad.need ∈ td.scope ∧
      (ad.kind = .spend → ∀ c amt, td.ceiling = some c → ad.amount = some amt → amt ≤ c)
  | _, _ => False

def sR (p a x : String) (t : Nat) : Prop :=
  ∃ q : Request, q.principal = p ∧ q.agent = a ∧ q.action = x ∧ q.at_ = t ∧ vRevocation q = true

def sAppointed (p a x : String) (t : Nat) : Prop :=
  ∃ q : Request, q.principal = p ∧ q.agent = a ∧ q.action = x ∧ q.at_ = t ∧ vAppointment q = true

def theSpec : EvidenceSpec := { C := sC, I := sI, M := sM, S := sS, R := sR, Appointed := sAppointed }

-- ============================================================
-- 4. CheckersSound. binding/mandate/scope/identity are real proofs over the
--    static tables; revocation/appointment are definitional relative to the
--    trace (see "Evidence scope" above) — self-witnessed by the same request.
-- ============================================================

theorem binding_sound (q : Request) (h : vBinding q = true) :
    sC q.principal q.agent q.action q.at_ := by
  unfold sC
  unfold vBinding at h
  cases hx : actionDefOf? q.action with
  | none => rw [hx] at h; cases h
  | some ad =>
    rw [hx] at h
    cases ad with
    | mk id need kind amount =>
      cases kind with
      | binding => cases h
      | normal => intro hc; cases hc
      | spend => intro hc; cases hc
      | barred => intro hc; cases hc

theorem identity_sound (p : String) (h : vIdentity p = true) : sI p := by
  unfold sI
  unfold vIdentity at h
  exact List.contains_iff_mem.mp h

theorem mandate_sound (a x : String) (h : vMandate a x = true) : sM a x := by
  unfold sM
  unfold vMandate at h
  cases hx : actionDefOf? x with
  | none => rw [hx] at h; cases h
  | some ad =>
    rw [hx] at h
    cases ad with
    | mk id need kind amount =>
      cases kind with
      | barred => cases h
      | normal => intro hc; cases hc
      | spend => intro hc; cases hc
      | binding => intro hc; cases hc

theorem scope_sound (a x : String) (h : vScope a x = true) : sS a x := by
  unfold sS
  unfold vScope at h
  cases htd : tierDefOf? a with
  | none => rw [htd] at h; cases h
  | some td =>
    cases hxd : actionDefOf? x with
    | none => rw [htd, hxd] at h; cases h
    | some ad =>
      simp only [htd, hxd] at h ⊢
      cases hne : td.scope.isEmpty with
      | true => rw [hne] at h; cases h
      | false =>
        rw [hne] at h
        cases hmem : td.scope.contains ad.need with
        | false => rw [hmem] at h; cases h
        | true =>
          rw [hmem] at h
          refine ⟨?_, ?_, ?_⟩
          · intro he; rw [he] at hne; cases hne
          · exact List.contains_iff_mem.mp hmem
          · intro hspend c amt hc ha
            cases ad with
            | mk id need kind amount =>
              cases kind with
              | spend =>
                rw [hc, ha] at h
                simpa using h
              | normal => cases hspend
              | barred => cases hspend
              | binding => cases hspend

theorem revocation_sound (q : Request) (h : vRevocation q = true) :
    sR q.principal q.agent q.action q.at_ :=
  ⟨q, rfl, rfl, rfl, rfl, h⟩

theorem appointment_sound (q : Request) (h : vAppointment q = true) :
    sAppointed q.principal q.agent q.action q.at_ :=
  ⟨q, rfl, rfl, rfl, rfl, h⟩

-- ============================================================
-- 5. The concrete Deployment, from closure/pre-attestation-verification-2026-09-12.md §2.
--    request_id (ULID) -> id (Nat) is the receipts-chain seq; disclosed here
--    so UniqueReceiptIds below is legible as a statement about the ULIDs.
--    -- seq 2  = 01M2A8FZQFCHSY77QMA9GV03T9 (post-merge verification, §1)
--    -- seq 3  = 01M2AA0SFN3NA90YTADZBRP6GV
--    -- seq 4  = 01M2AA1E7KYX68KG31SS1H3VSC
--    -- seq 5  = 01M2AA1MYGNM1AE9V4R3FGD3ED
--    -- seq 6  = 01M2AA1RZDX9XSFJK37CCVF5XY
--    -- seq 7  = 01M2AAD0A9R59GBPVYKDR5PJ8G
--    -- seq 8  = 01M2AAD2X74WGZSTNA8BY3RPHN
--    -- seq 9  = 01M2AAD5EP9Q528JCQ3WMGCR0F
--    -- seq 10 = 01M2AAD7VX7TXZZ33F7RFDGSG9
-- ============================================================

-- Time := seq (see "Type instantiation" above): Request.id and .at_ coincide,
-- one request being one commit for this gate.
def r2  : Request := ⟨2,  "PRIN-INSIDER-2026",     "insider",     "brief",  2⟩
def r3  : Request := ⟨3,  "PRIN-CONNOISSEUR-2026", "connoisseur", "auto",   3⟩
def r4  : Request := ⟨4,  "PRIN-VISIONARY-2026",   "visionary",   "assets", 4⟩
def r5  : Request := ⟨5,  "PRIN-VISIONARY-2026",   "visionary",   "neg",    5⟩
def r6  : Request := ⟨6,  "PRIN-INSIDER-2026",     "insider",     "brief",  6⟩
def r7  : Request := ⟨7,  "PRIN-CONNOISSEUR-2026", "connoisseur", "auto",   7⟩
def r8  : Request := ⟨8,  "PRIN-VISIONARY-2026",   "visionary",   "assets", 8⟩
def r9  : Request := ⟨9,  "PRIN-VISIONARY-2026",   "visionary",   "neg",    9⟩
def r10 : Request := ⟨10, "PRIN-INSIDER-2026",     "insider",     "brief",  10⟩

def receipts : List Receipt := [
  ⟨r2, true⟩, ⟨r3, true⟩, ⟨r4, false⟩, ⟨r5, false⟩, ⟨r6, true⟩,
  ⟨r7, false⟩, ⟨r8, false⟩, ⟨r9, false⟩, ⟨r10, true⟩,
]

-- Execution.agent and .at_ are the linked receipt's tier id and seq (this
-- adapter's Agent/Time conventions throughout), not the trace's raw
-- execution "agent"/"executed_at" fields — required for `Matches` to hold,
-- see file header.
def executions : List Execution := [
  ⟨2,  "insider",     "brief",  2⟩,
  ⟨3,  "connoisseur", "auto",   3⟩,
  ⟨6,  "insider",     "brief",  6⟩,
  ⟨10, "insider",     "brief",  10⟩,
]

def theDeployment : Deployment := ⟨receipts, executions⟩

theorem checkers_sound : CheckersSound theSpec theCheckers where
  binding := binding_sound
  identity := identity_sound
  mandate := mandate_sound
  scope := scope_sound
  revocation := revocation_sound
  appointment := appointment_sound

-- ============================================================
-- 6. Structural properties over the concrete trace.
-- ============================================================

theorem decisions_follow : DecisionsFollowChecker theCheckers theDeployment := by
  intro r hr
  simp only [theDeployment, receipts, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h|h|h|h|h|h|h|h|h <;> subst h <;> decide

theorem no_side_channel : NoSideChannel theDeployment := by
  intro e he
  simp only [theDeployment, executions, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with h|h|h|h <;> subst h
  · exact ⟨⟨r2, true⟩, by decide, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩
  · exact ⟨⟨r3, true⟩, by decide, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩
  · exact ⟨⟨r6, true⟩, by decide, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩
  · exact ⟨⟨r10, true⟩, by decide, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩

theorem unique_receipt_ids : UniqueReceiptIds theDeployment := by
  intro r r' hr hr' heq
  simp only [theDeployment, receipts, List.mem_cons, List.not_mem_nil, or_false] at hr hr'
  rcases hr with h|h|h|h|h|h|h|h|h <;> subst h <;>
    rcases hr' with h|h|h|h|h|h|h|h|h <;> subst h <;>
    first | rfl | (exfalso; revert heq; decide)

-- ============================================================
-- 7. The concrete accountability instance.
-- ============================================================

theorem apertures_trace_accountable :
    Accountable sC sI sM sS sR sAppointed (Executes theDeployment) inAoC :=
  trace_accountable theSpec theCheckers theDeployment checkers_sound decisions_follow no_side_channel

#print axioms binding_sound
#print axioms identity_sound
#print axioms mandate_sound
#print axioms scope_sound
#print axioms revocation_sound
#print axioms appointment_sound
#print axioms checkers_sound
#print axioms decisions_follow
#print axioms no_side_channel
#print axioms unique_receipt_ids
#print axioms apertures_trace_accountable

end Apertures.Adapter
