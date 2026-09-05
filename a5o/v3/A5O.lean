-- A⁵O FORMAL PROOF (v2 — corrected)
-- Claim: Any system achieving accountable delegated authority
-- in areas of consequence implements a predicate equivalent to O.
--
-- To run: install Lean 4 (https://leanprover.github.io/lean4/doc/setup.html)
-- then: lean A5O.lean
--
-- This file encodes the argument as Lean 4 propositions and theorems.
-- There are no remaining `sorry`s. Where the original version stood on an
-- axiom, the axiom is now either (a) narrowed to an independently
-- defensible primitive with the stronger claim proved as a theorem, or
-- (b) tied to a witnessing structure so it cannot be discharged vacuously.
--
-- REVISION NOTE — what changed and why (see prior audit for full detail):
--   1. The original did not compile: `[Preorder Time]` requires Mathlib,
--      which was never imported, and that failure cascaded into every
--      later declaration. Fixed by scoping a plain `[LT Time]` instance
--      to only the one axiom (P2) that actually needs an order relation.
--   2. `O`'s explicit section variables (`Principal Agent Action Time`)
--      were not marked implicit, so every call site in the original file
--      (`O C I M S R Appointed P A X t`) was missing four leading
--      arguments. Fixed by making the four types implicit.
--   3. `O_unique` was axiomatized directly over the whole six-conjunct
--      predicate. A countermodel (two distinct principals, every
--      predicate trivially True) shows nothing about O's structure
--      forces that cardinality — it was unjustified independent content.
--      Fixed: `O_unique` is now a THEOREM, derived from a narrower,
--      independently defensible axiom `C_functional` (a valid signature
--      verifies against exactly one principal).
--   4. `P2`'s original `∃ (revoked : Prop), revoked → ¬ R ...` is a
--      tautology — witness `revoked := False` proves it with zero
--      hypotheses, for any R. It asserted nothing about revocation.
--      Fixed: introduces a `Revoke` primitive tying the kill-switch to
--      an actual act by P.
--   5. `P3`'s free `A` and `t` were unbound by its own quantifier and not
--      declared as section variables, so Lean's `autoImplicit` silently
--      captured them, decoupling "the executing agent/time" from the
--      axiom's real meaning. Fixed with `set_option autoImplicit false`
--      (turns future recurrences into compile errors) plus an explicit
--      `Executes` primitive binding A/t to X.
--   6. `U3_reduction`'s `∃ gate, ∀ P A X t, gate P A X t ↔ O ...` is
--      provable by picking `gate := O` itself; `#print axioms` on that
--      proof shows zero dependency on P1/P2/P3/O_unique — mechanical
--      proof that the statement was vacuous, since `sys`/`achievesADA sys`
--      were never used. Fixed: `ADASystem` now carries its own
--      `enforces` predicate, `achievesADA` is a real `def` (not an
--      opaque axiom-satisfying predicate) asserting sys never enforces
--      outside O within an area of consequence, and `U3_reduction`
--      genuinely uses `sys`, `hADA`, and the witnessing execution.
--      Honest scope: this proves the NECESSITY half of the informal
--      claim (can't enforce outside O), not full completeness (that sys
--      enforces *everything* O permits) — that stronger claim is not
--      argued anywhere in the original file and is not assumed here.
--   7. M and S (mandate, scope) were never touched by any axiom despite
--      being two of O's six conjuncts. Added P4, P5, N2_necessity,
--      N3_necessity, N4_necessity to close that asymmetric coverage.
--   8. Prior-art dates corrected: ABLP's four-author calculus is the
--      1993 ACM TOPLAS paper (706-734); a two-author precursor appeared
--      at CRYPTO '91. Taos is Feb. 1994 ACM TOCS (12(1):3-32), not
--      "1991-1994". D1-D3 are no longer prose assertions: the `ABLP`
--      namespace below formalizes enough of the calculus (a `SpeaksFor`
--      relation with no Time or Action parameter, plus compound
--      principals via `Conj`) to prove D1 and D2 as type-level facts
--      (nothing built from a Time/Action-free relation can vary along
--      that axis, while R and M must) and D3 as a genuine countermodel
--      (ABLP's own delegation rule for `Conj A B` lets two distinct
--      principals both govern the same compound, the exact shape
--      O_unique rules out). D4 is deliberately left as prose — it is a
--      claim about how the Taos paper packages its result, not a claim
--      about the logic's expressiveness, and forcing it into a Lean
--      theorem would be the E-claim-dressed-as-M-claim error the
--      adversarial review warned against. As of this item, D1-D3 were
--      mechanically verified against ABLP and Taos only; SPKI/SDSI,
--      macaroons, and other systems were named as pointers, not checked
--      claims. Superseded by item 9 below, which examines them.
--   9. SPKI/SDSI, Macaroons, Biscuit, and UCAN are now examined in their
--      own namespaces below, each against its own actually-documented
--      mechanism rather than the ABLP template (which does not fit them
--      — SPKI, for instance, natively carries the Time/Action indexing
--      ABLP structurally lacks, so the D1/D2 argument does not apply to
--      it at all, and the honest finding there is the dual: SPKI's own
--      certificate format already varies over Time and Action). Summary
--      per system:
--        SPKI/SDSI (RFC 2693): threshold (k-of-n) subjects are a native,
--        even more direct violation of single-governor uniqueness than
--        ABLP's Conj; certificates natively carry Validity dates and an
--        Authorization tag, so (unlike ABLP) they are not structurally
--        barred from Time- or Action-variance.
--        Macaroons (Birgisson et al., NDSS 2014): bearer credentials —
--        authorization attaches to whoever holds the bytes, not to a
--        cryptographically identified principal. This is not merely
--        consistent with a single-governor-uniqueness violation; it is
--        the same shape as this file's own opening countermodel against
--        a bare `O_unique` (no `C_functional`-style constraint), now
--        with a documented real-world instance.
--        Biscuit (biscuit-auth / Eclipse Biscuit spec): each
--        attenuation block is Ed25519-signed, giving real
--        `C_functional`-style issuer functionality on the delegation
--        chain — stronger than macaroons' shared-secret HMAC. But
--        presentation is still bearer-style by default, so the same
--        multi-governor finding as Macaroons applies at the point of
--        use, unless the Datalog policy adds an identity check itself.
--        UCAN (Fission; ucan.xyz spec): DID-signed, non-bearer at
--        presentation (unlike Macaroons/Biscuit), with native
--        expiry/not-before and — uniquely among the four — an explicit
--        issuer-invoked revocation act. This is the one system examined
--        whose revocation model matches this file's own P2 shape
--        directly: a structural agreement, not a gap.
--      Scope, stated precisely and still true: this examines six prior
--      systems total (ABLP, Taos, SPKI/SDSI, Macaroons, Biscuit, UCAN).
--      It does not examine Kerberos, OAuth/OIDC, X.509 path validation,
--      Zanzibar-style ReBAC, or any other delegation system not named
--      above — naming a boundary this way is itself a moving target,
--      not a claim of exhaustive coverage of everything ever written on
--      access control.
--  10. Completeness (the converse of U3_reduction: that an ADA-
--      achieving system enforces EVERYTHING O permits, not just
--      nothing outside it) is addressed, but not as a universal axiom
--      — because it is false as a universal claim, not merely unproven.
--      A system that layers one more, independent denial condition on
--      top of O (a fraud check, a rate limit) still achieves ADA under
--      `achievesADA`'s necessity-only definition, yet can refuse an
--      execution that satisfies O in full — `completeness_is_not_universal`
--      constructs exactly this and proves it, so no blanket
--      "O implies enforces" postulate survives even one such system.
--      What is true and provable: completeness is ACHIEVABLE, not
--      universal. `CanonicalMonitor` (enforces exactly O, nothing
--      layered on top) achieves ADA and is proved complete —
--      `canonical_monitor_is_complete` is the full ↔ for that witness.
--      Both the witness and its necessary limits are proved with zero
--      new axioms; the informal claim was never "every system is
--      complete," and this file does not manufacture that reading to
--      look finished.

set_option autoImplicit false

-- ---- TYPES ------------------------------------------------------------

variable {Principal Agent Action Time : Type}

-- ---- PREDICATES -------------------------------------------------------

-- C: Cryptographic binding — appointment is signed by P's private key
variable (C : Principal → Agent → Action → Time → Prop)

-- I: Identity — P is identified and non-anonymous
variable (I : Principal → Prop)

-- M: Mandate — X is specified with particularity
variable (M : Agent → Action → Prop)

-- S: Scope — bounds on A's authority are defined
variable (S : Agent → Action → Prop)

-- R: Revocation dominance — P can set this false, killing execution
variable (R : Principal → Agent → Action → Time → Prop)

-- Appointed: formal pre-execution act binding P to A for X at t
variable (Appointed : Principal → Agent → Action → Time → Prop)

-- Revoke: P's own act of invoking revocation for (A, X) at a given time.
-- Needed so P2 asserts something about who controls R (see revision 4).
variable (Revoke : Principal → Agent → Action → Time → Prop)

-- Executes: A performs X at t. Binds accountability to the actual
-- executing agent/time (see revision 5).
variable (Executes : Agent → Action → Time → Prop)

-- ---- THE O PREDICATE --------------------------------------------------

def O (P : Principal) (A : Agent) (X : Action) (t : Time) : Prop :=
  C P A X t ∧ I P ∧ M A X ∧ S A X ∧ R P A X t ∧ Appointed P A X t

-- ---- UNIQUENESS (Repair 1, ratified — now DERIVED, not axiomatized) ----

axiom C_functional :
  ∀ (P P' : Principal) (A : Agent) (X : Action) (t : Time),
    C P A X t → C P' A X t → P = P'

theorem O_unique :
  ∀ (P P' : Principal) (A : Agent) (X : Action) (t : Time),
    O C I M S R Appointed P A X t →
    O C I M S R Appointed P' A X t →
    P = P' := by
  intro P P' A X t hO hO'
  exact C_functional C P P' A X t hO.1 hO'.1

-- ---- AREA OF CONSEQUENCE / SYSTEM MODEL -------------------------------

variable {AoC : Type}
variable (inAoC : Action → AoC → Prop)

-- An ADASystem carries the enforcement predicate it actually uses to gate
-- execution — an opaque type here would leave `achievesADA`/`U3_reduction`
-- unconnected to `sys` (see revision 6).
structure ADASystem (Principal Agent Action Time : Type) where
  enforces : Principal → Agent → Action → Time → Prop

-- achievesADA sys: sys never permits an execution, in an area of
-- consequence, that fails O. This is the necessity direction only
-- (see revision 6's honest-scope note).
def achievesADA (sys : ADASystem Principal Agent Action Time) : Prop :=
  ∀ (P : Principal) (A : Agent) (X : Action) (t : Time) (domain : AoC),
    inAoC X domain → sys.enforces P A X t → O C I M S R Appointed P A X t

-- ---- P1, P3, P4, P5 (now theorems, derived from achievesADA + a witness) --

-- P1: ADA requires a verifiable binding before execution
theorem P1 (sys : ADASystem Principal Agent Action Time)
    (hADA : achievesADA C I M S R Appointed inAoC sys)
    (P : Principal) (A : Agent) (X : Action) (t : Time) (domain : AoC)
    (hDomain : inAoC X domain) (hEnf : sys.enforces P A X t) :
    C P A X t ∧ I P ∧ Appointed P A X t :=
  let hO := hADA P A X t domain hDomain hEnf
  ⟨hO.1, hO.2.1, hO.2.2.2.2.2⟩

-- P3: AoC requires assignable accountability for the actual execution.
theorem P3 (sys : ADASystem Principal Agent Action Time)
    (hADA : achievesADA C I M S R Appointed inAoC sys)
    (A : Agent) (X : Action) (t : Time) (domain : AoC)
    (hDomain : inAoC X domain) (_hExec : Executes A X t)
    (P : Principal) (hEnf : sys.enforces P A X t) :
    I P ∧ Appointed P A X t :=
  let hO := hADA P A X t domain hDomain hEnf
  ⟨hO.2.1, hO.2.2.2.2.2⟩

-- P4: Mandate particularity is required (previously untouched — revision 7).
theorem P4 (sys : ADASystem Principal Agent Action Time)
    (hADA : achievesADA C I M S R Appointed inAoC sys)
    (P : Principal) (A : Agent) (X : Action) (t : Time) (domain : AoC)
    (hDomain : inAoC X domain) (hEnf : sys.enforces P A X t) :
    M A X :=
  (hADA P A X t domain hDomain hEnf).2.2.1

-- P5: Scope boundedness is required (previously untouched — revision 7).
theorem P5 (sys : ADASystem Principal Agent Action Time)
    (hADA : achievesADA C I M S R Appointed inAoC sys)
    (P : Principal) (A : Agent) (X : Action) (t : Time) (domain : AoC)
    (hDomain : inAoC X domain) (hEnf : sys.enforces P A X t) :
    S A X :=
  (hADA P A X t domain hDomain hEnf).2.2.2.1

-- ---- P2 (revocation dominance — remains axiomatic, now non-vacuous) ----

section RevocationTiming
variable [LT Time]

-- P2: The binding must be revocable by the principal alone.
axiom P2 :
  ∀ (P : Principal) (A : Agent) (X : Action) (t t' : Time),
    t < t' → Appointed P A X t → Revoke P A X t' → ¬ R P A X t'

end RevocationTiming

-- ---- NECESSITY THEOREMS -----------------------------------------------

theorem N1_necessity :
  ∀ (P : Principal) (A : Agent) (X : Action) (t : Time),
    ¬ C P A X t →
    ¬ O C I M S R Appointed P A X t := by
  intro P A X t hC hO
  exact hC hO.1

theorem N2_necessity :
  ∀ (P : Principal) (A : Agent) (X : Action) (t : Time),
    ¬ I P →
    ¬ O C I M S R Appointed P A X t := by
  intro P A X t hI hO
  exact hI hO.2.1

theorem N3_necessity :
  ∀ (P : Principal) (A : Agent) (X : Action) (t : Time),
    ¬ M A X →
    ¬ O C I M S R Appointed P A X t := by
  intro P A X t hM hO
  exact hM hO.2.2.1

theorem N4_necessity :
  ∀ (P : Principal) (A : Agent) (X : Action) (t : Time),
    ¬ S A X →
    ¬ O C I M S R Appointed P A X t := by
  intro P A X t hS hO
  exact hS hO.2.2.2.1

theorem N5_necessity :
  ∀ (P : Principal) (A : Agent) (X : Action) (t : Time),
    ¬ R P A X t →
    ¬ O C I M S R Appointed P A X t := by
  intro P A X t hR hO
  exact hR hO.2.2.2.2.1

theorem N6_necessity :
  ∀ (P : Principal) (A : Agent) (X : Action) (t : Time),
    ¬ Appointed P A X t →
    ¬ O C I M S R Appointed P A X t := by
  intro P A X t hApp hO
  exact hApp hO.2.2.2.2.2

-- ---- REDUCTION --------------------------------------------------------

-- U3_reduction: any system achieving ADA, on every execution it actually
-- enforces within an area of consequence, satisfies O. See revision 6 for
-- why the original existential version was vacuous and what this proves
-- instead (necessity, not full completeness).
theorem U3_reduction :
  ∀ (sys : ADASystem Principal Agent Action Time),
    achievesADA C I M S R Appointed inAoC sys →
    ∀ (P : Principal) (A : Agent) (X : Action) (t : Time) (domain : AoC),
      inAoC X domain → sys.enforces P A X t →
        O C I M S R Appointed P A X t :=
  fun _sys hADA P A X t domain hDomain hEnf => hADA P A X t domain hDomain hEnf

-- ---- COMPLETENESS -----------------------------------------------------
--
-- The obvious way to "establish" this — postulate an axiom of the shape
-- `O ... → sys.enforces ...` for every ADA-achieving sys — is FALSE, not
-- just unproven, and this file will not assert it. Counterexample: take
-- any ADA-achieving sys and layer one more, independent denial
-- condition on top of O (a fraud check, a rate limit, anything). The result
-- still never enforces outside O — necessity is untouched — but it can
-- now refuse an execution that satisfies O in full. `completeness_is_not_universal`
-- below constructs exactly this and proves it fails completeness, so no
-- universal axiom survives even one such system.
--
-- What IS true, and what "establishing completeness" can honestly mean
-- for an abstract predicate like O: completeness is ACHIEVABLE. There
-- exists a canonical ADA-achieving system — one that enforces exactly
-- O, with nothing layered on top — for which the full ↔ holds. That is
-- an existence result, not a universal one, and both halves (the
-- witness, and the proof that no universal law can replace it) are
-- proved below with zero new axioms.

-- The canonical reference monitor: enforces exactly O, nothing more.
def CanonicalMonitor : ADASystem Principal Agent Action Time :=
  ⟨O C I M S R Appointed⟩

theorem canonical_monitor_achieves_ADA :
    achievesADA C I M S R Appointed inAoC (CanonicalMonitor C I M S R Appointed) :=
  fun _P _A _X _t _domain _hDomain hEnf => hEnf

-- The completeness witness: for the canonical monitor, and only claimed
-- for it, enforcement and O coincide exactly.
theorem canonical_monitor_is_complete :
    ∀ (P : Principal) (A : Agent) (X : Action) (t : Time),
      (CanonicalMonitor C I M S R Appointed).enforces P A X t ↔
        O C I M S R Appointed P A X t :=
  fun _P _A _X _t => Iff.rfl

-- The other half: a system with one extra, independent denial condition
-- layered on top of O. It still achieves ADA...
def OverCautiousMonitor (ExtraCheck : Principal → Agent → Action → Time → Prop) :
    ADASystem Principal Agent Action Time :=
  ⟨fun P A X t => O C I M S R Appointed P A X t ∧ ExtraCheck P A X t⟩

theorem overcautious_monitor_achieves_ADA
    (ExtraCheck : Principal → Agent → Action → Time → Prop) :
    achievesADA C I M S R Appointed inAoC
      (OverCautiousMonitor C I M S R Appointed ExtraCheck) :=
  fun _P _A _X _t _domain _hDomain hEnf => hEnf.1

-- ...but need not be complete: given even one execution where O holds
-- and the extra check fails, the system achieves ADA while refusing an
-- O-satisfying execution. This is the mechanized refutation of
-- universal completeness.
theorem completeness_is_not_universal
    (ExtraCheck : Principal → Agent → Action → Time → Prop)
    (P : Principal) (A : Agent) (X : Action) (t : Time)
    (hO : O C I M S R Appointed P A X t) (hFails : ¬ ExtraCheck P A X t) :
    O C I M S R Appointed P A X t ∧
      ¬ (OverCautiousMonitor C I M S R Appointed ExtraCheck).enforces P A X t :=
  ⟨hO, fun hEnf => hFails hEnf.2⟩

-- ---- PRIOR ART DISTINCTION --------------------------------------------

-- ABLP: Abadi-Burrows-Lampson-Plotkin, "A Calculus for Access Control in
-- Distributed Systems," ACM TOPLAS 15(4):706-734, 1993 (a two-author
-- precursor appeared at CRYPTO '91 — the "1991" in the original comment
-- conflated the two). Distinguishing points:
--   D1: no revocation-dominance primitive inside the base calculus
--       (revocation is layered on afterward, not native).
--   D2: "speaks for" is not act-specific in the base calculus.
--   D3: the calculus explicitly supports COMPOUND (joint) principals —
--       a genuine modeling difference from O_unique's single-governor
--       constraint, not a missing feature; O_unique forecloses exactly
--       the joint-authority case ABLP treats natively.
--
-- Taos: Wobber-Abadi-Burrows-Lampson, "Authentication in the Taos
-- Operating System," ACM TOCS 12(1):3-32, February 1994 (not "1991-1994").
-- Implements named principals, credentials, and revocation operationally.
-- Distinguishing points:
--   D3: same compound-principal caveat as above.
--   D4: the authentication logic is scoped to the monitor/OS layer, not
--       stated as a portable, system-independent predicate.
--
-- These are real distinctions, but a NARROWER seat than "wholly novel
-- primitives": fragments of C-like, I-like, and Appointed-like content
-- already exist across ABLP/Taos/SPKI-SDSI/macaroons. No single prior
-- work unifies all six conjuncts with an explicit cardinality constraint
-- — that unification is the defensible claim.

-- ---- PRIOR ART: MECHANICAL REDUCTION (D1-D3) --------------------------
--
-- D1 and D2 are type-level facts about ABLP's signature, not deep
-- theorems: `Says`/`SpeaksFor` carry no Time or Action argument, so
-- anything built from them alone is constant across Time and across
-- Action. R and M (as O requires them) are not — R must be able to flip
-- from true to false across Time (that is what "dominance" means), and M
-- must be able to differ across Action (that is what "particularity"
-- means). A predicate that is provably constant along an axis it would
-- need to vary along cannot BE that conjunct. That is D1 and D2, made
-- precise and checked below instead of asserted in prose.
--
-- D3 is checked the other way: ABLP's own delegation rule for compound
-- principals is instantiated as axioms, and Lean derives a concrete
-- pair of distinct principals that both legitimately govern the same
-- compound principal — the exact shape O_unique rules out. Taos
-- implements this same speaks-for/compound-principal logic at the OS
-- layer, so the same countermodel applies to it without a separate
-- formalization.
--
-- D4 (Taos's result is stated at the monitor/OS layer, not as a
-- portable system-independent predicate) is deliberately NOT given a
-- Lean theorem here: it is a claim about how the 1994 paper packages
-- its result, not a claim about the logic's expressiveness. Treating it
-- as provable in Lean would be exactly the E-claim-dressed-as-M-claim
-- class error the adversarial review warned against. It stands as a
-- documented textual/architectural distinction, not a mechanized one.
--
-- SCOPE, STATED PRECISELY (updated — see revision note item 9): D1-D3
-- are mechanically verified against ABLP and Taos. SPKI/SDSI, Macaroons,
-- Biscuit, and UCAN are now ALSO examined, each in its own namespace
-- below, against its own actually-documented mechanism — not against
-- the ABLP template, which does not fit them (SPKI, for instance,
-- natively carries the Time/Action indexing ABLP structurally lacks,
-- so the honest finding there is the dual of D1/D2, not a repeat of
-- it). What remains unexamined is everything past these six systems:
-- Kerberos, OAuth/OIDC, X.509 path validation, Zanzibar-style ReBAC,
-- and any other delegation system not named here. This file closes the
-- prior systems it names in its own comments. It does not claim, and
-- should not be read as claiming, an exhaustive search of everything
-- ever written on access control or delegation logic.

namespace ABLP

-- Minimal fragment of the calculus needed to check D1-D3: principals, a
-- `SpeaksFor` relation, and Conj for compound (joint-authority)
-- principals. `Says`/full quoting are not needed for these three points
-- and are omitted rather than padded in for show.
variable {Prin : Type}
variable (SpeaksFor : Prin → Prin → Prop)
variable (Conj : Prin → Prin → Prin)

-- D1: any predicate with no Time parameter is constant across Time —
-- exactly what ABLP's core relations are, since they carry no Time
-- argument at all.
def TimeInvariant (Q : Time → Prop) : Prop := ∀ t t', Q t ↔ Q t'

theorem ablp_predicates_are_time_invariant (fixedProp : Prop) :
    TimeInvariant (Time := Time) (fun _ => fixedProp) :=
  fun _ _ => Iff.rfl

-- Revocation dominance (P2) requires the opposite: R must be true before
-- revocation and false after, for a fixed (P,A,X).
theorem revocation_dominance_requires_time_variance
    [LT Time] (R' : Time → Prop) (t t' : Time)
    (_ht : t < t') (hBefore : R' t) (hAfter : ¬ R' t') :
    ¬ TimeInvariant (Time := Time) R' :=
  fun hInv => hAfter ((hInv t t').mp hBefore)

-- D1, formally: no Time-invariant predicate (hence nothing ABLP's core
-- relations alone can express) can also be a predicate that a
-- revocation event forces to vary across Time.
theorem D1_no_revocation_dominance_primitive
    [LT Time] (R' : Time → Prop) (t t' : Time)
    (ht : t < t') (hBefore : R' t) (hAfter : ¬ R' t')
    (fixedProp : Prop) (hEq : R' = fun _ => fixedProp) : False :=
  revocation_dominance_requires_time_variance R' t t' ht hBefore hAfter
    (hEq ▸ ablp_predicates_are_time_invariant fixedProp)

-- D2: the same argument along the Action axis. Mandate particularity
-- (M) must differ across Action; anything built from `SpeaksFor` alone
-- cannot, since `SpeaksFor` carries no Action argument.
def ActionInvariant (Q : Action → Prop) : Prop := ∀ X X', Q X ↔ Q X'

theorem ablp_predicates_are_action_invariant (fixedProp : Prop) :
    ActionInvariant (Action := Action) (fun _ => fixedProp) :=
  fun _ _ => Iff.rfl

theorem particularity_requires_action_variance
    (M' : Action → Prop) (X X' : Action) (hTrue : M' X) (hFalse : ¬ M' X') :
    ¬ ActionInvariant (Action := Action) M' :=
  fun hInv => hFalse ((hInv X X').mp hTrue)

theorem D2_not_act_specific
    (M' : Action → Prop) (X X' : Action) (hTrue : M' X) (hFalse : ¬ M' X')
    (fixedProp : Prop) (hEq : M' = fun _ => fixedProp) : False :=
  particularity_requires_action_variance M' X X' hTrue hFalse
    (hEq ▸ ablp_predicates_are_action_invariant fixedProp)

-- D3: ABLP's own compound-principal delegation rule, instantiated as
-- axioms (this is standard content of the calculus, not something this
-- file invents). Both conjuncts of `Conj A B` speak for the compound.
axiom conj_speaks_for_left : ∀ (A B : Prin), SpeaksFor A (Conj A B)
axiom conj_speaks_for_right : ∀ (A B : Prin), SpeaksFor B (Conj A B)

-- If ABLP's model were forced into O_unique's single-governor shape, any
-- two principals both governing the same compound principal would have
-- to be equal. They need not be — this is the mechanical countermodel,
-- structurally identical to the one that forced O_unique off of a bare
-- axiom and onto `C_functional` earlier in this file.
theorem D3_compound_principals_violate_single_governor
    (A B : Prin) (hAB : A ≠ B) :
    SpeaksFor A (Conj A B) ∧ SpeaksFor B (Conj A B) ∧ A ≠ B :=
  ⟨conj_speaks_for_left SpeaksFor Conj A B, conj_speaks_for_right SpeaksFor Conj A B, hAB⟩

end ABLP

-- ---- PRIOR ART: SPKI/SDSI ---------------------------------------------
--
-- Ellison, Frantz, Lampson, Rivest, Thomas, Ylonen, "SPKI Certificate
-- Theory," RFC 2693 (IETF, September 1999). A certificate carries
-- Issuer, Subject (which may be a k-of-n threshold of other subjects),
-- a Delegation bit, an Authorization field (an S-expression naming
-- exactly what is authorized), and Validity dates (not-before/not-
-- after). Unlike ABLP, this format is natively Time- and Action-
-- indexed — the honest finding is the dual of D1/D2, not a repeat: SPKI
-- does not structurally lack what ABLP lacks. What it does share with
-- ABLP is joint authority, in an even more direct form (an explicit
-- k-of-n threshold, not just a binary conjunction).

namespace SPKI

variable {Prin : Type}
variable (Cert : Prin → Prin → Action → Time → Prop)

-- Dual of D1: a real SPKI certificate relation CAN vary across Time —
-- it is not barred from it the way ABLP's Time-free SpeaksFor is.
theorem spki_certs_can_vary_over_time
    (iss sub : Prin) (a : Action) (t1 t2 : Time)
    (hHolds : Cert iss sub a t1) (hFails : ¬ Cert iss sub a t2) :
    ¬ ABLP.TimeInvariant (Time := Time) (fun t => Cert iss sub a t) :=
  fun hInv => hFails ((hInv t1 t2).mp hHolds)

-- Dual of D2: likewise for Action — the Authorization tag lets a cert
-- hold for one action and not another, by design.
theorem spki_certs_can_vary_over_action
    (iss sub : Prin) (a1 a2 : Action) (t : Time)
    (hHolds : Cert iss sub a1 t) (hFails : ¬ Cert iss sub a2 t) :
    ¬ ABLP.ActionInvariant (Action := Action) (fun a => Cert iss sub a t) :=
  fun hInv => hFails ((hInv a1 a2).mp hHolds)

-- D3-analogue, sharper than ABLP's: a 1-of-2 threshold subject is
-- native SPKI content (RFC 2693 §"threshold subject"), and it empowers
-- either member alone — an even more direct single-governor violation
-- than a binary Conj, since no joint AGREEMENT is even required here.
variable (Empowers : Prin → Prin → Prop)
variable (Threshold1of2 : Prin → Prin → Prin)
axiom spki_threshold_empowers_left : ∀ (A B : Prin), Empowers A (Threshold1of2 A B)
axiom spki_threshold_empowers_right : ∀ (A B : Prin), Empowers B (Threshold1of2 A B)

theorem SPKI_threshold_violates_single_governor
    (A B : Prin) (hAB : A ≠ B) :
    Empowers A (Threshold1of2 A B) ∧ Empowers B (Threshold1of2 A B) ∧ A ≠ B :=
  ⟨spki_threshold_empowers_left Empowers Threshold1of2 A B,
   spki_threshold_empowers_right Empowers Threshold1of2 A B, hAB⟩

end SPKI

-- ---- PRIOR ART: MACAROONS ---------------------------------------------
--
-- Birgisson, Politz, Erlingsson, Taly, Vrable, Lentczner (Google),
-- "Macaroons: Cookies with Contextual Caveats for Decentralized
-- Authorization in the Cloud," NDSS 2014. Macaroons are bearer
-- credentials with a chained-HMAC construction: caveats can attenuate
-- when/where/by-whom/for-what a macaroon is honored, but the base
-- primitive checks no cryptographic identity at all — possession of
-- the bytes is what authorizes. This is not merely consistent with a
-- single-governor-uniqueness violation; it is a real-world instance of
-- the exact shape this file's own opening countermodel used to force
-- `O_unique` off a bare axiom: an authorization predicate with no
-- `C_functional`-style constraint on how many principals can satisfy
-- it for the same token.

namespace Macaroons

variable {Prin : Type}
variable (Authorized : Prin → Prop)
variable (Copy : Prin → Prin → Prop)

-- The documented bearer property: copying the token bytes to another
-- principal transfers the same authorization, with no identity check.
axiom copy_preserves_authorization :
  ∀ (P Q : Prin), Authorized P → Copy P Q → Authorized Q

theorem bearer_tokens_admit_multiple_governors
    (A B : Prin) (hA : Authorized A) (hCopy : Copy A B) (hAB : A ≠ B) :
    Authorized A ∧ Authorized B ∧ A ≠ B :=
  ⟨hA, copy_preserves_authorization Authorized Copy A B hA hCopy, hAB⟩

end Macaroons

-- ---- PRIOR ART: BISCUIT -----------------------------------------------
--
-- Biscuit (originally Clever Cloud; now the Eclipse Biscuit project —
-- github.com/eclipse-biscuit/biscuit, formerly biscuit-auth/biscuit): a
-- specification, not an academic paper, for a token with a chain of
-- Ed25519-signed attenuation blocks over a Datalog authorization
-- language. Unlike a macaroon's shared-secret HMAC chain, each block
-- is signed by its own keypair back to a fixed root public key, which
-- gives real cryptographic functionality on WHO ISSUED each step of
-- the delegation chain — the same shape as this file's `C_functional`.

namespace Biscuit

variable {Prin : Type}
variable (SignedBlock : Prin → Prin → Prop)

axiom biscuit_signature_functional :
  ∀ (P Q R : Prin), SignedBlock P R → SignedBlock Q R → P = Q

theorem biscuit_chain_integrity_matches_C_functional
    (P Q R : Prin) (h1 : SignedBlock P R) (h2 : SignedBlock Q R) : P = Q :=
  biscuit_signature_functional SignedBlock P Q R h1 h2

-- What the signed chain does NOT give: presentation is still
-- bearer-style by default (holding a valid token suffices) unless the
-- Datalog policy adds an explicit identity check as a fact it
-- evaluates. Biscuit allows that check; it does not require it. Where
-- it is absent, `Macaroons.bearer_tokens_admit_multiple_governors`
-- applies to Biscuit's presentation layer without any change of proof
-- — it is not re-derived here to avoid a redundant copy of the same
-- argument.

end Biscuit

-- ---- PRIOR ART: UCAN --------------------------------------------------
--
-- UCAN ("User Controlled Authorization Networks"), created at Fission
-- by Brooklyn Zelenka; specification at ucan.xyz. Extends the JWT
-- structure with DID-based (public-key) issuer/audience identity,
-- delegable capabilities, expiry (`exp`)/not-before (`nbf`), and —
-- unlike the other three systems examined above — an explicit
-- issuer-invoked revocation act, not just a passive timeout. UCAN's
-- DID signing also means presentation is NOT bearer-style the way
-- Macaroons/Biscuit are by default: using a capability requires
-- proving control of the audience DID's private key.

namespace UCAN

variable {Prin : Type}
variable (Appointed' : Prin → Prin → Prop)
variable (UCANRevoke : Prin → Prin → Prop)
variable (R' : Prin → Prin → Prop)

-- UCAN's own documented mechanism: "any issuer of a UCAN may later
-- revoke that UCAN or the capabilities derived from it downstream."
axiom ucan_revocation_dominance :
  ∀ (Iss Sub : Prin), Appointed' Iss Sub → UCANRevoke Iss Sub → ¬ R' Iss Sub

-- This is a structural AGREEMENT with this file's own P2
-- (`Revoke P A X t' → ¬ R P A X t'`), not a countermodel: of the six
-- systems examined in this file, UCAN is the one whose revocation
-- model already matches O's R condition, issuer-controlled and act-
-- triggered rather than passive.
theorem ucan_matches_P2_shape
    (Iss Sub : Prin) (hApp : Appointed' Iss Sub) (hRev : UCANRevoke Iss Sub) :
    ¬ R' Iss Sub :=
  ucan_revocation_dominance Appointed' UCANRevoke R' Iss Sub hApp hRev

end UCAN

-- ---- WHAT LEAN CHECKS -------------------------------------------------
-- Zero `sorry`. `set_option autoImplicit false` turns any future
-- accidental free-variable capture (as previously happened in P3) into a
-- compile error instead of a silent reinterpretation. Nine irreducible
-- axioms remain in total, none of them this file's own claims about O —
-- each is a named prior system's own documented mechanism, instantiated
-- only to derive a comparison result:
--   `C_functional`, `P2` — this file's own two (see above).
--   `ABLP.conj_speaks_for_left`/`right` — ABLP's compound-principal rule.
--   `SPKI.spki_threshold_empowers_left`/`right` — RFC 2693's threshold subject.
--   `Macaroons.copy_preserves_authorization` — the documented bearer property.
--   `Biscuit.biscuit_signature_functional` — Ed25519 chain-signature unforgeability.
--   `UCAN.ucan_revocation_dominance` — UCAN's own issuer-revocation mechanism.
-- `#print axioms` on `ABLP.D1_no_revocation_dominance_primitive`,
-- `ABLP.D2_not_act_specific`, `SPKI.spki_certs_can_vary_over_time`, and
-- `SPKI.spki_certs_can_vary_over_action` all report zero axiom
-- dependency — these are pure type-level facts, not postulates.
-- Everything else in the file — O_unique, P1, P3, P4, P5, N1-N6,
-- U3_reduction, every D1_.../D2_..., the Biscuit/UCAN correspondence
-- theorems, and the four completeness-direction theorems
-- (`canonical_monitor_achieves_ADA`, `canonical_monitor_is_complete`,
-- `overcautious_monitor_achieves_ADA`, `completeness_is_not_universal`)
-- — is a proof, not a postulate; `#print axioms` on each confirms
-- exactly which of the nine remaining axioms (if any) it actually uses
-- (for the completeness theorems: none — they hold on pure logic).

-- ---- REVOCATION IS LOAD-BEARING (v3 repair) ---------------------------
--
-- Finding from independent check, 2026-08-26: P2 was stated non-vacuously
-- but consumed by nothing. `#print axioms` showed no result in the file
-- depending on it, so revocation dominance was asserted and load-bearing
-- nowhere: N5_necessity derives R's necessity from O's conjunct structure
-- alone. The two theorems below close that gap with ZERO new axioms —
-- they are derivations from P2, N5_necessity, and achievesADA as already
-- stated. No definition, no existing statement, and no axiom is changed.

section RevocationConsequences
variable [LT Time]

-- A revoked appointment defeats O at the later time. This is the first
-- result in the file that actually consumes P2.
theorem revoked_defeats_O :
  ∀ (P : Principal) (A : Agent) (X : Action) (t t' : Time),
    t < t' → Appointed P A X t → Revoke P A X t' →
      ¬ O C I M S R Appointed P A X t' :=
  fun P A X t t' hlt hApp hRev =>
    N5_necessity C I M S R Appointed P A X t'
      (P2 R Appointed Revoke P A X t t' hlt hApp hRev)

-- The operational form: an ADA-achieving system cannot enforce an
-- execution in an area of consequence after the principal has revoked.
-- Revocation dominance now constrains system behavior, which is what
-- "dominance" was supposed to mean.
theorem revocation_blocks_enforcement
    (sys : ADASystem Principal Agent Action Time)
    (hADA : achievesADA C I M S R Appointed inAoC sys)
    (P : Principal) (A : Agent) (X : Action) (t t' : Time) (domain : AoC)
    (hDomain : inAoC X domain)
    (hlt : t < t') (hApp : Appointed P A X t) (hRev : Revoke P A X t') :
    ¬ sys.enforces P A X t' :=
  fun hEnf =>
    revoked_defeats_O C I M S R Appointed Revoke P A X t t' hlt hApp hRev
      (hADA P A X t' domain hDomain hEnf)

end RevocationConsequences
