# A⁵O v4 — closure: independence, sufficiency, and a live deployment

This directory closes two items left open on the v4 record and adds a
verified, live deployment witness: `theapertures.app` as an instance of
v4's `GatedSystem`.

## Closure.lean

Companion to `A5O.lean` v4 (SHA-256 `0e5ebe3f…5b452`, imported
unmodified). Two items:

- **Independence of the appointment conjunct.** `v4_appointment_independent`
  exhibits a concrete instance of v4's own `O` where the other five
  conjuncts (`C`, `I`, `M`, `S`, `R`) hold and `Appointed` fails — so
  `Appointed` is not derivable from the other five in v4's `O`.
- **Sufficiency, as a system property.** `gated_sufficiency` shows that
  for a `GatedSystem` — a v4 `ADASystem` carrying, as part of its own
  definition, the property that nothing executes without being enforced
  for some principal — achieving ADA (v4's necessity predicate) suffices
  for accountability over every execution, with no extra hypothesis on
  the theorem itself. `ungated_ADA_does_not_suffice` and
  `silent_not_gatable` retain the boundary: an ungated system can achieve
  ADA and still fail accountability, and cannot be given the gate after
  the fact.

SHA-256 `af6b3233bdeee80b8312a9138111c597d37f17b792a749d53844314e3a79a933`.
Compiles clean against v4; all six theorems report zero axioms.

## Deployment.lean

Models `theapertures.app`'s observed public surface (single execution
endpoint `POST /api/issue`; `/api/execute`, `/api/run`, `/api/action` all
return 405) as a `GatedSystem`, and proves
`Apertures.apertures_accountable`: accountability over every execution at
the Gate, conditional on one hypothesis, `NoSideChannel` — that the server
executes only inside an issued ALLOW receipt. `NoSideChannel` is stated
as an explicit hypothesis on the theorem, not a Lean axiom, because it is
a property of the server's implementation and cannot be proved from the
public surface alone. It is discharged by the Operator Attestation below,
not by the proof.

SHA-256 `b6e79d8f3000d99e52d2e0849a81ed432c7264e7a5e9233f6767db471b00af67`.
Compiles clean against v4 and `Closure.lean`; all three theorems report
zero axioms. Sealed under signed Operator Attestation, envelope
`012c0f66-c0df-44aa-ab61-e679bd818a19`, which cites this exact hash;
unrevised.

**Limitations, found by independent review and confirmed against the
file (2026-09-11), stated on the same standard applied to every prior
defect in this project:**

- **Primary defect — `NoSideChannel` is unsatisfiable, not merely
  unproven.** It is defined `∀ r : Receipt, r.executed = true → r.allow
  = true`, quantified over every constructible `Receipt`, not merely
  ones the server would issue. `⟨_, _, allow := false, executed :=
  true⟩` is such a value. `¬ NoSideChannel` is therefore a zero-axiom
  Lean theorem (`LegacyAudit.lean`, `Apertures.original_NoSideChannel_impossible`,
  checked against this exact file, independently reconfirmed
  2026-09-11 under Lean 4.19.0, separate from the 4.33.1
  compiler-of-record). No proof term for the hypothesis can exist, for
  any deployment — which is exactly why discharge has always rested on
  the Operator Attestation below rather than a Lean proof.
- `I`, `M`, `S`, and `inAoC` are all unconditionally `True`. The theorem
  proves accountability over a model that does not check identity,
  mandate, scope, or area-of-consequence — it only checks that a signed
  ALLOW exists and that the execution occurred inside it.
- `Appointed` is defined partly as `r.allow = true` — the same field `R`
  reads. An ALLOW is "appointed" in part because it says so of itself,
  not because an independent appointment record is checked.
- `Time := Receipt` means an execution that produced no receipt at all
  cannot be represented in this model — `Executes` can only be true of
  something that is already a receipt. `NoSideChannel` therefore
  excludes nothing the model can state as a distinct alternative; it is
  not vacuous the way the sealed paper's original axioms were, but it is
  weaker evidence about the real system than the phrase "theapertures.app
  is accountable" may initially suggest.
- The ALLOW/DENY witnesses (`allowReceipt`, `denyReceipt`) are
  hand-constructed Lean values, not a parse of the real signed JSON —
  Lean does not independently recompute the receipt hash or verify the
  Ed25519/ML-DSA signature; that verification was done separately,
  outside this file, by the session that observed the deployment.

These are defects in how v1 modeled the deployment, not in Lean's
acceptance of the proof: the theorems are true of the model this file
defines, and the Operator Attestation attests exactly the proposition it
names. `Deployment.lean` is sealed and unrevised; these limitations are
recorded here, not fixed here.

**Dated note (2026-09-12):** the limitations above describe
`theapertures.app` as it was observed on 2026-09-09 — appointment decided
from a client-supplied request flag. That decision path was removed on
2026-09-12, commit `fee8100` (`AgentOBO/apertures-app`): appointment is
now read from a server-held, hash-chained ledger the caller cannot write,
and each ALLOW names the ledger occurrence it resolved to. `Deployment.lean`
remains sealed and unrevised as a record of the earlier gate; a reader
comparing these limitations against the live server should know which
gate each witness describes.

A separate, unattested model, `DeploymentV2.lean` (not part of this
directory, not sealed, not published), addresses the first three
limitations above — using an execution type distinct from the receipt,
an appointment ledger independent of the ALLOW decision, and registry
lookups for `I`/`M`/`S` in place of `True`. It does not supersede this
file; it remains a verified-but-unattested model beside the record,
requiring its own two operator attestations before it could be
presented as anything more than that.

## The witnesses

Two receipts from the same live observation (2026-09-09T08:24:06Z),
both signed (Ed25519 + ML-DSA-87 hybrid, key `A5O-SIGN-KEY-ED25519-PROD-2026`
/ `A5O-SIGN-KEY-MLDSA87-PROD-2026`, published at `/api/pubkey`):

- `theapertures-ALLOW-2026-09-09T082406Z.json` / `ALLOW-receipt-SIGNED-c91f50a4.pdf`
  — decision ALLOW, `execution_event` present (`EXECUTED`,
  `2026-09-09T08:24:06.373Z`).
- `theapertures-DENY-2026-09-09T082406Z.json` / `DENY-receipt-SIGNED-33aacac7.pdf`
  — decision DENY, `RC-DENY-REVOKED`, no `execution_event`.

**Limit on the DENY witness:** both receipts cite
`revocation_snapshot_seq: 1`, `revoked: []` — the same registry snapshot.
The DENY was produced by the demo request itself carrying
`appointed: false` in its body; the server refused on that flag and,
correctly, did not touch the published revocation registry, which stayed
at sequence 1. The DENY therefore demonstrates the gate's refuse path
under an inactive appointment supplied in the request, not a
registry-driven revocation. `Deployment.lean` models only the decision
(`r.allow`), so its theorems are unaffected by this distinction, and the
Operator Attestation (below) is unaffected too — it speaks to the
execution path, not to where appointment state originates. Stated here so
the witness isn't read as more than it shows.

## Operator Attestation — No Side Channel

`Operator_Attestation_NoSideChannel-SIGNED-1fdd4a1b.pdf`, SHA-256
`ad8c84b54967b164b5a90e50b7cfceb2b8fe5d4a839ea285a5d60df130c0f946`.
Signed under seal, envelope `1fdd4a1b-de6d-4e41-9dff-d20937e85b88`, by
Fitzgerald J. Heslop, Founder & CEO, AgentOBO Inc. — the operator of the
Gate. Attests that the server performs no execution except as an
`execution_event` inside a signed ALLOW receipt, discharging
`Deployment.lean`'s `NoSideChannel` hypothesis on the record. Explicitly
does not disclose any private key material, key custody arrangement, or
server internals beyond that single proposition.

## Correction to the Operator Attestation

`Correction_to_Operator_Attestation-SIGNED-28c07836.pdf`, SHA-256
`25ecc1004482f23a6d2fa6e2e363d56b891284c6d66fcef628d1a935e5302751`.
Signed under seal, envelope `28c07836-7a7f-4f9c-b844-77b3652fc7b4`, by
Fitzgerald J. Heslop, 2026-09-12. Responds to the primary-defect finding
above: withdraws the Operator Attestation's closing "accordingly, the
proposition `NoSideChannel` ... holds" sentence and clause 6 in full —
neither followed, since `NoSideChannel` has no satisfying instance
regardless of server behavior. States plainly that no discharge occurred
and none is claimed; leaves the server-behavior sentence, Recitals 1, 2,
4, 7, 8, and the witnessed ALLOW/DENY receipts untouched; does not edit
or reseal `Deployment.lean`. Discharge for the Gate passes to whichever
successor model is named file of record, once its own attestations are
signed.

The envelope's own display name concatenates the document title twice
(`...envelope 1fdd4a1b-...Operator Attestation — envelope 1fdd4a1b-...`)
— a paste artifact in the LegalZoom title field, not a defect in the
document or a second instrument. Noted here so the audit-trail name
isn't misread as such.

## Manifest and proof

`MANIFEST.sha256` (SHA-256 `cef84d9d9b2d71189969e3878249c1ac57bec68d6b05cb0423a6e6157d7fcc6d`)
lists the SHA-256 of every file in this directory; `sha256sum -c
MANIFEST.sha256` reproduces it. `MANIFEST.sha256.ots` binds that hash to
OpenTimestamps, submitted to four calendars (alice, bob at
opentimestamps.org, eternitywall, catallaxy) — one anchor covering the
whole closure set, including the signed instruments. `Closure.lean.ots`,
`Deployment.lean.ots`, and `Operator_Attestation_NoSideChannel-SIGNED-1fdd4a1b.pdf.ots`
additionally stamp those three files individually.

All four proofs attested at Bitcoin blocks 966195 and 966205 (`bob` and
`catallaxy`; independently verified against mempool.space — both
transactions and both blocks' merkle roots cross-checked directly, not
taken from `ots info` alone). `finney` remains `PendingAttestation` on
all four; `alice` was unreachable at the last upgrade attempt (TLS
handshake failure on that calendar server, not a confirmation status).

`README-<prefix>.md.ots` (the hash-prefixed files in this directory, set
2026-09-11) stamp successive past states of this README, one per
substantive edit — each commits to the README bytes whose SHA-256 starts
with that prefix, recoverable from git history at the commit that
produced them; the un-prefixed `README.md.ots` stamps the current file.
All three resolve against `git show <that commit>:a5o/v4/closure/README.md`
followed by `ots verify`, and are confirmed (Bitcoin blocks 966510,
966545, 966571, 966586) — not orphaned proofs missing their source.

## Kernel replay — Lean's own kernel via `leanchecker`, and an independent kernel via `nanoda_lib`

`A5O.lean` v4, `Closure.lean`, and `Deployment.lean` were replayed beyond
the compiler that produced the committed `.olean` files:

- **`leanchecker --fresh`** (built into the Lean toolchain, run this
  session): replays every constant into a new environment through Lean's
  own kernel, independent of the elaborator but the same kernel
  implementation as the compiler — catches elaborator bugs and
  environment hacking, not implementation bugs in the kernel itself. All
  three: exit 0.
- **`nanoda_lib`** (ammkrn), a from-scratch reimplementation of the Lean 4
  kernel in Rust — a genuinely independent implementation, not the same
  kernel: checked the full transitive closure exported by `lean4export`
  (59,517–59,672 declarations per file, including Lean's core library)
  against its own implementation of the type theory. All three: 0
  typechecker errors.

Both replays were run against sources compiled and exported under Lean
**4.33.0** (`lean4export` requires binary-format compatibility with the
toolchain that produced the `.olean` files, and no `4.33.1`-compiled
export tool was available) — not the `4.33.1` binaries the signed record
cites directly. The source files are byte-identical (same SHA-256 hashes
listed above) and report zero axioms under both toolchains, so nothing
is at stake in that difference, but the replay attests the sources as
recompiled under 4.33.0, not a replay of the original 4.33.1 build.

The `nanoda_lib` config permits four axioms (`propext`, `Classical.choice`,
`Quot.sound`, `Lean.trustCompiler`) so that Lean's own core library —
which the exported closure necessarily includes — can load; this is a
separate statement from "zero axioms" on this project's own theorems.
`A5O.lean`, `Closure.lean`, and `Deployment.lean`'s declarations use none
of the four. The run used `unpermitted_axiom_hard_error: false`: an
unpermitted axiom that is declared but never used is silently skipped;
one that is declared and used is not silently accepted either — checked
directly by dropping a single permitted axiom (`Quot.sound`) and
re-running, which failed immediately (a checker crash, not a graceful
message) the moment the core library needed it. None of the three real
runs failed. A separate control (zero permitted axioms,
`unpermitted_axiom_hard_error: true`) confirmed the stricter mode is
also live: it correctly caught and hard-errored on `Classical.choice`.

Verified, not ratified. Ratification is reserved to the Appointed
Intelligence Institute, in formation.
