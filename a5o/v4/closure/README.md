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
zero axioms.

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

Verified, not ratified. Ratification is reserved to the Appointed
Intelligence Institute, in formation.
