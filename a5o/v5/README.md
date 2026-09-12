# A⁵O v5 — deployment closure, successor to sealed v1

## Provenance

`Deployment.lean` and `DeploymentTests.lean` in this directory originate from
an externally supplied repair candidate, not authored in this repository. As
delivered, the candidate did not compile: `at` was used as a structure field
name, a reserved Lean token, producing cascading parse errors, and its own
verification report had never actually been run through a Lean kernel. The
candidate was patched and independently verified by the Code session across
two sittings — the field rename, elaborator-visibility fixes for `by decide`
sites, and a further round removing `propext` from all but one fixture proof.
`SOURCE_FIXES.patch` in this directory is the complete diff from the
as-delivered candidate to the files committed here. `A5O.lean` and
`Closure.lean` are unmodified, byte-identical copies of the sealed v4 files
(hashes below) — nothing about the foundation changed.

## Toolchain

`leanprover/lean4:v4.33.1` — the same compiler-of-record as the sealed v4/v1
record. The candidate was originally verified under 4.19.0; migration to
4.33.1 was attempted and succeeded without changes to any file, so there is
no toolchain heterogeneity in the record.

## Axiom status

95 of the 96 theorems in `Audit.lean`'s inventory report zero axioms — 96
across all four imported modules (`A5O.lean` 33, `Closure.lean` 16,
`Deployment.lean` 14, `DeploymentTests.lean` 33; 47 are v5's own). One,
`Apertures.Tests.phantom_not_listed` (`¬ (phantom ∈ demo.executions)`, a
demonstration-file fixture, not a core theorem), depends on `propext`. This
was investigated directly, not merely disclosed: Lean's own `List.mem_cons`
and `List.mem_singleton` lemmas are themselves `propext`-dependent in the
stdlib, and excluding an impossible case in dependent elimination against a
non-matching concrete list element routes through the same dependency —
confirmed under both 4.19.0 and 4.33.1, via direct `List.Mem` constructors,
and via raw term-mode `match`. No proof strategy tried avoided it. Every
other membership fact in the file — all of them positive — was rewritten
using `List.Mem.head`/`List.Mem.tail` directly rather than the stdlib's `Iff`
lemmas, which removed `propext` everywhere it appeared except this one
negative case. Nothing in `A5O.lean`, `Closure.lean`, or core `Deployment.lean`
uses `propext` or any other axiom.

## What this is and is not

`Deployment.lean` here supersedes nothing sealed. The sealed v1
`Deployment.lean` (`a5o/v4/closure/`, hash `b6e79d8f…af67`) remains
unrevised, under its Operator Attestation as corrected. This directory is a
candidate file of record for the Gate's closure going forward; its own
`CheckersSound`, `DecisionsFollowChecker`, `NoSideChannel`, and
`CoversActualExecutions` evidence obligations are not yet attested for
`theapertures.app`, and its decision path does not yet read a server-held
ledger — see `a5o/v4/closure/README.md` for that item's status.

## Dated note (2026-09-12) — CheckersSound and CoversActualExecutions discharged for theapertures.app

The status described in "What this is and is not" above — `CheckersSound`,
`DecisionsFollowChecker`, `NoSideChannel`, and `CoversActualExecutions` "not
yet attested," decision path not yet reading a server-held ledger — is as of
this note superseded for a specific, bounded window. Left unrevised above
since it was accurate when written; recorded here rather than edited in
place.

Since that text was written, `apertures-app` gained a server-held,
hash-chained appointment ledger (`lib/ledger.js`) and six named checker
functions (`lib/gate.js` `runChecks()`) matching this file's `Checkers`
structure field-for-field, at commit `f683e50`. `a5o/v5/adapter/` (new in
this directory as of this note) contains a Lean adapter transliterating
those checkers and embedding a signed production trace
(`AperturesTrace_20260912.json`, nine receipts, four executions, ledger seq
30–32); it compiles under the toolchain above with no `sorry`, and proves
`DecisionsFollowChecker`, `NoSideChannel`, and `UniqueReceiptIds` by
computation, reaching a concrete instance of `trace_accountable` — every
obligation of `apertures_accountable` except `CheckersSound` and
`CoversActualExecutions`, which a Lean proof from trace data alone cannot
establish (they are claims about the running server, not the trace).

Those two are supplied by two operator attestations, `a5o/v5/closure/`:

- `Operator_Attestation_1of2_CheckersSound-2.pdf` — discharges `CheckersSound`.
  Verified clause-by-clause against `lib/gate.js`/`lib/ledger.js` at `f683e50`
  before signing, including one correction (the attestation is scoped to
  receipts issued on the default A5O-RCT-1.3.x path; the separate A5O-RCT-1.4
  path, `issue14()`, carries no `checks` block, writes no ledger/receipt/
  execution row, and is outside the trace). Envelope `faee154a-6a7a-40d9-9937-3d10ab75f0d2`,
  signed 2026-09-12T09:29:41Z.
- `Operator_Attestation_2of2_CoversActualExecutions-2.pdf` — discharges
  `CoversActualExecutions`. `insertExecution` (`lib/ledger.js`) has exactly one
  call site in the codebase (`lib/gate.js`, inside `issue()`'s single DB
  transaction with the receipt insert, gated by decision = ALLOW), and the
  `execution_log` schema enforces `CHECK (decision = true)` plus a foreign key
  into `issued_receipts (request_id, decision)` — confirmed by direct search,
  not assumed. Envelope `4a3121ab-db3f-4dcf-a760-980b11acbb56`, signed
  2026-09-12T09:30:17Z.

Both attestations are scoped to `apertures-app` commit `f683e50` and its
successors that leave the six checkers and the execution path unchanged,
under the production keys named in each instrument and ledger sequence 32; a
superseding attestation is required otherwise. Together with the adapter,
`apertures_accountable` now stands, without further condition, for every
actual execution at theapertures.app in the window of the cited trace: each
resolves to a principal for whom `A5O.lean` v4's `O` holds.

Full account of the verification round the trace itself records — which
buttons, in what order, expected vs. observed reason codes — is
`a5o/v5/closure/pre-attestation-verification-2026-09-12.md`.

## Reference hashes

```
A5O.lean                0e5ebe3f5113727ae0cd41ec4399661a352fcc4fb522fcfe7ef7be3318f6b452
Closure.lean            af6b3233bdeee80b8312a9138111c597d37f17b792a749d53844314e3a79a933
Deployment.lean         e07c69ae33d1d77e3c8e657f12f8a0fb58d233e8fd5873557c6564afcfdd59da
adapter/AperturesTrace_20260912.lean   96369a093189710eac6d6b2e3748d00f9996bb12a9045d15a4d38656de756e0b
adapter/AperturesTrace_20260912.json   c5ba5e2cfa4be0f8e9f9a97259f3bdaf2666fe7bb85d44d03d039e9803e19ed5
```
