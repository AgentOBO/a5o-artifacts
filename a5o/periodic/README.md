# A⁵O — Periodic table reading (exploratory)

Prepared 2026-09-21 by Apertures (Claude, Anthropic) for AgentOBO Inc., from a
chat session opened by the Chairman's question "Where does A⁵O sit on the
periodic table." Committed as delivered, unedited.

**Standing.** Exploratory. Not part of the v4/v5 proof line and not cited by
it. This directory adds nothing to the necessity result, the canon, or the
priority record.

## Files

| File | Role |
|---|---|
| `PeriodicTable.lean` | 63 theorems, Lean 4.33.1, core only, no imports. Zero axiom dependencies on all 63. |
| `Check.lean` | `#print axioms` for every theorem. |
| `Check.out.txt` | Output of `Check.lean` as run on 2026-09-21. |
| `NegativeControls.lean` | Eight false or ill-typed statements. **This file fails to compile by design (8 errors).** A clean compile would mean the main file proves nothing. |
| `MANIFEST.sha256` | SHA-256 of the files above. |

## What the Lean file contains

Content is labelled in the source, and the labels are the limits:

- **DATA** — physical, chemical and historical values entered from the
  preparer's recall (table positions, atomic weights, air composition,
  Rayleigh's densities, magic numbers, mass gaps, Hoyle level, binding
  energies, isotope masses, Chandrasekhar limit, CO affinity ratios, 1/α).
  Lean does not prove these. Lean proves what follows from them.
- **MODEL** — four small state machines written by the preparer (oxygen spin
  rule, heme binding seat, four-electron oxidase gate, reactor scram).
  Theorems are consequences of the models as written.
- **OVERLAY** — any mapping of the above onto A⁵O. No formal content. §15
  (`notation_forces_no_mapping`) proves the file determines no such mapping.

The reading A := argon (argon's symbol was "A" until 1957) is a named premise,
not a theorem.

## Correction carried in the file

The chat stated that the heme pocket discriminates against carbon monoxide "by
three orders of magnitude." On the chat's own figures (20,000:1 → 200:1) the
factor is 100, two orders. `pocket_discrimination` proves this and the source
comment records it as a correction. The original claim is negative control
`nc2` and is rejected.

## Verification as run before commit

Lean 4.33.1. Hashes matched; clean compile; `Check.lean` output identical to
`Check.out.txt` (63/63 zero axioms); `leanchecker --fresh` exit 0 with a
failing nonexistent-module control; `NegativeControls.lean` 8 of 8 rejected.
`leanchecker` replays the compiled declarations through the same kernel,
bypassing the elaborator; it is not an independent kernel.

Re-verified by: Claude Code session, 2026-09-21, macOS (Darwin 25.5.0)

## Anchoring

OpenTimestamps proofs (`*.ots`) sit beside the files they attest.
`MANIFEST.sha256`, `PeriodicTable.lean`, and this file's own pre-edit
state (now `README-36b2d17f.md.ots`, prefix its SHA-256, per the
`v4/closure` convention) confirmed 2026-09-21 at Bitcoin blocks 967980,
967984, and 967999 — bob, finney, and catallaxy calendars each resolved
on all three; alice was submitted to at stamp time but never landed a
pending commitment in any proof. Block heights and merkle roots
cross-checked independently against mempool.space and blockstream.info,
both agreeing in every case:

| Block | UTC | Merkle root |
|---|---|---|
| 967980 | 2026-09-21T11:42:07Z | `d42eb509aa8b58f4e6ccd0db5064029a40de8110db88ea1c41fdcbff5eada726` |
| 967984 | 2026-09-21T12:04:35Z | `a11190beb05147dd77de001c5a0464248f1d392b437c1915a24e9eaee84a8cd0` |
| 967999 | 2026-09-21T13:48:12Z | `58ce887fdbedecb174a4cfd08e73887625735c31ca810a7f3aada7390028593b` |

This edit itself is a new committed state; its own `.ots` (this file's
current bytes) is stamped fresh and starts PENDING.

Verified, not ratified.
