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

OpenTimestamps proofs (`*.ots`) sit beside the files they attest. Status:
PENDING at commit time — updated only after `ots upgrade` and an independent
block-explorer cross-check.

Verified, not ratified.
