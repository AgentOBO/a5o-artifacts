# A⁵O — Lean 4 source, three versions

This directory publishes the Lean 4 formalization behind *A Machine-Checked
Necessity Result for Accountable Delegated Authority* (28 Aug 2026) in three
distinct, separately verified forms. None is "the" verified source on its
own — each is labeled, and the label is load-bearing.

## v2 — what the paper describes

`v2/A5O.lean`, SHA-256 `c219cb0e0c0e8b3948fb0d04060afaaef9da705cfc06aef732376cce47c44ec6`.

This is the file as reproduced in the signed report of 25 August 2026
("A5O Formal Proof — Executive Summary and Verified Source") and described in
the paper's §12 ("Artifact availability") and cover page ("Verified source
sealed 25 August 2026"). The 25 Aug report reproduces this source as a
typeset image, not as extractable text or a committed file with a matching
hash — its bytes cannot be matched to `c219cb0e…` exactly by direct
comparison. The repository's own git history for this project contains a
`v2` commit (`0b46caa`, `48e71e63c5076a19df26a5302392176e3bd5f6eedf103bd2e077c10bca761841`)
that differs from `c219cb0e…` only in comment typography — Unicode
box-drawing dividers versus plain ASCII dashes, and one word of wording —
with zero difference in any definition, axiom, or proof.

- `v2/Check.lean`, SHA-256 `c79e4039739b15b6f9df679a495b7ae71bd10b31a5cf9105be1367690a714e5b`
- `v2/axioms.txt`, SHA-256 `8f2af5d9ceb18c15deedf4d49e4c8411f95f75dbab201dae4ce7a0af7affc43e`

Re-check with Lean 4.14.0:
```
lean -o A5O.olean A5O.lean       # expect exit 0, no output
LEAN_PATH=. lean Check.lean       # expect output identical to axioms.txt
```

## v3 — what the repository tag and the Bitcoin-anchored commit carry

`v3/A5O.lean`, SHA-256 `2fde9ccbf3ff8d851e1bbf6dcb0de6809d67cf8d2be2fbf440da8387cc13de2a`.

This is `A5O.lean` at tag `paper-sealed-2026-08-29`, commit `16142fb` (the
commit that added the companion paper to the repository, 29 Aug 2026,
anchored on Bitcoin as part of that commit's OpenTimestamps proof). v3 is a
strict extension of v2, made one day after the 25 Aug report: it adds one
section, `RevocationConsequences`, with two theorems —
`revoked_defeats_O` and `revocation_blocks_enforcement` — that make `P2`
(revocation dominance) load-bearing. In v2, `P2` was declared and stated
non-vacuously but consumed by nothing else in the file; v3 closes that gap.

Nothing else changes. The same nine axioms appear across both versions
(`C_functional`, `P2`, `ABLP.conj_speaks_for_left`/`right`,
`SPKI.spki_threshold_empowers_left`/`right`,
`Macaroons.copy_preserves_authorization`,
`Biscuit.biscuit_signature_functional`, `UCAN.ucan_revocation_dominance`),
and the same 25 audited theorems checked in v2's `Check.lean` produce
byte-identical `#print axioms` output in v3 — verified directly: the first
27 lines of v3's audit output (25 theorems; two entries wrap to a second
line) are identical to `v2/axioms.txt`. The two new theorems each depend on
`[P2]` and nothing else — confirmed before this bundle was published.

- `v3/Check.lean` — `v2/Check.lean` plus two lines:
  `#print axioms revoked_defeats_O` and
  `#print axioms revocation_blocks_enforcement`.
  SHA-256 `9d813560b6c1307063d6b53ed4e79dbf14178037ba316ddbf528213843b73645`
- `v3/axioms.txt`, SHA-256 `b97f3565d26a463a7df10ec6dddf713dac84489af4a3e69ba19fba88f8a3778b`

Re-check with Lean 4.14.0:
```
lean -o A5O.olean A5O.lean       # expect exit 0, no output
LEAN_PATH=. lean Check.lean       # expect output identical to axioms.txt
```

## v4 — a defect found in v3's axioms, and the repair

`v4/A5O.lean`, SHA-256 `0e5ebe3f5113727ae0cd41ec4399661a352fcc4fb522fcfe7ef7be3318f6b452`.

On 2026-09-07, an external review (`Consistency.lean`) found that each of
v3's nine axioms is stated over the file's own section variables, which Lean
generalizes automatically — so each axiom in fact asserted its property for
*every* predicate of the matching type, not only the one this file reasons
about. Instantiating each axiom at a deliberately pathological predicate
(e.g. `C_functional` at the constantly-true signature predicate on `Bool`)
derives `False` from that axiom alone, with no other axiom or `sorry`
involved: all nine were individually inconsistent as stated, which makes
every theorem that depended on one of them vacuously true regardless of its
proof — a defect in how the axioms were stated, not in the reasoning that
used them. The nineteen theorems that never depended on any axiom (the
necessity theorems, the completeness-direction theorems, and the pure
type-level D1/D2-and-dual facts) were never affected.

v4 converts each axiom into an explicit hypothesis parameter on the
theorem(s) that consume it (`O_unique`; `revoked_defeats_O` and
`revocation_blocks_enforcement`; `ABLP.D3_...`; `SPKI.SPKI_threshold_...`;
`Macaroons.bearer_tokens_...`; `Biscuit.biscuit_chain_...`;
`UCAN.ucan_matches_P2_shape`), applied to the one abstract predicate already
in scope rather than universally quantified over every predicate of that
type. Two theorems document the boundary this creates on `O_unique`:
`quorum_two_governors` exhibits two distinct principals both satisfying `O`
on a board-quorum instance of the sealed predicate, and
`quorum_not_CFunctional` proves that instance fails exactly the hypothesis
`O_unique` now requires. Nothing else changes: the `O` predicate and every
other pre-existing definition are byte-identical to v3.

- `v4/Check.lean`, SHA-256 `4a426b13bfa582fb301e24164f2fbfcdbafd9c9067fa876c9a560280c82ff66a`
  — `#print axioms` on all 33 theorems in the file (every `theorem`
  declaration, not a pre-selected subset).
- `v4/axioms.txt`, SHA-256 `1ecf611ce211fbaaf147666feb40c1518b7ed6bc07e8a795f914706b7a830daf`
  — all 33 report zero axiom dependency.

Re-check with Lean 4.14.0:
```
lean -o A5O.olean A5O.lean       # expect exit 0, no output, no warnings
LEAN_PATH=. lean Check.lean       # expect output identical to axioms.txt
```

The regression that found the defect, `Consistency.lean` (SHA-256
`3c2387c6b9730a81a9b5b03ed6f0e800ce9b43fe19411bb914919578149ddebb`), now
fails to compile against v4 — nine "unknown identifier" errors, because
there is no longer an axiom to instantiate. It is not included in this
public bundle; the full record, including the regression file itself and
the dated finding, is in `AgentOBO/a5o-lean`'s `corrections/` and
`repairs/2026-09-07/` directories (private repository).

v3 (`2fde9ccb…`) is not revised by this finding — it remains sealed and
Bitcoin-anchored at tag `paper-sealed-2026-08-29`. v4 supersedes it for the
reason above; it does not retract or alter it.

## OpenTimestamps

`v2/A5O.lean.ots` and `v3/A5O.lean.ots` are independent Bitcoin-anchor
proofs, stamped separately (v2 on 2026-09-05T13:04:47Z as part of an
eight-file batch also covering the audit report, provenance record, and 5
Sep verification record; v3 on 2026-09-05T13:50:41Z as a single-file stamp).
`ots verify <file>.ots` against the matching `A5O.lean` will show
`PendingAttestation` until the underlying Bitcoin transaction confirms, then
a block height once it does. v4 is not yet timestamped.

Every hash on this page was verified with `sha256sum -c` against
`SHA256SUMS` before this bundle was committed.

A signed correction to Executive Provenance Record AOB-PROV-2026-08-31-0001
§5.3, addressing the same v2/v3 distinction documented above, is at
[`CORRECTION-2026-09-06-provenance-5.3.md`](CORRECTION-2026-09-06-provenance-5.3.md),
with its OpenTimestamps proof at
[`CORRECTION-2026-09-06-provenance-5.3.md.ots`](CORRECTION-2026-09-06-provenance-5.3.md.ots).

Verified, not ratified. Ratification is reserved to the Appointed
Intelligence Institute, in formation.
