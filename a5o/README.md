# A⁵O — Lean 4 source, two versions

This directory publishes the Lean 4 formalization behind *A Machine-Checked
Necessity Result for Accountable Delegated Authority* (28 Aug 2026) in two
distinct, separately verified forms. Neither is "the" verified source on its
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

## OpenTimestamps

`v2/A5O.lean.ots` and `v3/A5O.lean.ots` are independent Bitcoin-anchor
proofs, stamped separately (v2 on 2026-09-05T13:04:47Z as part of an
eight-file batch also covering the audit report, provenance record, and 5
Sep verification record; v3 on 2026-09-05T13:50:41Z as a single-file stamp).
`ots verify <file>.ots` against the matching `A5O.lean` will show
`PendingAttestation` until the underlying Bitcoin transaction confirms, then
a block height once it does.

Every hash on this page was verified with `sha256sum -c` against
`SHA256SUMS` before this bundle was committed.

Verified, not ratified. Ratification is reserved to the Appointed
Intelligence Institute, in formation.
