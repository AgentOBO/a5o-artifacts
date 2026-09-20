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
used them.

The sealed development (v3, and v2 before it) states 31 theorems: 8
depended on one of the nine axioms (`O_unique`; `revoked_defeats_O` and
`revocation_blocks_enforcement`; `ABLP.D3_...`; `SPKI.SPKI_threshold_...`;
`Macaroons.bearer_tokens_...`; `Biscuit.biscuit_chain_...`;
`UCAN.ucan_matches_P2_shape`); the other 23 never depended on any axiom
(the necessity theorems, the completeness-direction theorems, and the pure
type-level D1/D2-and-dual facts) and were never affected.

v4 restates the 8 with explicit hypothesis parameters, applied to the one
abstract predicate already in scope rather than universally quantified
over every predicate of that type, and leaves the 23 unchanged. It also
adds two theorems that exist nowhere in the sealed development —
`quorum_two_governors` and `quorum_not_CFunctional` — documenting the
boundary `CFunctional` now names on `O_unique`: the first exhibits two
distinct principals both satisfying `O` on a board-quorum instance of the
sealed predicate, and the second proves that instance fails exactly the
hypothesis `O_unique` now requires. 31 restated/unchanged plus 2 additions
is v4's 33. Nothing else changes: the `O` predicate and every other
pre-existing definition are byte-identical to v3.

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
a block height once it does. `v4/A5O.lean.ots` was stamped separately,
2026-09-07T08:44:33Z, two days after v3's — the corrected file has its own
independent existence proof, not one inherited from v3 or the paper.
Attested at Bitcoin blocks 965908 and 965933 (two of three calendars,
independently verified against mempool.space; `finney.calendar.eternitywall.com`
remains `PendingAttestation`).

Every hash on this page was verified with `sha256sum -c` against
`SHA256SUMS` before this bundle was committed.

## Signed correction — Executive Provenance Record §5.3

(Ref: `AOB-CORR-2026-09-06-0001`.) Addresses the same v2/v3 distinction
documented above: Executive Provenance Record AOB-PROV-2026-08-31-0001
§5.3 cited tag `paper-sealed-2026-08-29` as the sealed source; that tag
resolves to v3, not v2, while the paper's §12 and cover describe v2.
Dated 2026-09-06, envelope `f94f3dab-3fec-4a18-894b-33373ef268ff`. Hash
of the signed instrument: `8d446af28d95efe6e6b122e3d6819c7a42f2739b796c91457615e30aba69faf7`
(not published here — its source text is, matching content, at hash
`ae9ed913ca7361628b004ba0e191c7c9a3b97c90542bf0bc515e9f893d44b21c`).
Attested at Bitcoin block 965717 (`bob.btc.calendar.opentimestamps.org`;
`catallaxy` and `finney` remain `PendingAttestation`).

[`CORRECTION-2026-09-06-provenance-5.3.md`](CORRECTION-2026-09-06-provenance-5.3.md),
proof at
[`CORRECTION-2026-09-06-provenance-5.3.md.ots`](CORRECTION-2026-09-06-provenance-5.3.md.ots).

## Signed correction — all nine axioms were individually inconsistent

[`corrections/2026-09-07/`](corrections/2026-09-07/) carries the executed
instrument that authorizes v4: the paper's §Axioms, §Uniqueness, and each
of the five prior-art sections described nine axioms as reasonable,
narrow, independently-justified assumptions. Each was in fact individually
inconsistent — Lean generalized it over every predicate of its declared
type rather than the one predicate this development reasons about, so
each derives `False` when instantiated at a pathological predicate of the
right type. This correction states the finding plainly (a correction, not
a softening) and proposes the exact section-by-section replacement text,
citing v4 (`0e5ebe3f…`) as the repair.

- `corrections/2026-09-07/CORRECTION-2026-09-07-axioms-inconsistent.md`
  — SHA-256 `d550aeab2d87e978232db8d6ee704e408cfc5646b3b379ea08a86a9dd40649b9`
  (the source text, unsigned)
- `corrections/2026-09-07/Correction to the paper_ all nine axioms were individually inconsistent - Signed.pdf`
  — SHA-256 `dc15cb164d8f2d41516de6b4661db8535736847a8facfd02b2dd0d126d756d6e`
  (the executed instrument)

The Evidence Summary for this envelope — the LegalZoom audit trail, which
carries the signer's email and per-event IP addresses — was removed from
this tree on 2026-09-20. It was committed here on 2026-09-07, before this
project's later, general policy of keeping that document class private
(the signed instrument is the public register; the audit trail is not).
Removed from the live surface, not from git history — that history isn't
rewritten. The address itself is part of the private, per-envelope
signing-IP record kept alongside this repository, not reproduced here.

Signed 2026-09-07T08:33:39Z, envelope `fa7e9727-b043-4764-a679-58df8d24147e`,
signer `founder@agentobo.ai`. The sealed paper `.tex`/`.pdf` is unrevised;
this correction is issued separately, per this project's standing practice.
Its OpenTimestamps proof is attested at Bitcoin blocks 965908 and 965933
(two of three calendars, independently verified against mempool.space;
`finney.calendar.eternitywall.com` remains `PendingAttestation`).

## v4/clock — three physical claims, checked as arithmetic

Three texts, each in a pre-framing and a framed version — the pre-framing
file is the arithmetic on its own; the framed version adds one section
relating that arithmetic back to `A5O.lean` v4's ledger. Both versions of
each text are signed and committed; all six compile clean under Lean
4.33.1, zero `sorry`, zero axioms on every theorem.

**`clock/ClockStandard.lean`** and **`clock/ClockStandard-partI.lean`** —
`A5O-CLK-1.0` restated as integer arithmetic in picoseconds, separating
what the January 2026 disclosure's "17.5 ns / 57.142857 MHz / 57 million
checks per core" language actually forces (the period-frequency identity,
the exact tick count, and that "57.142857" is a six-digit truncation of
400/7, not an exact value) from the physical claims it doesn't (one check
per tick, one gate per core — recorded as explicit hypotheses, not
proved). The framed version's own header labels itself as putting the
clock "as **the time axis of the proof**" — relating tick count directly
to `A5O.lean`'s abstract `Time`.

| File | SHA-256 | Envelope | OTS blocks |
|---|---|---|---|
| `ClockStandard.lean` (framed, 24 theorems) | `67208b017217596dcdb47726fa0fa490bbabab664ae50d1851aa036501fed772` | `c402256c-70aa-4cd3-baae-46e34cb247c8` | 967720 |
| `ClockStandard-partI.lean` (7 theorems) | `064d7da25bff41b432cb94f6f7f792017c75db61c77601b355a5437108e1fa14` | `21127e3c-ba26-4b28-bc14-5723513231a0` | 967720 |

**`clock/Giza.lean`** and **`clock/Giza-preframing.lean`** — the same
clock constants checked against the Great Pyramid's standard survey
figures (Petrie 1883; Lehner). Both versions' headers self-label
**"(exploratory)"** and state plainly that "reading of the results is
overlay" — the arithmetic is real (it compiles, zero axioms), but the
file itself disclaims any causal or intentional relationship between the
clock spec and the pyramid's proportions; it establishes only that a
numerical coincidence exists and states its exact size.

| File | SHA-256 | Envelope | OTS blocks |
|---|---|---|---|
| `Giza.lean` (framed, 14 theorems) | `8d65c1ad59dd3064b39effda8bed51fd8bfc4859f1c126ecb42e3eea9e82bbb6` | `38b10c0e-a43b-40cf-b73e-a05db38e1267` | 967728, 967736, 967784 |
| `Giza-preframing.lean` (8 theorems) | `9ad53612a37bbbd7d988763a37b1dcdcbd1106d5fb9eadf5e176342a242b7297` | `086cb5ec-2d83-46bd-996e-2d91add8f1e0` | 967728, 967784 |

**`clock/DataCenter.lean`** and **`clock/DataCenter-preframing.lean`** —
what `GateReadsLedger` (the gate reads the ledger every tick) requires
physically: a ledger read is a round trip, and light-speed alone bounds
how far the ledger can be from the gate inside one 17,500 ps tick. Also
self-labels **"(exploratory)"**; its framed section separately describes
the Clock Standard itself as **"a conversion table"** between geography
and latency — establishing the distance/latency budget the ledger must
fit inside, not a claim about any real deployment's actual topology.

| File | SHA-256 | Envelope | OTS blocks |
|---|---|---|---|
| `DataCenter.lean` (framed, 9 theorems) | `043f11bc92902336af52381e775de07fd7b7f06fbb0070c8b6c5d4c674893d20` | `ac8d691d-a18b-4b98-95e3-bf108e01dee6` | 967728, 967736, 967784 |
| `DataCenter-preframing.lean` (8 theorems) | `83c5ef72bc05fd5c5b7a996d0bf9414ffe7a95a5f4e48c79faf9e2655ce23dec` | `100dc094-1fc6-433f-b0f3-b4d13e7896d1` | 967728, 967736, 967784 |

All six OTS proofs verified independently, twice — walking each `.ots`
file's own append/prepend/SHA-256 operation tree (not trusting the
verifier's printed claim alone), then recomputing each claimed block's
hash and proof-of-work from a freshly-fetched raw 80-byte header, cross-
checked between mempool.space and blockstream.info. Full detail, envelope
timestamps, and the two-machine cross-verification of this record:
[`v4/clock/proof-record-2026-09-19.md`](v4/clock/proof-record-2026-09-19.md).

## v4/hops — the delegation-chain lineage, and its companion

Five files proving one claim: a multi-hop appointment chain is not a new
object — an appointed agent that appoints is, at that hop, a principal
under the *same* gate, against the *same* ledger, all the way to a root.
`Hops.lean` (one gate at any hop depth) and `HopsWitness.lean` (a
concrete two-hop satisfiability witness) import `A5O.lean` v4 and
`Closure.lean` unmodified. `Ten.lean` adds ten closures on top —
scope attenuation, root uniqueness, time-indexed acyclicity, principal
identification, receipt non-persistence, deny-path decidability,
revocation permanence, corporate-quorum uniqueness, ledger
linearizability, and a fixed-point closure — with `TenWitness.lean`
discharging its hypotheses on the same concrete model. `KillSwitchA5O.lean`
restates a kill-switch-survival result over v4's own `O`/`Appointed`/`R`/
`Revoke`. All five: zero `sorry`, 52 `#print axioms` lines, all
zero-dependency.

`a5o/v4/companion/KillSwitch.lean` is kept separate rather than a sixth
`hops/` file: a standalone formalization of the same claim (not derived
from `A5O.lean`), with two of its eight theorems depending on
`[propext, Classical.choice, Quot.sound]` — kept out of `hops/` so that
directory's zero-axiom property holds per-directory, not just per-file.

| File | SHA-256 | Envelope | OTS blocks |
|---|---|---|---|
| `hops/Hops.lean` | `ca7a950d3c9eaf6004b665a91e9c32e7ecedcab489ad2a43d21e3bc0d966f090` | `2bce620d-5dd1-4194-bfd0-25ca858a60cf` | 967682, 967703, 967720 |
| `hops/HopsWitness.lean` | `b2ce30f00de251112416215c4154b2d15de4041601285c1bcb9ada9d75ac8d37` | `3d443f2f-e7b3-4a3d-8415-e5f57c350ffe` | 967682, 967703, 967720 |
| `hops/Ten.lean` | `294d1de78a8956160e310f33ad2bc6984664d00e9a6c87e94eae3183cb73328a` | `be2f97fb-8c56-48be-b416-8900e9b00b39` | 967682, 967703, 967720 |
| `hops/TenWitness.lean` | `ab22dfcafbfd483a948988242fe651d35b1a637f6487b123ebe3ab2cdfca413d` | `95e52e67-a8b8-42b1-a2ac-4bf66438ed27` (+ duplicate `21a38dd6…`) | 967682, 967703, 967720 |
| `hops/KillSwitchA5O.lean` | `069ca673b69e6c67ed8f0d68f1d84da96f1407f0065b071c8fdf936558c3cd15` | `36801c69-3074-4840-b9bc-90ca06348164` | 967682, 967703, 967720 |
| `companion/KillSwitch.lean` (2 of 8 theorems classical) | `d55dfa11d6643a7294f6dc76e6edbbd3e0ee3b0cfdeafa1abbd47407f3ca69b6` | `3e4cd29d-2a46-4d6b-9f68-b3e0465cc46e` | 967682, 967703, 967720 |

Full signature register and the two corrections carried forward with
this lineage (`Ten.lean`'s acyclicity result is time-indexed, not a
party-level non-recurrence claim; `KillSwitchA5O.lean` carries forward
only the already-constructive results from `KillSwitch.lean`, not its
two classical theorems): [`v4/closure/hops-companion-closure-2026-09-19.md`](v4/closure/hops-companion-closure-2026-09-19.md).

## v5 — the live gate's deployment closure

`A5O.lean` and `Closure.lean` here are unmodified copies of the sealed v4
files (same hashes as above). `Deployment.lean` models `theapertures.app`'s
public surface as a `GatedSystem` and proves accountability over every
execution conditional on one hypothesis, `NoSideChannel` — a claim about
the running server that a Lean proof from the public surface alone can't
establish. `adapter/AperturesTrace_20260912.lean` closes that gap for a
specific, bounded production window: it embeds a signed trace (nine
receipts, four executions, ledger seq 30–32) and proves
`DecisionsFollowChecker`, `NoSideChannel`, and `UniqueReceiptIds` by
computation over those concrete rows, reaching a concrete instance of
`apertures_trace_accountable`. The two remaining obligations —
`CheckersSound` and `CoversActualExecutions` — are claims about the
server's own code, not the trace, and are supplied by two signed operator
attestations rather than proved.

| Item | SHA-256 | Envelope | OTS blocks |
|---|---|---|---|
| `Deployment.lean` | `e07c69ae33d1d77e3c8e657f12f8a0fb58d233e8fd5873557c6564afcfdd59da` | — | 966551, 966586 |
| `adapter/AperturesTrace_20260912.lean` | `96369a093189710eac6d6b2e3748d00f9996bb12a9045d15a4d38656de756e0b` | — | — |
| `adapter/AperturesTrace_20260912.json` (the signed trace) | `c5ba5e2cfa4be0f8e9f9a97259f3bdaf2666fe7bb85d44d03d039e9803e19ed5` | — | — |
| `closure/Operator_Attestation_1of2_CheckersSound-2.pdf` | — | `faee154a-6a7a-40d9-9937-3d10ab75f0d2` | 966664 |
| `closure/Operator_Attestation_2of2_CoversActualExecutions-2.pdf` | — | `4a3121ab-db3f-4dcf-a760-980b11acbb56` | 966664 |

Both attestations are scoped to `apertures-app` commit `f683e50` and
ledger sequence 32; a superseding attestation is required beyond that
point. Full account, including the button-by-button verification round
the trace itself records: [`v5/README.md`](v5/README.md) and
[`v5/closure/pre-attestation-verification-2026-09-12.md`](v5/closure/pre-attestation-verification-2026-09-12.md).

## specimens/2026-09-20 — USPTO SOU specimen captures, date-anchored

Eight signed captures, each a Statement of Use specimen for a
trademark filing — the artifact of record is the capture's existence
at a provable date, not a mathematical claim. Evidence Summaries
(signer email, per-event IP addresses) are not published here; they
and their own OTS proofs are in the private `a5o-lean` repository
alongside this record's other Evidence Summaries.

**Governance Operator / AgentOBO.ai marks:**

| Title | SHA-256 | Envelope | OTS |
|---|---|---|---|
| A⁵O Governance Operator - Lean 4 \| Agent OBO USPTO - SOU - Specimen | `b55fefe42fc5160281958acb63ebace54b22f3aec6375fd78fa57d9f19036e22` | `8c33307a-79bf-47d9-8c5a-8f4e7c8a4441` | pending — checked at 2026-09-20T08:31:33Z |
| AgentOBO.ai – Appointed AI That Acts On behalf of You. USPTO - SOU - Specimen | `aa788672b1e036d0f7b2a3d45e4c55a2e9be50840d7c70a945ba3a2313c0efa0` | `7b2388d9-f2a5-46c3-99fd-e18c5ce04713` | pending — checked at 2026-09-20T08:31:33Z |
| A⁵O Governance Operator - Lean 4 \| Agent OBO - USPTO -Specimen - SOU | `ce9baafa46ca4fea8819a465788ec39008ade200f8bef08155a638d27f1dafa3` | `ef96322c-27ea-4836-a1c6-2241c9074fbf` | pending — checked at 2026-09-20T08:31:33Z |
| AgentOBO.ai – Appointed AI That Acts On behalf of You. - USPTO - SOU - Specimen | `73882697c89326210804dc3d8859c6e2c0e40f76d093df2d91e9f9f996e065d2` | `d7098983-f882-4f78-b130-f4f612b4f546` | pending — checked at 2026-09-20T08:31:33Z |

**ONEBEHALFOF™ mark — Receipt Verifier captures:** two print-to-PDF
captures of the live verifier page and two image screenshots; see
[`onebehalfof-receipt-verifier-record.md`](onebehalfof-receipt-verifier-record.md)
for the full record, a correction to the original intake claim about
one capture's content, and a note on signing-timestamp precision.

| Title | SHA-256 | Envelope | OTS |
|---|---|---|---|
| ONEBEHALFOF Receipt Verifier — A⁵O Public Evidence Surface - USPTO - Specimen - SOU (9pp print-to-PDF) | `2b88aa57bc0ed48a347016d1cb8bc35ac3962c36bf178cb7fc5928bc29bbfa22` | `9882cb4a-7743-4871-98bb-278e8725b96e` | pending |
| ONEBEHALFOF Receipt Verifier — A⁵O Public Evidence Surface - USPTO - SOU - Specimen (1pp print-to-PDF) | `796be8b1a8a424b2f45d8437f6edfcd9577ab26936c2f175224ada01faaaeba2` | `27e39a3d-c6c3-4879-bb12-76ea57483e6f` | pending |
| Screenshot 2026-09-20 at 12.32.07 PM (image capture) | `7cdea8debb4a69a1883ef6121b32da3994ad70ba55f33fad233c733def3b1068` | `c73e720d-6ee2-4d2c-a78e-94f175c4793b` | pending |
| Screenshot 2026-09-20 at 12.37.02 PM (image capture) | `c448b57b3791c4b195e075d6b22333d70592901bd104dd292f6b43e49f7ec393` | `aaa4e39b-8161-4e27-b0a1-16f4595a6986` | pending |

All eight signed 2026-09-20, from the same signing IP recorded on each
envelope's Evidence Summary (private repo, not reproduced here).

Verified, not ratified. Ratification is reserved to the Appointed
Intelligence Institute, in formation.
