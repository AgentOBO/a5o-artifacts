# CORRECTION — EXECUTIVE PROVENANCE RECORD AOB-PROV-2026-08-31-0001, §5.3

**Ref:** AOB-CORR-2026-09-06-0001
**Issued by:** Fitzgerald J. Heslop, Founder & CEO, Agent OBO Inc.
**Subject:** Identification of the Lean source cited by the Executive Provenance Record and by the paper *A Machine-Checked Necessity Result for Accountable Delegated Authority*
**Practice:** The provenance record is sealed and unrevised. This correction is issued separately, per standing practice.

---

## §1 — THE DISCREPANCY

The Executive Provenance Record §5.3 cites repository tag `paper-sealed-2026-08-29` as the sealed source. That tag resolves to **v3** of `A5O.lean`, SHA-256 `2fde9ccbf3ff8d851e1bbf6dcb0de6809d67cf8d2be2fbf440da8387cc13de2a`.

The paper's cover ("Verified source sealed 25 August 2026") and §12 ("reproduced as an appendix to the report of 25 August 2026") describe **v2** of `A5O.lean`, SHA-256 `c219cb0e0c0e8b3948fb0d04060afaaef9da705cfc06aef732376cce47c44ec6`.

The two pointers name different files.

## §2 — THE RELATIONSHIP BETWEEN THE FILES

v2 (`c219cb0e…`, 696 lines) and repository commit `0b46caa` (`48e71e63c5076a19df26a5302392176e3bd5f6eedf103bd2e077c10bca761841`) are identical in all non-comment content; they differ only in comment typography (Unicode versus ASCII section rules) and the wording of one comment.

v3 (`2fde9ccb…`, 736 lines) is v2 with one section appended, `RevocationConsequences`, containing two theorems — `revoked_defeats_O` and `revocation_blocks_enforcement` — each depending on axiom `P2` alone. v3 declares no new axiom and alters no existing declaration.

Under `#print axioms`, the twenty-five declarations audited for the paper report identical dependencies in v2 and v3. Every claim the paper makes holds in both files.

## §3 — DATES

| Event | UTC |
|---|---|
| Report of 25 Aug 2026 reproducing v2 as an appendix (`A5O_Report.pdf`, SHA-256 `85614f16942a968b93d2b60a02e007081e6c8d2924be25eb0c9cb23d05deea66`) created | 2026-08-25 09:48:06 |
| Commit `0b46caa` — "Replace scaffold with the signed A5O.lean source (v2, verified)" | 2026-08-26 11:16:44 |
| Commit `7c1ca07` — "v3: make P2 load-bearing (zero new axioms)" | 2026-08-26 12:43:09 |
| Paper signed (envelope `8017d707-315c-4fe4-94b7-06956dcb2afe`) | 2026-08-28 |
| Commit `16142fb4e6322d364c5e6cb501c4301fe4718955` — "Add companion paper"; tag `paper-sealed-2026-08-29` created on this commit | 2026-08-29 09:24:52 |
| Provenance record signed (envelope `7ebae903-7b53-45e2-ae09-53fca8900775`) | 2026-08-31 11:18:06 |

## §4 — ANCHORS

| File | Register |
|---|---|
| v3 `2fde9ccb…` | Committed to the tree at `16142fb`, attested via `paper-commit-hash.txt` at Bitcoin blocks 964554 and 964600 (29 Aug 2026); separately stamped 5 Sep 2026, attested at blocks 965627, 965642, 965689 |
| v2 `c219cb0e…` | Stamped 5 Sep 2026, attested at blocks 965627, 965642, 965689 |

Both files, their audit scripts, audit outputs, and proofs are published at `https://artifacts.agentobo.ai/a5o/` and at `github.com/AgentOBO/a5o-artifacts`.

## §5 — STATED LIMIT

The report of 25 August 2026 reproduces its appendix as page images. The identification of `c219cb0e…` with that appendix rests on content match — header, revision notes, declarations, axiom count, and trailer — not on a byte-level comparison, which the rasterized format does not permit.

## §6 — EFFECT

No sealed instrument is amended. The Executive Provenance Record §5.3 is to be read with this correction: the tag it cites carries v3; the paper describes v2; the mathematics of the paper is fully contained in both, and v3 extends v2 without contradiction.

---

Fitzgerald J. Heslop
Founder & CEO, Agent OBO Inc. · Delaware File No. 10272951 · UEI GGLZDKW3CMQ7 · CAGE 17EB1

Date: ______________

*Drafted by Claude Code under AOB-CC-2026-09-05-0002; reviewed and revised in-session under the principal's instruction, 6 September 2026. Carries no authority until signed by the principal.*
