# ONEBEHALFOF Receipt Verifier — specimen record, 2026-09-20

Four signed captures of the live public verifier at
`https://verify.theapertures.app/`, filed as USPTO Statement of Use
specimens for ONEBEHALFOF™ alongside the same day's Governance Operator
and AgentOBO.ai captures in this directory. Evidence Summaries (signer
email, per-event IP addresses) are not published here; they and their
own OTS proofs are in the private `a5o-lean` repository.

## Files

| Title | Pages | SHA-256 | Envelope | Completed (UTC, audit trail) |
|---|---|---|---|---|
| ONEBEHALFOF Receipt Verifier — A⁵O Public Evidence Surface - USPTO - Specimen - SOU (print-to-PDF) | 9 | `2b88aa57bc0ed48a347016d1cb8bc35ac3962c36bf178cb7fc5928bc29bbfa22` | `9882cb4a-7743-4871-98bb-278e8725b96e` | 09:29:48.890686 |
| ONEBEHALFOF Receipt Verifier — A⁵O Public Evidence Surface - USPTO - SOU - Specimen (print-to-PDF) | 1 | `796be8b1a8a424b2f45d8437f6edfcd9577ab26936c2f175224ada01faaaeba2` | `27e39a3d-c6c3-4879-bb12-76ea57483e6f` | 09:30:13.507463 |
| Screenshot 2026-09-20 at 12.32.07 PM (image capture) | 1 | `7cdea8debb4a69a1883ef6121b32da3994ad70ba55f33fad233c733def3b1068` | `c73e720d-6ee2-4d2c-a78e-94f175c4793b` | 09:36:09.835574 |
| Screenshot 2026-09-20 at 12.37.02 PM (image capture) | 1 | `c448b57b3791c4b195e075d6b22333d70592901bd104dd292f6b43e49f7ec393` | `aaa4e39b-8161-4e27-b0a1-16f4595a6986` | 09:40:44.800368 |

All four signed 2026-09-20, from the same signing IP recorded on each
envelope's Evidence Summary (private repo, not reproduced here).

## Correction to the intake claim

The delivery message accompanying these files characterized the
9-page capture (envelope `9882cb4a…`) as showing "no verdict panel (no
receipt run)," distinguishing it from the 1-page capture (envelope
`27e39a3d…`), which was said to show "ONEBEHALFOF™ verified." Direct
text extraction from the 9-page file's own pages (confirmed against
its own footer stamp) shows this is incorrect: it carries the identical
verdict panel — "PUBLIC VERDICT / ONEBEHALFOF™ verified," decision
`ALLOW` — and the identical receipt detail block as the 1-page capture,
down to the same receipt hash and keyset digest. Both captures show the
verifier page's default-loaded example, receipt
`RCT-A5O-PUBLIC-DEMO-2026-07-10-0001`, not the result of an interactive
check run at capture time. The two files differ only in print
pagination (9 pages vs. 1), not in page content. The original claim's
inference that a receipt "was run" for the 1-page capture is withdrawn;
what both captures show is the page's default state.

## Timing note

Each signed PDF carries a visible "eSigned on ... GMT" banner baked in
at signing time. Across every envelope read this session, that banner
time runs measurably earlier than the same envelope's own audit-trail
`Signed` event — by roughly 3 to 7 seconds, consistent in direction
each time. The banner appears to record ceremony initiation; the audit
trail records server-side completion. The `Completed` timestamp in the
table above is the audit-trail figure and is the time of record for
this filing; the on-document banner time is not read as more precise
than that.

## OpenTimestamps

Four proofs — the four signed captures above — stamped 2026-09-20,
**upgraded** 2026-09-20: `BitcoinBlockHeaderAttestation` at blocks
967821, 967825, and 967860 for all four files. Each `.ots` re-verified
via `ots info` against its own file's SHA-256 both before and after
upgrade. All three block/merkle-root pairs cross-checked directly
against mempool.space and blockstream.info independently, both
agreeing on height and merkle root in every case.

---

*Filed by Claude Code, 20 September 2026.*
