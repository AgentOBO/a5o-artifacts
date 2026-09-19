# ClockStandard proof record — 2026-09-19

No prior file under this name exists in `a5o-lean` or `a5o-artifacts`; this
is the first entry, filed under Brief 5 (`AOB-CC-2026-09-19-0002`), Task D.

## Files, as committed

| File | SHA-256 | Signed envelope |
|---|---|---|
| `ClockStandard.lean` (full, Part I+II, 24 theorems) | `67208b017217596dcdb47726fa0fa490bbabab664ae50d1851aa036501fed772` | `c402256c-70aa-4cd3-baae-46e34cb247c8`, signed 2026-09-19 14:37:48 UTC |
| `ClockStandard-partI.lean` (Part I only, 7 theorems) | `064d7da25bff41b432cb94f6f7f792017c75db61c77601b355a5437108e1fa14` | `21127e3c-ba26-4b28-bc14-5723513231a0`, signed 2026-09-19 10:30:06 UTC |

Both compile clean under Lean 4.33.1, zero `sorry`, all 24 (resp. 7)
`#print axioms` lines zero-dependency, confirmed by `leanchecker --fresh`.
Both signed PDFs content-verified against these exact bytes (whitespace-
normalized, envelope-footer stripped; two single-space insertions inside
`═══` divider rules in the full file are a PDF line-wrap artifact, not a
content difference).

## Commit hashes

| Repo | Commit | Contents |
|---|---|---|
| `a5o-lean` (private) | `7aa56855bb62140d2babc57028f6ce8435348ccd` | Both `.lean` files, `Check.lean`, `axioms.txt` |
| `a5o-lean` (private) | `2454211748ca38927757ba53e39ba64d54c7fd6d` | Both Evidence Summaries |
| `a5o-artifacts` (public) | `3080bf3579776b0fed49f83ea4adf2b6ba9d94e9` | Source, `Check.lean`, `axioms.txt`, both signed PDFs, `SHA256SUMS` |
| `a5o-artifacts` (public) | `95bad5d44575f816ac2a2661ed7994250753d9ed` | Five `.ots` proofs, `clock-commit-hash.txt`, `SHA256SUMS` |

Evidence Summaries (signer email, per-event IP addresses) are not in
`a5o-artifacts` — that repo is public. They are in `a5o-lean` only,
consistent with Amendment A1 item 2 (Brief 4).

## OpenTimestamps

Five proofs — `ClockStandard.lean`, `ClockStandard-partI.lean`, both signed
PDFs, `clock-commit-hash.txt` — stamped 2026-09-19, **pending** Bitcoin
confirmation as of 2026-09-19T15:10:28Z. Upgrade and block heights to
follow once the calendars have had at least one block.

## IP chain

Three envelopes confirmed on the record: `f26f357a…` (7 Dec 2025),
`21127e3c…` and `c402256c…` (today, both above) — all signed from the
same signing IP recorded on their Evidence Summaries (private repo; not
reproduced here). A fourth link, claimed against a 25 Aug 2026 `A5O.lean`
signature, is withdrawn: the note that made the claim carried no envelope
ID, the two candidate instruments (`8017d707…`, 28 Aug; `e711736d…`, 29
Aug) don't carry that date directly (the 25 Aug date is the *seal* date
printed on `8017d707…`'s cover page, not its signing date — the likely
source of the conflation), and neither instrument's Evidence Summary is
in hand on either machine to check the signing IP. Restorable only if one
of those two summaries surfaces and shows the matching signing IP;
until then the chain is three envelopes, not four.

---

*Filed by Claude Code under Ref AOB-CC-2026-09-19-0002, 19 September 2026.*
