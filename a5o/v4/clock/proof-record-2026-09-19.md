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

## Giza and DataCenter, both versions each (Brief 6, `AOB-CC-2026-09-19-0003`)

| File | SHA-256 | Signed envelope |
|---|---|---|
| `giza/Giza.lean` (framed, §1–6, 14 theorems) | `8d65c1ad59dd3064b39effda8bed51fd8bfc4859f1c126ecb42e3eea9e82bbb6` | `38b10c0e-a43b-40cf-b73e-a05db38e1267`, signed 2026-09-19 16:56:17 UTC |
| `giza/Giza-preframing.lean` (§1–5, 8 theorems) | `9ad53612a37bbbd7d988763a37b1dcdcbd1106d5fb9eadf5e176342a242b7297` | `086cb5ec-2d83-46bd-996e-2d91add8f1e0`, signed 2026-09-19 15:45:49 UTC |
| `datacenter/DataCenter.lean` (framed, §1–5 with F4, 9 theorems) | `043f11bc92902336af52381e775de07fd7b7f06fbb0070c8b6c5d4c674893d20` | `ac8d691d-a18b-4b98-95e3-bf108e01dee6`, signed 2026-09-19 16:56:49 UTC |
| `datacenter/DataCenter-preframing.lean` (§1–4, 8 theorems) | `83c5ef72bc05fd5c5b7a996d0bf9414ffe7a95a5f4e48c79faf9e2655ce23dec` | `100dc094-1fc6-433f-b0f3-b4d13e7896d1`, signed 2026-09-19 17:04:16 UTC |

All four compile clean under Lean 4.33.1, zero `sorry`, every `#print axioms`
line zero-dependency, confirmed by `leanchecker --fresh` (the two
`-preframing` files needed the guillemet-escaped module name — hyphens
aren't valid in a bare Lean identifier). The same check was run
retroactively against `ClockStandard-partI.lean` above, which Brief 5
compiled but never separately ran through `leanchecker`; it also passes.
All four signed PDFs content-verified against these exact bytes.

**Standing rule (Decision 3, Brief 6):** every signed instrument gets its
source committed — a signed text with no committed bytes is a loose
instrument. This governs Giza and DataCenter here and is not a
ClockStandard-specific exception.

### Commit hashes

| Repo | Commit | Contents |
|---|---|---|
| `a5o-lean` (private) | `37bb8b2f7d3587b6a53ffdba503fd8dcd2ce7e3a` | Four `.lean` files, four `Check.lean`/`axioms.txt` pairs, four signed PDFs, four Evidence Summaries |
| `a5o-artifacts` (public) | `e4c2923df421f52b4d1be975eb79669324efac57` | Source, `Check.lean`/`axioms.txt` pairs, four signed PDFs, `SHA256SUMS` |
| `a5o-artifacts` (public) | `c6e729a95ca7765554714395bca84db28130b47a` | Nine `.ots` proofs, `giza-datacenter-commit-hash.txt`, `SHA256SUMS` |

No Evidence Summaries in `a5o-artifacts` — `a5o-lean` only, same as
ClockStandard.

### OpenTimestamps

Nine proofs — four `.lean` files, four signed PDFs,
`giza-datacenter-commit-hash.txt` — stamped 2026-09-19, **pending** as of
2026-09-19T17:24:38Z.

Checked in the same pass: ClockStandard's five proofs above show a real
transaction on one calendar path, confirmed on-chain at 5 confirmations
at check time, but not yet reported complete by that calendar's own
upgrade check, and the other two calendar paths show no block yet — not
upgraded this pass.

## Envelope chain

Seven envelopes now stand on the record: `f26f357a…` (7 Dec 2025),
`21127e3c…`, `c402256c…`, `086cb5ec…`, `38b10c0e…`, `100dc094…`,
`ac8d691d…` (19 Sep 2026, all six above). All seven signed by the same
recipient, from the same signing IP on each occasion — the IP itself and
the recipient's email are recorded on the Evidence Summaries in the
private `a5o-lean` repo only, not reproduced here. An eighth candidate
link, claimed against a 25 Aug 2026 `A5O.lean` signature, remains
withdrawn: the two candidate instruments (`8017d707…`, 28 Aug;
`e711736d…`, 29 Aug) don't carry that date as their signing date (25 Aug
is the *seal* date printed on `8017d707…`'s cover page), and neither
instrument's Evidence Summary is in hand to check. Restorable only if one
surfaces and shows the matching signing IP; until then the chain is
seven envelopes, not eight.

---

*Filed by Claude Code under Ref AOB-CC-2026-09-19-0002 and -0003, 19 September 2026.*
