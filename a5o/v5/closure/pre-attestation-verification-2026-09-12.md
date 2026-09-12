# Pre-attestation verification round — theapertures.app

**Dated 2026-09-12.** This note documents two distinct events on the
production gate (theapertures.app) between the step 2–4 merge and the
operator attestations: the post-merge health verification, and the
pre-attestation verification round proper, run against `/operator.html`
(`apertures-app` commit `f683e50`). It is filed here so the production
ledger's first rows after `seq 29` are accounted for in the record they
belong to, not left to speak for themselves.

## Scope

- **Post-merge verification**: receipts chain `seq 2` only (§1 below)
- **Pre-attestation round**: ledger chain `seq 30–32`; receipts chain `seq 3–10`; execution log `seq 2–5`
- **Trace export**: `export_hash_sha256 20ff8dd98f35cc2f758c6b8dcaef4a2ce924b145e36d6b6319da45739930ef9d`, exported `2026-09-12T08:05:45.566Z`

## §1 — Post-merge verification (receipts seq 2)

Immediately after the step 2–4 merge (`be440d2`) deployed to production,
Apertures (Claude, the Chairman's chat session) issued one verification
request and confirmed the gate was live and correct: schema
`A5O-RCT-1.3.3`, six `checks` all true, the `request` block present with
its ULID, `receipt_id` suffixed by it, `appointment_ref` resolving to the
seq-29 grant, hash match, Ed25519 valid under the production key. This is
`receipts seq 2` (`insider+brief`, ALLOW, `07:32:15`) — the first row in
production's `receipts` chain and its execution the first in
`execution_log`, the schema migration having run on the production
database on this request, against the confirmed-empty tables, as designed.
This predates `/operator.html`'s own deployment (`f683e50`, later the same
day) and is not part of the button round below.

## §2 — Pre-attestation verification round (operator page)

Eight buttons on `/operator.html`, clicked by the operator (Fitzgerald J.
Heslop) from the operator's own browser, admin token held only in that
browser tab. The four Issue buttons were run twice, not once as scripted —
the first pass ran before the revoke had landed, so `connoisseur+auto` still
read ALLOW; the second pass, run cleanly six minutes later, produced the
intended demonstration. Both passes are real, signed, permanent rows; both
are reported here rather than only the clean pass.

| Ledger seq | Action | Grant/revocation id |
|---|---|---|
| 30 | Grant `connoisseur+auto` | `01M2AACSD72513P8218V9Q5094` |
| 31 | Revoke that grant | `01M2AACWZNH11GXH1142W5THE5` |
| 32 | Re-grant `connoisseur+auto` | `01M2AADRZVFGGQDAXDM0GN78WJ` |

| Receipt seq | request_id | Tier + action | Decision | Reason code | Note |
|---|---|---|---|---|---|
| 3 | `01M2AA0S...` | connoisseur + auto | ALLOW | `RC-OK-CONNOISSEUR-AUTOMATION` | first pass, before revoke landed |
| 4 | `01M2AA1E...` | visionary + assets | DENY | `RC-DENY-NO-ADVICE-NO-CUSTODY` | first pass |
| 5 | `01M2AA1M...` | visionary + neg | DENY | `RC-DENY-REQUIRES-RATIFICATION` | first pass |
| 6 | `01M2AA1R...` | insider + brief | ALLOW | `RC-OK-INSIDER-INFO` | first pass |
| 7 | `01M2AAD0...` | connoisseur + auto | DENY | `RC-DENY-REVOKED` | **second pass — the intended demonstration** |
| 8 | `01M2AAD2...` | visionary + assets | DENY | `RC-DENY-NO-ADVICE-NO-CUSTODY` | second pass |
| 9 | `01M2AAD5...` | visionary + neg | DENY | `RC-DENY-REQUIRES-RATIFICATION` | second pass |
| 10 | `01M2AAD7...` | insider + brief | ALLOW | `RC-OK-INSIDER-INFO` | second pass |

All three refuse paths named in the brief (`mandate`, `binding`,
`revocation`) are demonstrated, each with the `checks` object showing
exactly the one failing check, in both passes.

## Verification

Every row above — all nine receipts, all four executions, all three ledger
entries — was independently recomputed and checked, not taken on the
server's word: `entry_hash` recomputed from each row's own fields under
`A5O-CANON-SIGN-1.0`, chain linkage confirmed (`prev_entry_hash` matches the
prior row's `entry_hash`, first row of each chain traces to `sha256("")`),
and every receipt's and the trace export's Ed25519 *and* ML-DSA-87
signatures verified against the production keys published at
`/api/pubkey` (`A5O-SIGN-KEY-ED25519-PROD-2026` /
`A5O-SIGN-KEY-MLDSA87-PROD-2026`). 86/86 checks passed.

Production's `/api/revocations` read `as_of: 32` with the new grant id
present in the revoked set after this round, and `seq 29` (unchanged)
immediately before it — confirming this was the first write to the
production ledger chain since the step 1 merge.

No further test writes were made to production after the trace export;
the ledger stood at seq 32.
