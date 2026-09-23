# A⁵O — v6: synthetic necessity and the bridge to v5

`SyntheticNecessity.lean` and `Bridge.lean`, 22 September 2026. A new
closure above both the v4 proof line and v5's deployment line, not a
member of either: `SyntheticNecessity.lean` proves a third-party
accountability predicate that mentions none of v4's six conjuncts, and
`Bridge.lean` identifies v5's deployed checkers with it. Filed together
because Bridge imports SyntheticNecessity directly.

## Files

| File | SHA-256 | Role |
|---|---|---|
| `A5O.lean` | `0e5ebe3f5113727ae0cd41ec4399661a352fcc4fb522fcfe7ef7be3318f6b452` | v4, byte-identical copy — anchored at [`v4/A5O.lean.ots`](../v4/A5O.lean.ots) |
| `Closure.lean` | `af6b3233bdeee80b8312a9138111c597d37f17b792a749d53844314e3a79a933` | v4, byte-identical copy — anchored at [`v4/closure/Closure.lean.ots`](../v4/closure/Closure.lean.ots) |
| `Deployment.lean` | `e07c69ae33d1d77e3c8e657f12f8a0fb58d233e8fd5873557c6564afcfdd59da` | v5, byte-identical copy — anchored at [`v5/Deployment.lean.ots`](../v5/Deployment.lean.ots) |
| `SyntheticNecessity.lean` | `6263ac8bf0c49aac2011595bd2d47f070b4b61e002e8fb2a19e00a993fcb06f1` | New. 13 theorems, zero axioms. |
| `Bridge.lean` | `1ca1e304a78a326105c560973e173533c9615608ea18a965f51aa3b2a3fe6321` | New. 8 theorems, zero axioms. |
| `Check.lean` | see `MANIFEST.sha256` | `#print axioms` for all 21 new declarations. |
| `Check.out.txt` | see `MANIFEST.sha256` | Output of `Check.lean` as run 2026-09-22. |
| `MANIFEST.sha256` | — | SHA-256 of the seven files above. |

The three imported files are unmodified copies, placed here so the
directory compiles standalone; each is already anchored under its own
line of record (linked above) and is not re-stamped here. `README.md`
sits outside the manifest and is stamped as its own proof, per standing
practice.

## Declaration count

**63 imported (33 + 16 + 14, all byte-identical to their lines of
record) + 21 new (13 + 8) = 84 declarations in the directory.** The 21
new declarations are what v6 adds; all 21 report zero axiom dependency,
confirmed by `Check.lean` against `Check.out.txt` and independently by
`leanchecker --fresh` on both new modules.

## What SyntheticNecessity.lean proves

Closes the remainder of an adversarial finding (Finding A, review dated
2026-09-22): v4's `achievesADA` contains `O` by definition, so a prior
"reduction" theorem built on it was analytic, not a genuine result — and
Closure.lean's own `Accountable` also contains `O`, so it isn't the
independent predicate the finding calls for either.

`SyntheticNecessity.lean` instead defines accountability as a
**third-party observable** — what an outside verifier can compute from
public inputs alone (a resolver, a grant ledger, a principal registry, a
withdrawal set), naming none of v4's six conjuncts (C, I, M, S, R,
Appointed) — and proves `synthetic_necessity`: that this independent
predicate entails v4's `O` at a derived instance. The six conjuncts fall
out as consequences of the observable, not as stipulations.

**One definitional commitment**, stated so it can be disputed: *"P
authorized this act" means P's grant was made before the act and not
withdrawn as of the act. Ratification after the fact is not
authorization.* Nothing else in the third-party predicate is a reading
of any conjunct.

Six countermodels (`cm_C` through `cm_App`, plus `cm_M`, `cm_S`, `cm_R`)
show each of the six conjuncts is separately load-bearing — dropping any
one breaks third-party accountability while the other five still hold.
`C_and_Appointed_separate` additionally shows public-binding (`C`) and
pre-execution appointment (`Appointed`) can diverge in both directions.

## What Bridge.lean proves

v5's `EvidenceSpec` leaves its six meanings abstract and says so in its
own text — a caller could supply overly weak predicates. `specOf`
removes that freedom: it fixes the spec to the six derived third-party
readings from `SyntheticNecessity.lean`, so `CheckersSound (specOf obs)
v` means soundness against what an outside observer can compute, not
against whatever a caller chose.

**Second definitional commitment**: the receipt's `mandate` boolean is
identified with `dM` — a sound mandate checker returns `true` only if a
public ledger grant for that agent names that act (`mandate_means_named`);
`scope_means_bounded` is the separate, distinct fact for the bound. From
these, `allow_requires_named_act`: an ALLOW decision entails a grant
naming the act, and `unnamed_act_denied` is the same fact in v5's own
denial form.

**Round trip.** `Coherent obs` is one named property of the deployed
resolver — the public binding resolves to the appointing entry
(`appointment_ref` = the grant a decision was actually made against).
Under it, `coherent_equiv` shows Closure's `Accountable` over the
derived six readings and the independent `ThirdPartyAccountable` are
equivalent. `trace_third_party_accountable` then runs the full chain —
coherent resolver, sound checkers, decisions following the checker, no
side channel — to the independent predicate. `Coherent` is the same
object-kind as `NoSideChannel`: a deployment property, attested over a
named trace, not proved.

## Controls

Two controls were run against these exact bytes, unfiltered, after an
earlier round of self-reported figures was found wrong and corrected in
session (a namespace-broken control file that never reached its own
`#print axioms` lines, misread as "no taint," and a truncated grep that
undercounted). The corrected figures, independently reproduced twice:

| Control | Patch | Hard errors | Notes |
|---|---|---|---|
| 1 (consistent) | `def Coherent (obs : Obs) : Prop := True`, or all three `(hco : Coherent obs)` binders changed to `(hco : True)` together | 2 | 3 further theorems (`O_implies_authorized`, `coherent_equiv`, `trace_third_party_accountable`) elaborate but become `sorryAx`-tainted |
| 1 (single-site) | only `O_implies_authorized`'s binder changed, callers left referencing `Coherent obs` | 3 | two inside `O_implies_authorized`, one at `coherent_equiv`'s now-mismatched call site; same 3 theorems `sorryAx`-tainted |
| 2 | `M := fun _ _ => True` in `specOf` | 4, at `mandate_means_named`, `allow_requires_named_act`, `unnamed_act_denied`, `trace_accountable_observable` | `trace_third_party_accountable` additionally `sorryAx`-tainted downstream |

Both controls confirm the same thing two ways: `Coherent` is
load-bearing for the round trip, and the `M` obligation is load-bearing
for the mandate theorems. Neither conclusion changed across any of the
figure corrections — only the error counts did.

## Signed instruments

Both files were signed before this commit. Evidence Summaries (signer
email, per-event IP addresses) are not published here; they and their
own OTS proofs are in the private `a5o-lean` repository.

| Title | SHA-256 | Envelope | Signed (UTC) |
|---|---|---|---|
| Syntheticnecessity · LEAN | `4edd72ac8265b880b715bd65908783b3b15101dde98d6e96567b074ea83817bd` | `6aa2d8b9-39c0-412d-b1df-728876c89e0a` | 2026-09-22 11:33:06 |
| Bridge · LEAN | `dc7a8d0fe7df78010ab4ef5c9aaff76ba7fe3c14dc7eb439ffc55e6aec4f2306` | `5ae00e30-b9d5-4574-a4e3-241f72fc7b83` | 2026-09-22 11:39:14 |

The signed PDF text was checked against the delivered `.lean` bytes by
content correspondence (the PDF renders without indentation, so match is
by content, not by byte-diff); the bytes of record are the `.lean` files
in this directory.

## Anchoring

`SyntheticNecessity.lean`, `Bridge.lean`, `MANIFEST.sha256`, this file's
own bytes at commit `ff3b0aa`, and the two signed PDFs — six proofs,
confirmed 2026-09-22 at Bitcoin blocks 968150, 968184, and 968193; all
three calendars (bob, finney, catallaxy) resolved on all six. Block
heights and merkle roots cross-checked independently against
mempool.space and blockstream.info, both agreeing in every case:

| Block | UTC | Merkle root |
|---|---|---|
| 968150 | 2026-09-22T14:12:46Z | `9b7c2dc8ad9dc5e44c343d8e87a0a930a1fc9710cd14f912a76edd7768689783` |
| 968184 | 2026-09-22T21:07:08Z | `999d9f033efb32ff21f6454c42a0ee70c16b4c22d0bcdb5fc849a71264344edb` |
| 968193 | 2026-09-22T21:51:59Z | `509e4f6d9c95a097c5cc60beefafa9748f711b7b096343784c0eac09f227d9b8` |

The two Evidence Summaries in the private `a5o-lean` repository were
stamped separately (fix-forward, commit `4d6b0f3` there) and remain
pending as of this sweep.

This edit is itself a new committed state; its own `.ots` (this file's
current bytes) is stamped fresh and starts pending.

Verified, not ratified. Ratification is reserved to the Appointed
Intelligence Institute, in formation.
