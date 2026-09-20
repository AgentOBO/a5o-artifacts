# Hops/Ten closure — signature register, 2026-09-19

Closes the signature layer for `a5o/v4/hops/` (five files: `Hops.lean`,
`HopsWitness.lean`, `Ten.lean`, `TenWitness.lean`, `KillSwitchA5O.lean`)
and `a5o/v4/companion/` (`KillSwitch.lean`). All six compile clean against
`A5O.lean` v4 (SHA-256 `0e5ebe3f…5b452`) and `Closure.lean`
(SHA-256 `af6b3233…a933`), both imported unmodified; zero `sorry`
anywhere. Acceptance test for each directory is
`LEAN_PATH=. lean Check.lean | diff - axioms.txt`, confirmed to pass for
both `hops/` (52 lines, all zero-dependency) and `companion/` (8 lines,
6 zero-dependency, 2 classical).

## Source hashes

| File | SHA-256 |
|---|---|
| `Hops.lean` | `ca7a950d3c9eaf6004b665a91e9c32e7ecedcab489ad2a43d21e3bc0d966f090` |
| `HopsWitness.lean` | `b2ce30f00de251112416215c4154b2d15de4041601285c1bcb9ada9d75ac8d37` |
| `Ten.lean` | `294d1de78a8956160e310f33ad2bc6984664d00e9a6c87e94eae3183cb73328a` |
| `TenWitness.lean` | `ab22dfcafbfd483a948988242fe651d35b1a637f6487b123ebe3ab2cdfca413d` |
| `KillSwitchA5O.lean` | `069ca673b69e6c67ed8f0d68f1d84da96f1407f0065b071c8fdf936558c3cd15` |
| `KillSwitch.lean` | `d55dfa11d6643a7294f6dc76e6edbbd3e0ee3b0cfdeafa1abbd47407f3ca69b6` |

## Signature register

Seven signed envelopes, all recipient Fitzgerald J. Heslop
(`founder@agentobo.ai`), every `Signed` audit-trail action from the same
signing IP recorded on each envelope's Evidence Summary (private repo,
not reproduced here), in signing order:

| Envelope | Envelope name | Content | Signed (UTC) | Signed-PDF SHA-256 |
|---|---|---|---|---|
| `95e52e67-a8b8-42b1-a2ac-4bf66438ed27` | Tenwitness · LEAN | `TenWitness.lean` | 06:10:57 | `5f760df71c583b2aeda1bd64f18a3fb5712f9597b475644aef1991312f9dc311` |
| `36801c69-3074-4840-b9bc-90ca06348164` | A5O.KillSwitchA5O | `KillSwitchA5O.lean` | 06:14:43 | `9b650e84bb659dd6a09a1a7877d29ac59b966cf75382453e37fae0a12cccf670` |
| `3e4cd29d-2a46-4d6b-9f68-b3e0465cc46e` | A5O.KillSwitch | `KillSwitch.lean` | 06:23:04 | `09e0cba467b4de16c6285cf3a8cfc80f553ca21dd23b47ee4095a022fb906f7e` |
| `21a38dd6-0b98-4980-9f6d-7ab7438f8a1c` | Ten HopsWitness | `TenWitness.lean` (duplicate; see note) | 06:28:24 | `392a5a2e1e1bb5730f8c1516b68988c4852ef06d15cb13b6676bd51c1b65331b` |
| `2bce620d-5dd1-4194-bfd0-25ca858a60cf` | Hops · LEAN | `Hops.lean` | 06:32:34 | `6b498ed1e0bac51878a46a9fe602a3e76bba3a32d664e716b30e61559ba0ee56` |
| `3d443f2f-e7b3-4a3d-8415-e5f57c350ffe` | Hopswitness · LEAN | `HopsWitness.lean` | 06:36:35 | `85add7c040837658c0f79d1fc2a473faf7e56f9377604704ecd31b1de0089a3a` |
| `be2f97fb-8c56-48be-b416-8900e9b00b39` | Ten · LEAN | `Ten.lean` | 06:49:39 | `512a67ada374f91c4bb2ca6714a50e07b89fa2f8f9bb58ea544aa081e5557ad3` |

**Naming note.** The envelope named "Ten HopsWitness" (`21a38dd6…`)
carries `TenWitness.lean`'s text, not `Ten.lean`'s — confirmed by
whitespace-normalized full-text comparison, byte-identical to envelope
`95e52e67…`. `TenWitness.lean` therefore carries two valid signatures;
`Ten.lean`'s own signature is `be2f97fb…`, obtained separately.

Each signed PDF's content was verified whitespace-normalized-identical
to the corresponding source file above (per-page "Envelope ID" footer
stamps excluded from the comparison); each source hash above was also
independently reproduced by direct SHA-256 of the file on disk.

**OpenTimestamps (2026-09-20).** All thirteen proofs — the five source
files, `companion/KillSwitch.lean`, and the seven signed PDFs above —
upgraded to Bitcoin-confirmed, blocks 967682, 967703, and 967720; each
verified via `ots info` against its own source hash before commit.

**Correction (2026-09-20).** The signature register above originally
stated the seven envelopes' common signing IP in clear text. Edited to
refer to it by reference (each envelope's private Evidence Summary)
rather than reproduce it — the email above is unaffected, published
contact rather than audit-trail data, per standing practice. This is an
edit, not a scrub: the original text remains in this repository's git
history, which is not rewritten.

Signing-ceremony Evidence Summaries (which carry the signer's email and
per-event IP addresses) are held off this public repository; they are an
operator-internal record, not part of the mathematical or signature
spec. The register above — envelope IDs, content, timestamps, signed-PDF
hashes — is the public record, on the same standard as the 5 September
verification record.

## Two corrections carried forward as record

**1. `Ten.lean` §3 (acyclicity).** `no_link_is_own_ancestor` proves that
a specific trace-link instance, indexed by `(Party, Action, Time)`, is
never its own ancestor — i.e. the trace is acyclic *in time*. It does
not entail, and was not intended by a prior overstated framing to claim,
that a given party can never recur elsewhere in the ledger or that a
party can never be appointed for some unrelated act. Only the
time-indexed acyclicity of a single trace is proved; party-level
non-recurrence and general no-self-appointment are separate claims this
theorem does not make.

**2. `KillSwitchA5O.lean`'s relationship to `KillSwitch.lean`.**
`KillSwitchA5O.lean` restates KS1–KS3 over v4's own `O`/`Appointed`/`R`/
`Revoke`, and specifically carries forward T6/T7 from the standalone
`KillSwitch.lean`, which were already constructive there (no
`Classical` dependency in either file's proof of those two results).
`KillSwitch.lean`'s two genuinely classical theorems —
`survives_iff_not_forgeable` and `boundary`, both depending on
`[propext, Classical.choice, Quot.sound]` via `Classical.byContradiction`
— are not carried forward into `KillSwitchA5O.lean` at all; that file's
own biconditional (`survival_iff_appointer_compromised`) is a different,
independently-derived result over the `Channel` predicate, and is itself
zero-axiom.
