# A⁵O v5 — deployment closure, successor to sealed v1

## Provenance

`Deployment.lean` and `DeploymentTests.lean` in this directory originate from
an externally supplied repair candidate, not authored in this repository. As
delivered, the candidate did not compile: `at` was used as a structure field
name, a reserved Lean token, producing cascading parse errors, and its own
verification report had never actually been run through a Lean kernel. The
candidate was patched and independently verified by the Code session across
two sittings — the field rename, elaborator-visibility fixes for `by decide`
sites, and a further round removing `propext` from all but one fixture proof.
`SOURCE_FIXES.patch` in this directory is the complete diff from the
as-delivered candidate to the files committed here. `A5O.lean` and
`Closure.lean` are unmodified, byte-identical copies of the sealed v4 files
(hashes below) — nothing about the foundation changed.

## Toolchain

`leanprover/lean4:v4.33.1` — the same compiler-of-record as the sealed v4/v1
record. The candidate was originally verified under 4.19.0; migration to
4.33.1 was attempted and succeeded without changes to any file, so there is
no toolchain heterogeneity in the record.

## Axiom status

95 of the 96 theorems in `Audit.lean`'s inventory report zero axioms — 96
across all four imported modules (`A5O.lean` 33, `Closure.lean` 16,
`Deployment.lean` 14, `DeploymentTests.lean` 33; 47 are v5's own). One,
`Apertures.Tests.phantom_not_listed` (`¬ (phantom ∈ demo.executions)`, a
demonstration-file fixture, not a core theorem), depends on `propext`. This
was investigated directly, not merely disclosed: Lean's own `List.mem_cons`
and `List.mem_singleton` lemmas are themselves `propext`-dependent in the
stdlib, and excluding an impossible case in dependent elimination against a
non-matching concrete list element routes through the same dependency —
confirmed under both 4.19.0 and 4.33.1, via direct `List.Mem` constructors,
and via raw term-mode `match`. No proof strategy tried avoided it. Every
other membership fact in the file — all of them positive — was rewritten
using `List.Mem.head`/`List.Mem.tail` directly rather than the stdlib's `Iff`
lemmas, which removed `propext` everywhere it appeared except this one
negative case. Nothing in `A5O.lean`, `Closure.lean`, or core `Deployment.lean`
uses `propext` or any other axiom.

## What this is and is not

`Deployment.lean` here supersedes nothing sealed. The sealed v1
`Deployment.lean` (`a5o/v4/closure/`, hash `b6e79d8f…af67`) remains
unrevised, under its Operator Attestation as corrected. This directory is a
candidate file of record for the Gate's closure going forward; its own
`CheckersSound`, `DecisionsFollowChecker`, `NoSideChannel`, and
`CoversActualExecutions` evidence obligations are not yet attested for
`theapertures.app`, and its decision path does not yet read a server-held
ledger — see `a5o/v4/closure/README.md` for that item's status.

## Reference hashes

```
A5O.lean                0e5ebe3f5113727ae0cd41ec4399661a352fcc4fb522fcfe7ef7be3318f6b452
Closure.lean            af6b3233bdeee80b8312a9138111c597d37f17b792a749d53844314e3a79a933
Deployment.lean         e07c69ae33d1d77e3c8e657f12f8a0fb58d233e8fd5873557c6564afcfdd59da
```
