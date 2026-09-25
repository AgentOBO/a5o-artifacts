# A⁵O — the control plane, checked over the live gate

## Purpose

`ControlPlane.lean` defines a control plane — a `GatedSystem` (Closure.lean:
nothing executes in an area of consequence unless the system decided it for
some principal) that achieves ADA (A5O.lean v4's `achievesADA`: every
decision it enforces satisfies `O`) — and proves nine theorems about that
definition alone.

`ControlPlaneApertures.lean` assembles v5's `theApertures` (the live gate as
a `GatedSystem` built from a trace) and `gate_achievesADA` into a
`ControlPlane`, and applies every `ControlPlane` theorem to the installation
— over the logged trace and over ACTUAL executions. It proves nine further
theorems at the installation.

All 18 theorems (9 + 9) are zero-axiom: `#print axioms` on every one reports
"does not depend on any axioms," reproduced byte-for-byte in
`ControlPlane_axioms.txt` and `ControlPlaneApertures_axioms.txt` in this
directory.

## Dependencies

Imported unmodified, cited by hash:

| File | SHA-256 |
|---|---|
| `A5O.lean` (v4) | `0e5ebe3f5113727ae0cd41ec4399661a352fcc4fb522fcfe7ef7be3318f6b452` |
| `Closure.lean` (v4) | `af6b3233bdeee80b8312a9138111c597d37f17b792a749d53844314e3a79a933` |
| `Deployment.lean` (v5) | `e07c69ae33d1d77e3c8e657f12f8a0fb58d233e8fd5873557c6564afcfdd59da` |
| `DeploymentTests.lean` (v5) | `1386ffb193f611bf0c33d7f95909e649e567b6c97e19a08e51f2a8f6d86424d8` |

`ControlPlane.lean` imports only `A5O.lean` and `Closure.lean` — it has no
v5 dependency of its own. `ControlPlaneApertures.lean` imports all four
above plus `ControlPlane.lean` itself; it is this file specifically that
requires v5, which is why the pair is placed under `a5o/v5/`, beside the
dependencies it needs, rather than under `a5o/v4/`.

## The four v5 obligations

Kept as explicit hypotheses, not proved here:

- **`CheckersSound`**, **`CoversActualExecutions`** — signed operator
  attestations (claims about the server's own code, not the trace).
- **`DecisionsFollowChecker`**, **`NoSideChannel`** — decided over the
  signed trace (`adapter/AperturesTrace_20260912.lean`/`.json`, v5).

## Scope

It is machine-checked that the installation, under those four obligations,
is a control plane. The theorems fix the form the claim takes; the
deployment facts themselves are carried by the attestations and the signed
trace, not by this file.

## Controls

Removing `CoversActualExecutions` (the hypothesis `ha`) makes the
`ControlPlane` construction over ACTUAL executions fail — it appears in
every theorem below the first in `ControlPlaneApertures.lean`, and the
first (which needs only `CheckersSound`/`DecisionsFollowChecker`/
`NoSideChannel`) does not reach actual executions.

The boundary theorems `silent_is_no_plane` and `quorum_plane_two_governors`
are inside `ControlPlane.lean` (confirmed present at compile time, this
directory's own `ControlPlane_axioms.txt`).

v5's own `bypass_violates_coverage` (`DeploymentTests.lean`) excludes a
receipt-less execution — confirmed present in the dependency copied into
this build.

## Signatures

| Instrument | Envelope | Signed (GMT, 25 Sep 2026) |
|---|---|---|
| `ControlPlane.lean` | `b8034039-02f7-4104-91bf-46b7d0a0f3bb` | 20:33:18 |
| `ControlPlaneApertures.lean` | `b7168496-ee91-4e08-b8b3-266a27bff0e0` | 20:33:47 |
| `ControlPlane_axioms.txt` | `15fa7136-3542-47b6-8c69-ae0205e16d5c` | 20:34:19 |
| `ControlPlaneApertures_axioms.txt` | `944f5efd-f03e-43f8-bfe5-5500efb582fc` | 20:34:50 |

The signatures attest the content as rendered in the signed PDFs. Byte
identity of the source files is carried separately, by the SHA-256 hashes
above and in `MANIFEST.sha256`, and by the OpenTimestamps proofs.

## Toolchain

Lean **4.33.1**, core only (`leanchecker`, no `native_decide`, no
`unsafe`). Re-checked in a scratch directory (not this repository) against
the four dependencies above, copied from this repository and hash-verified
before use.

## Re-verification

```
lean -o A5O.olean A5O.lean
LEAN_PATH=. lean -o Closure.olean Closure.lean
LEAN_PATH=. lean -o Deployment.olean Deployment.lean
LEAN_PATH=. lean -o DeploymentTests.olean DeploymentTests.lean
LEAN_PATH=. lean -o ControlPlane.olean ControlPlane.lean > cp.out 2>&1;  diff cp.out ControlPlane_axioms.txt
LEAN_PATH=. lean -o ControlPlaneApertures.olean ControlPlaneApertures.lean > cpa.out 2>&1;  diff cpa.out ControlPlaneApertures_axioms.txt
LEAN_PATH=. leanchecker --fresh ControlPlane
LEAN_PATH=. leanchecker --fresh ControlPlaneApertures
grep -nE "sorry|^axiom |native_decide|unsafe" ControlPlane.lean ControlPlaneApertures.lean
```

Expected: all builds exit 0; both `diff`s empty (9 lines each, every line
"does not depend on any axioms"); `leanchecker` exits 0 on both; the `grep`
returns nothing.

**Re-verified by:** Claude Code session, 2026-09-25, macOS (Darwin), Lean
4.33.1 via elan.

**Anchoring:** PENDING at commit time.

Verified, not ratified.
