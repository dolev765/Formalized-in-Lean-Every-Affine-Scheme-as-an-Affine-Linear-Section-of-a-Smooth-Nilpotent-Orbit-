# Comparator verification

```sh
python3 scripts/check_comparator.py
```

Compares `Universality.affine_orbit_universality_explicit` with the fixed reference
commit in [comparator.json](comparator.json), including the definitions in its statement. The pinned
upstream Comparator enforces the axiom allowlist and replays the solution through
Lean's kernel. `Statements.lean` remains the public theorem and direct Lean audit.

The reference builds in a separate checkout using its own pinned dependencies. It
is never regenerated from the current statement. Changing `reference_commit`
changes the specification being audited and requires reviewing that specification.

This command builds trusted repository sources; it is not a sandbox for adversarial
submissions. It uses Comparator's comparison and kernel APIs on separate exports.
