# ink-to-lean

Export Ink laws to Lean 4, so a second, independent kernel checks them.

Ink states laws once, in its `law` form (see Ink's `docs/laws-in-source.md`),
and checks them with its own semantic law kernel. `ink-to-lean` turns a
checked law bundle into a core Lean 4 file (no Mathlib): each law becomes a
theorem, with a proof that mirrors the Ink proof's structure and closes its
leaves with Lean automation. Lean then checks every proof from scratch.

```sh
ink emit-laws knowledge/libraries/general-laws.ink -o general.json > general.names.json
python3 -m ink_to_lean general.json --names general.names.json -o GeneralLaws.lean \
    --lean lean --check --statements GeneralStatements.lean --report report.json
```

`--check` runs Lean and reports any theorem whose exported proof fails;
`--statements` writes a copy in which only those proofs are `sorry`. A
statement is never changed or weakened. Constructs with no faithful
translation are reported as unsupported and left out.

Current results (Lean 4.34.1, core only):

| Library | Laws | Proved by Lean |
|---|---:|---:|
| `general-laws.ink` (lists, folds over any monoid, Option/Result, maps, buffers, records, vectors, `Int`, words, Bool) | 33 | 33 |
| `incremental-laws.ink` (delta rules for sum, group-by, join, views over views) | 8 | 8 |

The exported files are in `examples/`.

## Translation

| Ink | Lean |
|---|---|
| `law name<A, B>(xs: List<A>, f: fn(A) -> B) { ... }` | `theorem name {A B : Type} (f : A → B) (xs : List A) : ...` (parameters in name order) |
| `requires c;` | hypothesis `(hN : c)` |
| `assume a(x: M): l == r;` | hypothesis `(a : ∀ (x : M), l = r)` |
| `u32`, `u64`, `i32`, `Int`, `f32` | `UInt32`, `UInt64`, `Int32`, `Int`, `Float32` (wrapping words, exact `Int`) |
| `List<T>`, `Buffer<T>` | `List T` |
| `Option<T>`, `Result<T, E>` | `Option T`, `Except E T` |
| `Map<K, V>` | `Ink.Map K V`: a sorted association list with Ink's insertion, lookup and removal |
| records, `Vec2..4` | `structure`s |
| helper functions of a law's definition context | `@[simp] def`s (non-recursive only) |
| `foldr`, `foldl`, `sum`, `scan`, `sort`, `at_or`, `map_indexed`, `quot_or`/`rem_or` | `Ink.*` definitions in `InkPrelude.lean` following Ink's reduction rules |

Proofs: `induction` (also generalized), Bool cases, Option/Result cases,
`calc` chains, symmetry, assertions and uses of other laws translate
structurally; uses become applications of the exported theorem with its
assumption proofs; leaves use the `ink_auto` tactic (simp with hypotheses,
`grind` for ring and linear arithmetic, `omega`).

## Trust

- `InkPrelude.lean` is the bridge: a Lean proof is about these definitions.
  They follow the reduction rules of Ink's checker (`core/src/laws.rs`,
  `core/src/owned_semantic.rs`); a mismatch would make a Lean proof about the
  wrong function, so changes to Ink's semantics must be mirrored here.
- Maps are modelled on all association lists, a superset of the maps Ink can
  build (sorted, unique keys); a law proved over the superset holds for Ink.
- `Float32` follows IEEE hardware arithmetic, not Ink's canonical-NaN binary32
  contract; laws with float arithmetic should not be exported as evidence.
- Nothing here is trusted by Ink, and Lean acceptance grants no rewrite
  authority in Ink.

## Tests

```sh
INK_TO_LEAN_LEAN=/path/to/lean python3 -m unittest discover -s tests
```

The Lean tests check every example law and that a falsified statement
(`x + 4294967295 + 2 == x`) is reported as a failure.

## Hunchroom

Each exported theorem is a self-contained statement over the prelude, so it
can be posted as a problem: the statement with `sorry` from `--statements`,
the full file as the reference proof. The prelude's definitions must be
included with the statement.

## Source contract evidence

The exporter also accepts the `ink-contracts-v1` `evidence.json` produced by
Ink's knowledge-owned contract proof author. Pure contract laws use the same
translation as ordinary law bundles; names and source bindings confer no proof
authority. First-order state theorems are reported as unsupported by this Lean
translator. They remain checked by Ink's inductive kernel; no Lean check of
those obligations is claimed. Structural equality translates only for exact
non-floating scalar/list/Option/Result values. Raw-bit float identity is not
silently translated into Lean's numeric Float32 equality.
