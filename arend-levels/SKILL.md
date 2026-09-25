---
name: arend-levels
description: Diagnosing and fixing Arend universe-level errors — when a definition needs its own `.{u}` parameter, how level parameters propagate through `\where` blocks and call sites, why cumulativity does not rescue a universe-indexed proposition, and the error messages that mean "this is a level problem". Use whenever a typecheck fails with `Cannot solve equations ? <= ?p1`, `Infinite level is not allowed here`, or a `Type mismatch` whose two sides differ only by `.{...}` annotations.
user-invocable: true
---

# Arend universe levels — when you need `.{u}`, and what goes wrong

Level errors are the single most common source of friction when extending a level-polymorphic
corner of arend-lib (`Homotopy/`, `Equiv/`, the algebra class hierarchy). They are also the easiest
to misdiagnose, because the reported `Type mismatch` usually prints two types that *look identical*
and differ only in an invisible or elided level annotation.

Companion to **arend-quirks** §5, which states the level *rules*; this skill is about the *failures*.

---

## The propagation rule

> A definition needs its own level parameter **iff its statement mentions something that itself
> demands `\Type u` / `SomeClass.{u}` arguments.**

That is the whole rule, and it is checkable mechanically. Two definitions sitting next to each
other, over the same objects, can legitimately differ:

```arend
-- Needs nothing: `Loop`, `->*` and `PointedProduct` are all declared over bare (infinite) `Pointed`.
\func Loop-Func {X Y : Pointed} (f : X ->* Y) : Loop X ->* Loop Y => ...

-- Needs `.{u}`: `Omega^` is declared as `Omega^.{u} (n : Nat) (X : Pointed.{u})`,
-- so anything whose *type* mentions `Omega^` must supply that `u`.
\func Omega^-Func.{u} (n : Nat) {X Y : Pointed.{u}} (f : X ->* Y) : Omega^ n X ->* Omega^ n Y => ...
```

**Do not add `.{u}` speculatively.** It is noise, it forces every call site to agree on a level it
did not care about, and it hides the real dependency. The cheap way to find out is an experiment:
strip the annotation, re-typecheck, put it back only if the typechecker objects.

**`\where` members do not inherit the enclosing definition's level parameters.** A `\where`-nested
lemma whose statement mentions the level-polymorphic parent must re-declare `.{u}` itself. This is
the same non-inheritance that bites with implicit binders (see **arend-formalize**, "Cannot infer
implicit X inside a `\where`-block lemma").

---

## Declared result level vs. actual level

This distinction causes the most confusing failures.

```arend
\instance Loop (X : Pointed) : Pointed
  | E => base = {X} base
  | base => idp
```

`Loop`'s *declared* result is bare `Pointed` (infinite level). But the value it produces is a
class-call `Pointed (base = base) { | base => idp }`, whose actual level is computed from `X`. So
for `X : Pointed.{u}`:

- **Works** — using `Loop X` where a *type* at level `u` is wanted, because the coercion projects
  the carrier `base = base : \Type u`:
  ```arend
  \func piLoopShift.{u} (n : Nat) (X : Pointed.{u}) : QEquiv {pi n (Loop X)} {pi (suc n) X} => ...
  ```
- **Fails** — passing `Loop X` as an implicit argument that is *declared* `Pointed.{u}`:
  ```
  Cannot infer an instance of class 'Pointed'
    Candidate is: Loop ?X
    Since types of the candidates are not less than or equal to the expected type
    Expected type: Pointed.{?p1}
      Actual type: Pointed (base {?X} = base {?X}) { | base => idp ... }
  ```
  Fix: supply the implicit explicitly — `f {n} {k} {Loop X} arg` — rather than making `Loop`
  level-polymorphic.

**Never widen an existing library signature to `.{u}` to fix your own downstream code without
checking whether the call site can be fixed instead.** Making a widely used definition
level-polymorphic cascades: every consumer that mentions it then needs its own `.{u}`, and you will
be editing a dozen unrelated definitions before you notice the fix belonged in one place.

---

## Cumulativity gets you less than you expect

Cumulativity (`\Type0` values are usable where `\Type u` is expected) applies to **arguments**. It
does **not** make a universe-indexed *predicate* at one level the same proposition as at another:

```
Type mismatch:
  Expected type: \Pi (Z : Local.{u} {truncUniverse.{u} 0}) -> isLocal Z.S
    Actual type: \Pi (Z : Local.{0} {truncUniverse.{0} 0}) -> isLocal Z.S
```

Here a `\Prop`-valued connectedness predicate was proved at level `0` (about a `\Type0` object) and
needed at level `u`. The object is small; the *statement* is not. The fix is to make the lemma
level-polymorphic and state it at the level you will use it at:

```arend
\lemma sphere0-nconnected.{u} : isNConnectedType.{u} 0 (Sphere 0) => ...
```

Note the explicit `.{u}` on the *predicate* in the result type. A bare `isNConnectedType 0 (Sphere 0)`
would be inferred at level 0 again.

---

## Cumulativity leaves the level *unsolved*, not wrong

Passing `X : C.{u}` to something declared over `C.{p}` constrains `p >= u` and nothing more, so `p`
stays a metavariable. Inside a definition body this is invisible until the result has to match an
expected type that already says `.{u}`, and the report is a `Type mismatch` between two terms that
differ only in `?p1` versus `u`. Supplying the *implicit arguments* does not help — the level is a
separate slot. Write `f.{u} args`, at every call in the body.

A definition whose **result type** pins the level is immune, which is why factoring a subterm out
into its own named `\func` with a spelled-out result type fixes this as a side effect.

## Transporting along a path *between types*

`transport (\lam T => T) p x` fails with `Cannot infer parameter 'A' of definition 'transport'` and
the unhelpful `Candidate is: \Type`: the index type here is a universe, and the elaborator will not
guess its level. Write `transport {\Type u} (\lam T => T) p x`, and give the enclosing definition a
`.{u}`. The same applies to every `transport_*>` / `transport_pmap` step in such a chain.

Two traps follow. A `\where` member cannot name the parent's level parameter, so give it its own
(`.{v}`) and let the call site unify. And do not name a level parameter after a value parameter —
`\func f.{u} (u : J -> A)` makes `f.{u}` ambiguous; rename the level to `.{l}`.

## Error message → cause

| Message | What it actually means |
|---|---|
| `Cannot solve equations` / `? <= ?p1` | A level metavariable was never determined. Usually a missing `.{u}` on the definition you are writing, or an argument whose level the elaborator cannot read off. |
| `Cannot solve equation u <= constant` | You passed a level-`u` object where something concrete (typically level 0) was expected, or vice versa. Pass the level explicitly: `f.{u} args`. |
| `Infinite level is not allowed here` | A truncated universe (`\Set`, `\n-Type`) or a class with a `\Set`/`\Type u` carrier appeared where a *finite* level is required. Most often in an ascription like `a = {Group} b`; write `= {Group.{u}}` and give the enclosing definition a `.{u}`. |
| `Type mismatch: Expected C.{?p1} / Actual C` | A definition declared over bare (infinite) `C` is being fed to something declared over `C.{u}`. See "Declared result level vs. actual level". |
| Two printed types that look character-for-character identical | Look for elided `.{...}`. Re-read with the level annotations in mind before suspecting anything else. |

---

## Call-site tools, in order of preference

1. **Explicit implicit arguments** — `f {A} {B} args`. Often enough on its own: it gives the
   elaborator the levels indirectly, without changing any signature.
2. **Explicit level application** — `f.{u} args`, and on the *result-type* occurrence of a
   predicate, `P.{u} x = ...`.
3. **Explicit level on a local lambda** — `\lam (P : SomeClass.{u}) => ...` when a `pmap`/`transport`
   motive is the thing that cannot be placed.
4. **A new `.{u}` on your own definition** — correct when the propagation rule says so.
5. **Widening a library signature** — last resort, and only after confirming 1–4 cannot work.

---

## Anti-patterns

- **Sprinkling `.{u}` until it compiles.** Each one you add is a constraint every caller inherits.
  Add one, re-typecheck, and if the error moves rather than disappears you probably needed an
  explicit implicit at the call site instead.
- **Leaving `.{u}` on definitions that stopped needing it** after a refactor. Strip-and-recheck is
  cheap; unnecessary level parameters make later call sites fail for no reason.
- **Reading the `Type mismatch` body before checking for level annotations.** If the two sides read
  the same, it *is* a level error, and no amount of staring at the term will show it.
- **Fixing a level error by making a core definition polymorphic.** That is the change with the
  largest blast radius and is almost never the minimal fix.
