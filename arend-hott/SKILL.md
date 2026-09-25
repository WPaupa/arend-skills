---
name: arend-hott
description: Formalizing synthetic homotopy theory in arend-lib — truncation levels and their off-by-one conventions, eliminating out of `\truncated \data`, doing path induction on a structure field (the endpoint-generalization trick), proving equalities of pointed maps and other dependent pairs, and reusing the h-level/equivalence helpers instead of reproving them. Use when working under `Homotopy/`, when a proof needs `\elim` on a path whose endpoint is a field projection, or when a truncated-data elimination is rejected.
user-invocable: true
---

# Homotopy theory in arend-lib — conventions and pitfalls

Notes from building connectivity and homotopy-group layers on top of arend-lib's existing
`Homotopy/` tree. Companion to **arend-quirks** (language paper-cuts) and **arend-levels** (the
universe errors that dominate this area).

---

## 1. Fix the index convention once, in a header comment

arend-lib's h-level predicate is shifted relative to the HoTT book:

```text
A ofHLevel_-1+ n   is the book's (n-1)-type
Trunc_-1+ n A      is the book's (n-1)-truncation
```

So `n = 0` is "proposition", `n = 1` is "set". Any numeric connectedness/truncatedness API you build
on top inherits the shift, and every derived arithmetic statement inherits it again. Two consequences:

- **State the convention in the module's header comment.** It is the single most valuable comment in
  such a file, because no signature reveals it.
- **Re-derive the arithmetic in the shifted indices rather than translating book formulas.** For
  example, "S^m ∗ S^n ≃ S^(m+n+1)" and "book-(i)-connected join book-(j)-connected is
  book-(i+j+2)-connected" both come out as `suc (m + n)` in the shifted API — but only one of those
  is a coincidence. Sanity-check a degenerate case by hand (e.g. `m = n = 0`) before believing the
  statement.

Pick the sphere index the same way. In the shifted convention an `n`-type is `Sphere n`-null, *not*
`Sphere (suc n)`-null; the `+1` from the book cancels against the `-1` in the indexing.

---

## 2. Test definitional equality before you prove anything

Layers built by specialization very often coincide *definitionally* with the thing they specialize.
Before writing comparison lemmas, transports, or `QEquiv`s, check with a throwaway module:

```arend
\func t1 (n : Nat) (A : \Type) : SomeLocalization A = Trunc_-1+ n A => idp
\func t2 (n : Nat) {A : \Type} (a : A) : someUnit a = inT a => idp
```

If `idp` typechecks, the planned comparison theorems do not exist as proof obligations — delete
them from the plan and record the fact in a comment instead of shipping `idp`-bodied lemmas.

This also tells you the *shape* to state downstream results in: state them in the concrete,
user-facing form (`Trunc_-1+`), not the abstract one (`LType`), since they are the same term.

---

## 3. Eliminating out of `\truncated \data`

For `\truncated \data T : \Set` (e.g. `Trunc0`), pattern matching is allowed only when the result
type lives in a universe ≤ `\Set`. In practice:

| Target | What works |
|---|---|
| a `\Prop` (including any path in a `\Set`) | plain `\func` / `\lemma` with `\elim` |
| a `\Set` given by a `\level` proof | **`\sfunc` only** |

A `\level` annotation does **not** unlock a plain `\func`:

```
Pattern matching on truncated data type 'Trunc0' is allowed only in \sfunc and \scase
```

So the general eliminator has to be `\sfunc`, which does not reduce — which is exactly why the
propositional truncation in `Logic.ard` ships `TruncP.rec` *together with* `TruncP.rec-eval`. Mirror
that shape rather than inventing a new one:

```arend
\sfunc rec {A B : \Type} (p : isSet B) (t : Trunc0 A) (f : A -> B) : B \level p \elim t
  | in0 a => f a

\lemma rec-eval {A B : \Type} {p : isSet B} {a : A} {f : A -> B} : rec p (in0 a) f = f a \level p _ _
  => \peval rec p (in0 a) f
```

Downstream, every use of `rec` needs `rec-eval` to compute. Budget for that: a "two-line" inverse
law becomes `pmap someMap Trunc0.rec-eval`.

**Two truncations of the same thing will coexist.** A library can easily end up with both a
`\truncated \data` set-truncation and a HIT `Trunc_-1+ 1`. They are equivalent but not
interchangeable. Build the bridging `QEquiv` **once**, in the `\where` of the theorem that first
needs it, and route everything through it — do not let the mismatch leak into several proofs.

---

## 4. Path induction on a structure field: generalize the endpoint

This is the highest-value trick in this area.

A pointed map is `f : X ->* Y`, i.e. `\Sigma (g : X -> Y) (g base = base)`. Many lemmas about the
induced map on loop spaces want induction on `f.2`. You cannot match it with `idp`: matching
requires one side of the equation to be a *variable* not occurring in the other, and `base {Y}` is a
field projection, not a variable.

**Restate the lemma over the raw components, with the endpoint as its own parameter.** Then the
endpoint *is* a variable and `\elim` works:

```arend
\func lem {X : Pointed} {E : \Type} (f1 : X -> E) {y : E} (f2 : f1 base = y) (p q : base {X} = base)
  : <statement about (inv f2 *> pmap f1 _ *> f2)> \elim y, f2
  | _, idp => <one line>
```

Apply it at the real map with `lem f.1 f.2 ...`; the instantiation `y := base {Y}`, `f2 := f.2` is
definitional, so the pointed statement follows immediately. The same move works for any path whose
endpoint is a projection: **make the endpoint an explicit parameter and eliminate it alongside the
path.**

### When the trick is not enough

It fails as soon as the *statement itself* must mention structure that needs the codomain to be a
`Pointed` (or any record), not a bare type — for instance a statement about composition of pointed
maps, which has to mention the composite's basepoint proof.

The fix is not a cleverer generalization; it is to **factor the definition below the structured
layer** so the hard lemma can be stated in raw path algebra:

```arend
\func loopMap {A B : \Type} (f : A -> B) {a : A} {b : B} (q : f a = b) (z : a = a) : b = b
  => inv q *> pmap f z *> q
  \where {
    \func idp-case ... : loopMap f q idp = idp
    \func comp      ... : loopMap (g `o` f) (pmap g q *> r) z = loopMap g r (loopMap f q z)
    \func comp-coh  ... : <the 2-dimensional coherence, stated in raw paths>
  }

\func Loop-Func {X Y : Pointed} (f : X ->* Y) : Loop X ->* Loop Y
  => (loopMap f.1 f.2, loopMap.idp-case f.1 f.2)
```

Because nothing in `comp`/`comp-coh` mentions `Pointed`, both endpoints generalize and both proofs
collapse under `\elim b, q, c, r | _, idp, _, idp`. Coherences that look intimidating routinely
reduce to `idp` in the fully-eliminated case — **write the `| _, idp, _, idp => idp` clause first and
let the typechecker tell you** before investing in a hand-built 2-path.

Refactoring an existing definition to sit on top of such a helper is safe when the new body is
*definitionally* the old one: dependent proofs keep working untouched.

---

## 5. Equality of pointed maps (and other dependent pairs)

`->*.ext` takes a pointwise equality of the underlying functions **and a coherence** relating the two
basepoint proofs. The coherence is a 2-dimensional obligation and is where the work is.

Structure it as: prove the pointwise part as one raw lemma, the coherence as a *second* raw lemma
stated entirely in path expressions, then feed both to `ext`. Do not try to produce the coherence
inline — you lose the ability to path-induct on it.

Useful sanity check: many "obvious" structural equalities of pointed maps (identity laws, unit
coherences) are `idp` once the definitions reduce. Try `idp` before `ext`.

---

## 5a. Universal properties of HITs: state the glue as a dependent path

For a *dependent* eliminator, giving the glue datum as `transport P (ppglue c) (lm (u c)) = rm (v c)`
forces the section round-trip through a 2-dimensional uniqueness argument. State it as
`Path (\lam i => P (pglue c i)) (lm (u c)) (rm (v c))` instead: the eliminator's clause becomes
`| pglue c => gm c`, both round-trips are `idp`, and the equivalence is four lines.

Bonus: if the map you eliminate along is constant on the gluing path, that family is definitionally
constant, so the dependent path *is* an ordinary path and no transport correction survives.

## 5b. Computing with univalence transports

- `transport (\lam T => T) (QEquiv_= e) x` reduces to `e.f x`.
- A **`*>`-chain of such paths does not** — `*>` eliminates its right argument. Peel with
  `transport_*>` first; `==<`/`>==` chains are exactly this shape.
- `coe` over an interval-indexed `\data` does not reduce even on a constructor that ignores the
  interval. Supply the path by hand: `pathOver.conv (path (\lam i => tinl {…} {i} y t))`, spelling
  out the constructor's implicits — they will not infer inside the lambda.

Keep such computation lemmas inside the `\where` of the construction they compute, where the
parent's parameters are already threaded.

## 6. Reuse the h-level and equivalence plumbing

Before writing any transport-of-h-level or transport-of-contractibility helper, check for these.
Reproving them is a common waste:

| Need | Use |
|---|---|
| move `Contr` across an equivalence | `Contr.Contr_QEquiv` |
| `Contr` of a path type in a contractible/prop type | `isProp=>PathContr`, `isProp=>isContr` |
| raise an h-level | `HLevel_-1_suc`, `HLevel_-1_+`, `HLevel_-1_<=` |
| h-levels closed under Σ/Π/retract/embedding | `HLevels-sigma`, `HLevels-pi`, `HLevel-retracts`, `HLevels-embeddings` |
| a type equality from an equivalence and back | `QEquiv_=`, `=_Equiv`, `Equiv.toQEquiv` |
| `IsEquiv` of a composite | `IsEquiv.trans` |
| fibers of a first projection / of a precomposite | `proj-fib`, `fib-precomp`, `totalEquiv.totalFiber` |

When a proof reduces to "this h-level fact, transported", it is nearly always one of the above plus
one `pmap`.

---

## 7. Anti-patterns

- **Translating book index arithmetic literally** into a shifted-index API. Re-derive, then check a
  degenerate case.
- **Writing a comparison `QEquiv` before testing `idp`.** Specializations of an abstract construction
  are frequently definitionally equal to the concrete one.
- **Trying harder to generalize a lemma that mentions record structure.** If the endpoint you need to
  eliminate is a field projection *and* the statement needs the record, factor the definition
  instead.
- **Building a bespoke 2-path for an `ext` coherence** before checking whether the fully-eliminated
  case is `idp`.
- **Letting two truncations of the same type leak into several proofs.** Bridge once, in a `\where`.
- **Using a `\sfunc` eliminator without its `-eval` lemma.** It will not reduce, and the failure
  surfaces far from the definition as an unprovable-looking equation.
- **Building an equivalence pointing the wrong way.** `IsEquiv` is a `\Prop`, so its quasi-inverse
  comes from the `\sfunc` `IsEquiv.ret` and never reduces. Any map you will later have to *compute*
  with must be the forward one: pick the direction of each equivalence in a chain so that the
  composite you need is built, not inverted.
