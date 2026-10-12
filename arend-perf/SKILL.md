---
name: arend-perf
description: Finding and fixing slow Arend typechecking — measuring per-definition times, isolating the expensive step, recognising when the elaborator is normalizing a large term behind your back, and the fixes that work (opaque `\sfunc` + eval lemma at the right layer, named abbreviations, explicit `=` types, `\lemma` for propositions). Use when a definition or module takes seconds to minutes to check, when `--show-times` lists a definition above ~1s, or before writing a long equational chain over terms built from big definitions.
user-invocable: true
---

# Arend typechecking performance

A slow definition is almost never slow because the proof is long. It is slow because, somewhere, the
elaborator compares two terms, the cheap comparison fails, and it falls back to **normalizing both
sides**. That can unfold definitions you never meant to compute with. The cost depends on what the
terms *unfold to*, not on how big the source text is. A one-line `idp` can take four seconds.

Companion to **arend-quirks** §7 (the `\func` / `\sfunc` / `\lemma` semantics) and **arend-prove**
(cache hygiene). This skill is about locating the expensive comparison and stopping it.

---

## 1. Measure first, and make sure the measurement is real

```bash
arend --serialize --show-times <Module>     # per-definition times, sorted descending
arend --serialize --show-sizes <Module>     # core-term sizes; huge terms are a hint, not a diagnosis
```

Before trusting any timing, rule out two cache artefacts. Both make everything look slow, or make it
look fast when it isn't:

- **Caches that fail to load.** Lines like `Definition … is not loaded` or `Deserialization…` mean
  the `.arc` files are being ignored, so every run rechecks the whole dependency cone. A
  wrapper script that greps out noise can hide these lines, so check the raw output once. Fix with a
  cold `arend -r --serialize`.
- **Caches that do not get invalidated.** Seen with CLI 1.12: after editing module `A`, a run on
  `B` (which imports `A`) reused `B.arc` and did not recheck `B`. To time, or even verify, the
  modules downstream of an edit, delete their `.arc` files by hand first:
  ```bash
  grep -rl "import Path.To.A" src     # then rm the matching bin/**/*.arc
  ```

## 2. Isolate the expensive step

`--show-times` reports a whole definition. To find the slow step inside it:

1. **Use a scratch module.** Create a temporary `src/Scratch.ard` that imports the cached modules,
   put one experiment per definition in it, and run `arend --show-times Scratch`. Only the scratch
   module is rechecked, so each round takes seconds. Delete the file afterwards.
   - The `Module:Def` positional is meant for this, but on Windows the CLI parses it as a file path
     and crashes (`InvalidPathException: Illegal char <:>`).
2. **Split the chain.** Copy each `*>` segment of the slow proof into its own `\sfunc` with its
   intermediate equation as the type. The times tell you which segment pays.
3. **Shrink the segment.** Keep the expensive step but swap pieces for variables:
   - Replace `pmap f p` by `pmap f q` with `q` a parameter of the same type.
   - Replace a concrete map by a variable of the same type.
   - Replace the step by `idp` on `X = X`.
   Whichever replacement makes it fast names the culprit. If `idp : X = X` is slow while `idp : Y = Y`
   for a subterm `Y` of `X` is fast, the cost is in what `X`'s head unfolds to.
4. **Print the elaborated term:** `arend <Module> -p <Module>:<Def>`. Implicit arguments that show up
   *normalized* tell you the elaborator computed a type by unfolding. Examples are `\Sigma (f : E -> E) (f base = base)` where
   you wrote `X ->* Y`, or `LinearMap {…} { | func => \lam x => BigSum … }` where the declared type was
   `AddGroupHom (ZFree g) (ZFree h)`.

If you have to look inside the compiler, use Java Flight Recorder:
`java -XX:FlightRecorderOptions:stackdepth=4096 -XX:StartFlightRecording=filename=rec.jfr,settings=profile -jar <cli.jar> …`,
then `jfr print --events jdk.ExecutionSample --stack-depth 4096 rec.jfr`. The default stack depth
(64) cuts off the typechecker frames because normalization recurses deeply. Look for
`CompareVisitor.normalizedCompare` under `CheckTypeVisitor.checkResult`. Breakpoints in `jdb` are
not worth it, because prelude checks hit the same methods first.

## 3. What is actually happening

The elaborator compares two terms in two stages:

1. **A structural comparison without normalization.** Same head, same arguments, recursively. This
   is cheap.
2. **If that fails, normalize both sides to WHNF and compare again**, recursively, normalizing at
   every level where the cheap comparison fails.

Two terms can fail the first stage even though they come from identical source text. This was
observed with `degree {suc n} (project b ->*.∘* (boundaryMap (suc n) ->*.∘* include a))`, written
twice. The same text wrapped in a named `\func` passed the first stage at once. Every such failure
costs a normalization of whatever the terms unfold to.

Two more mechanisms feed it:

- **`a = b` without an explicit type** takes its type from `a`. If `a`'s head unfolds to `\new C {…}`,
  for example through a `\cowith` function such as `LinearMap.toLinearMap`, the inferred type can be
  the *singleton* class call `C { | func => <the whole implementation> }`. Later comparisons then
  carry that implementation around.
- **`pmap f p`** reads its endpoint and codomain types off `p` and `f`. Those types can likewise come
  back normalized.
- **Unsolved universe levels.** A call to a level-polymorphic definition without `.{u}` gets a level
  metavariable `?p`. Two occurrences of the same source text then carry different metavariables, the
  structural comparison fails, and both sides are normalized. In one measurement, `idp : t = t` for a
  term `t` built from a few level-polymorphic homomorphisms took 322ms with inferred levels and 6ms
  with `.{u}` written on every call (see 4.6).
- **Recursive definitions at indices with concrete `suc`s.** A definition by recursion on a `Nat` whose
  `suc` clause mentions the recursive call more than once (directly, or through a record component and
  a proof about it, as a functorial action on iterated loop spaces does) unfolds to a term that doubles
  with every concrete `suc` in the index. The same `idp` took 21ms at index `suc (suc n)`, 83ms at three
  `suc`s and 1.3s at four. Indices built by arithmetic such as `n + suc k` produce such `suc`s silently
  (see 4.7).

## 4. Fixes, in order of preference

### 4.1 Make the right layer opaque: `\sfunc` + eval lemma

Find the definition in the middle of the stack whose unfolding is expensive and whose unfolding is
*used in few places*. Make it an `\sfunc`, add an eval lemma, and rewrite only those few places.

```arend
\sfunc degreeMatrix {m g h : Nat} (f : Bouquet (suc m) g ->* Bouquet (suc m) h) : Matrix Int h g
  => mkMatrix \lam b a => degree {m} (Bouquet.project b ->*.∘* (f ->*.∘* Bouquet.include a))
  \where
    \lemma eval {m g h : Nat} (f : Bouquet (suc m) g ->* Bouquet (suc m) h) (b : Fin h) (a : Fin g)
      : degreeMatrix f b a = degree {m} (Bouquet.project b ->*.∘* (f ->*.∘* Bouquet.include a))
      => pmap (\lam (M : Matrix Int h g) => M b a) (\peval degreeMatrix f)
```

Here `degreeHom f = columnAction (degreeMatrix f)`. Before the change, every comparison involving
`degreeHom (boundaryMap (suc n))` normalized through the entire definition of `boundaryMap`. After
it, the CW chain-complex modules went from **2m32s to 7s**. The individual proofs went from 47s, 26s,
25s, 15s and 15s to under 0.2s each. Only seven proofs had relied on the unfolding, and each needed one
`eval` step.

How to choose the layer:

- **Grep the uses of each candidate.** A definition unfolded in hundreds of places is the wrong one
  to hide. In the case above, `columnAction` had one computation rule, `boundaryMap` had about four
  proofs using its body, and `degreeMatrix` had seven.
- **Time the candidates in the scratch module before editing the library.** Define `\sfunc` copies of
  each and rerun the slow experiment. Here an opaque `degreeMatrix` gave 34ms, an opaque
  `boundaryMap` 169ms, and the original 2.2s.
- **Prefer the layer that produces data** (a matrix, an array, a number) over the layer that
  produces a structure (a `\new` record). Hiding the data keeps the record's shape visible, so
  field projections still compute.

The eval lemma is a `\lemma` when the equation is a proposition. That holds for matrices, integers, and
elements of a set. Otherwise use `\sfunc` (see 4.4). When the unfolded body is an `\elim`, `\peval`
needs the eliminated argument to be a variable, per **arend-quirks**.

### 4.2 Name repeated composites

If the same composite term appears on both sides of many equations, wrap it in a `\func` with its
arguments:

```arend
\func P {C : RelCW} (n : Nat) (b : Fin (C.count (suc n))) (a : Fin (C.count (suc (suc n))))
  => Bouquet.project b ->*.∘* (boundaryMap {C} (suc n) ->*.∘* Bouquet.include a)
```

`degree (P n b a) = degree (P n b a)` checked in 6ms. The inlined version took 2s. The name still
unfolds, so proofs need no change. It just gives the structural comparison something to match. Also
consider this when a `\where` block repeats the same long implicit-argument list, as in
`S {C} {D} {b} F`.

### 4.3 Give `=` and `pmap` their types

- `a = {T} b` with `T` the *declared* type stops the singleton-type inference. In a test, the type
  `degreeHom X = degreeHom X` took 2.5s with the type inferred and 7ms with `= {AddGroupHom …}`.
- `pmap {A} {B} f p`, or a typed lambda `pmap (\lam (h : AddGroupHom G H) => h x) p`, does the same
  for `pmap`.
- These help with type *inference*. They do not stop a later comparison from normalizing, so they
  are cheaper to apply but weaker than 4.1.

### 4.4 Stop proofs from unfolding at their use sites

- **Propositions go in `\lemma`.** Users never see the body, and the lemma is checked once.
- **Equalities in a non-set go in `\sfunc`.** Examples are equalities of pointed maps, of Σ-types
  containing groups, and of data records. `\lemma` rejects them: "The type of a lemma must be a
  proposition".
- **A definition whose *value* is used** (a group homomorphism, a chain map) but whose body is
  expensive can also be an `\sfunc` + `eval`. Then the downstream lemmas state their equations in
  terms of the opaque name and rewrite with `eval` only at the start and the end. For a functorial
  construction, prove its laws (identity, composition, congruence in the map, naturality,
  equivalence) once in its `\where`, each with one `eval` step, and let every other proof use only
  those laws. Then no proof outside that block ever unfolds the body.

### 4.5 Restate a slow lemma in the vocabulary of its caller

If a helper is stated with a different but convertible spelling of the terms the caller uses,
the caller pays a normalizing comparison at every use. One example is the helper saying `CellStep.of F n`
while the caller says `CellSteps.lower (towerSteps F)`. State the helper with the caller's spelling.

### 4.6 Spell out universe levels

When the definitions involved are level-polymorphic, write `.{u}` on every call in both the
statement and the proof of a slow lemma, including calls to lemmas and to the level-polymorphic
definitions inside lambdas passed to `pmap`. A helper that names a lambda (`\func row.{u} … => …`)
and is then applied as `row.{u} …` fixes the level of an otherwise inferred lambda. The test for this
cause: copy the slow equation into a scratch module twice, once without and once with explicit
levels, and compare `idp` on each side.

### 4.7 Keep recursion indices symbolic

If a definition from §3's last bullet is used at an index such as `suc (suc (suc d))`, make the
arithmetic opaque: put the index behind an `\sfunc` (`\sfunc twice (m : Nat) : Nat => m + m`, with
`\peval` lemmas relating `twice (suc m)` to `suc (suc (twice m))`), and move between equal indices with
an explicit cast defined by `\elim` on the index equality. The cast's naturality and equivalence
lemmas are one-line `| _, idp => …` proofs. At most two concrete `suc`s on a variable keep the
unfolding small.

### 4.8 Prove record equalities with a lemma, not with `exts` at the use site

`exts` on an equation between records with propositional fields (homomorphisms, for example)
elaborates the record structure at the call site, which is slow when the two sides are composites
of expensive definitions. In one case `exts p` took 2s and `equals p` 0.2s, where `equals` is a lemma
proved once by `exts` over variables:

```arend
\lemma equals {G H : AddGroup} {f g : AddGroupHom G H} (p : \Pi (x : G) -> f x = g x) : f = g
  => exts p
```

Pass the two sides as explicit implicits, `equals {_} {_} {lhs} {rhs} p`. Otherwise `f` and `g` are
inferred from partially normalized forms of the goal and the argument's type no longer matches.

## 5. What did not help

- Explicit implicit arguments on `pmap degreeHom p` (still 1.5s).
- Binding the term with `\let` first.
- Explicit universe levels, when the terms had no level arguments that differed. Check `-p`
  before suspecting levels. Where levels *are* inferred, they matter a lot (4.6).
- Making the structure-producing layer (`columnAction`) opaque while leaving the inner data
  (`degreeMatrix`) transparent. The type of `=` stopped being a singleton, but `idp` still
  normalized (2.4s).

## 6. Anti-patterns

- **Turning everything into `\sfunc`.** Every opaque definition needs an eval lemma and an explicit
  rewrite wherever its body is used. Hide one layer, measured, not the whole stack.
- **Guessing from source size.** The slow step is wherever an unfolding is expensive, which
  `--show-sizes` and line counts do not show.
- **Optimizing before checking the caches** (§1). A silently ignored cache makes everything slow,
  and an un-invalidated one makes a regression look fixed.
- **Keeping the scratch module.** Delete `src/Scratch.ard` and its `.arc` before a full-library run.
