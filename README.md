# arend-skills

Claude Code skills for working with [Arend](https://arend-lang.github.io/), a
dependently-typed proof assistant based on homotopy type theory.

Each directory is a self-contained skill: a single `SKILL.md` whose frontmatter
tells the agent when to load it.

| Skill | What it is for |
| --- | --- |
| [`arend-formalize`](arend-formalize/SKILL.md) | Turning an informal mathematical statement into a typechecking Arend definition or lemma — what to read first, which CLI tools to use, and the order of operations up to "only GOAL errors remain". |
| [`arend-prove`](arend-prove/SKILL.md) | Filling in `{?}` placeholders once the statement typechecks, plus the catalog of metas (`rewrite`, `cases`, `mcases`, `simplify`, `equation`, `cong`, `ext`, `linarith`, `unfold`, …) and the lookup discipline. |
| [`arend-quirks`](arend-quirks/SKILL.md) | Survival notes on how Arend's syntax and semantics differ from Coq/Agda/Lean — the things that surprise you after reading the tutorial. |
| [`arend-levels`](arend-levels/SKILL.md) | Universe-level errors: when a definition needs its own `.{u}`, how level parameters propagate, why cumulativity does not rescue a universe-indexed proposition, and which messages mean "this is a level problem". |
| [`arend-hott`](arend-hott/SKILL.md) | Synthetic homotopy theory in arend-lib: truncation index conventions, eliminating out of `\truncated \data`, path induction on a structure field, and the h-level/equivalence helpers worth reusing. |
| [`arend-error-type-mismatch`](arend-error-type-mismatch/SKILL.md) | Diagnosing misleading `Type mismatch: Expected X, Actual Y` errors, where the printed types are downstream effects of an upstream name-resolution or implicit-inference failure. |
| [`arend-error-extraneous-input`](arend-error-extraneous-input/SKILL.md) | Diagnosing `extraneous input '<tok>' expecting {...}` parser errors. The reported token is almost never the bug. |

`arend-formalize` → `arend-prove` is the intended pipeline: the first gets a file
to the point where only goals remain, the second closes them. The two
`arend-error-*` skills are reference material consulted when a typecheck fails,
as are `arend-levels` (for level errors specifically) and `arend-hott` (when the
subject matter is homotopy-theoretic).

## Installation

Clone anywhere, then make the skill directories visible to Claude Code by
symlinking them into your skills directory:

```sh
git clone https://github.com/sxhya/arend-skills.git
cd arend-skills
for d in arend-*/; do ln -sfn "$PWD/${d%/}" ~/.claude/skills/; done
```

Use `~/.claude/skills/` for skills available in every project, or
`<project>/.claude/skills/` to scope them to one repository. Copying the
directories instead of symlinking works equally well.

## Notes

Some skills reference absolute paths on the author's machine (for example the
local checkout of `arend-lib`); adjust those to your own layout.
