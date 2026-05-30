# Project conventions for Claude

## Lean code style

- No comments. Strip `--` line comments, `/-- ... -/` docstrings, and `/-! ... -/` section markers from all Lean files. Lemma names and proof structure should be self-explanatory.
- Trailing `;` on each tactic line (e.g. `intro x;`, `grind;`, `rfl;`). Follow the project's existing style (see `Propositional/FMT/Completeness.lean`, `Modal/Proof/N.lean`).
- Prefer `grind;` over `tauto;` for boolean / propositional goals. The project marks `Forced`, `Forces`, etc. with `@[grind]`, so `grind` often closes goals where `tauto` would. Fall back to `tauto;` only if `grind` fails.

## Workflow

- Commit per lemma. After each formalized lemma/theorem builds without new `sorry`, create a git commit. Use a short title describing the lemma; don't bundle multiple lemmas unless asked.
- Co-author every commit with Claude:

  ```
  git commit -m "$(cat <<'EOF'
  <title>

  <body>

  Co-Authored-By: Claude Opus 4.7 <noreply@anthropic.com>
  EOF
  )"
  ```

  Update the Claude model name if it changes.
- Don't wrap `lake build` in `timeout 300` (or any shell `timeout`). Call `lake build` directly.

## Paper

- Section 6 of the paper (Modal companions) is being formalized step-by-step in `VeryWeakSubintuitionistic/ModalCompanion/`.
- The propositional formulas live in `VeryWeakSubintuitionistic/Propositional/`; the modal ones in `VeryWeakSubintuitionistic/Modal/`. Note `Modal.Formula` only has `imp` and `box` as primitives — `⋏`, `⋎`, `∼`, `⊤` are abbreviations.
