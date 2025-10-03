# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Repository Purpose

This repository contains small proof experiments using the ACL2 theorem prover. The goal is to explore ACL2's capabilities through focused, isolated experiments rather than building a single large system.

## Project Structure

- **experiments/** - Experiments organized by topic (arithmetic, lists, logic, data-structures)
- **utils/** - Shared utility functions and lemmas used across experiments
- **notes/** - Learning notes and lessons learned

## Working with ACL2

### File Conventions

- ACL2 source files use `.lisp` extension
- Files are called "books" in ACL2 terminology
- All ACL2 books should start with `(in-package "ACL2")`
- Mark helper lemmas as `local` if they shouldn't be exported from a book

### Running ACL2

Start the ACL2 REPL:
```bash
acl2
```

Load a book in the ACL2 REPL:
```lisp
(include-book "path/to/book")
```

Certify a book (verify all proofs):
```bash
cert.pl path/to/book.lisp
```

### Development Workflow for Experiments

1. Create new experiment files in the appropriate `experiments/` subdirectory
2. Name files descriptively: `experiment-NN-description.lisp`
3. Use `include-book` to load `utils/common.lisp` or other dependencies
4. Test proofs interactively in the ACL2 REPL before certifying
5. Document interesting findings in `notes/lessons-learned.md`

### Shared Utilities

The `utils/common.lisp` file contains shared definitions used across multiple experiments. Add reusable lemmas and functions here rather than duplicating them across experiment files.

## Learning ACL2

See [notes/acl2-quick-reference.md](notes/acl2-quick-reference.md) for a concise guide covering:
- Function definitions and termination
- Common predicates and patterns
- Theorem proving basics
- What to do when proofs fail

## Resources

- [ACL2 Documentation](https://www.cs.utexas.edu/~moore/acl2/)
- [ACL2 Manual](https://www.cs.utexas.edu/users/moore/acl2/manuals/current/manual/)
