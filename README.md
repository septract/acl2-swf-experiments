# ACL2 Experiments

This repository contains small proof experiments using the ACL2 theorem prover.

## Structure

- **experiments/** - Main experiments organized by topic
  - **arithmetic/** - Arithmetic-related proofs
  - **lists/** - List manipulation proofs
  - **logic/** - Logic and reasoning experiments
  - **data-structures/** - Data structure experiments
- **utils/** - Shared utility functions and lemmas
- **notes/** - Documentation and learning notes

## ACL2 Basics

- Source files use `.lisp` extension
- Files are called "books" in ACL2
- Use `include-book` to load dependencies
- Books can be certified with `certify-book`

## Running ACL2

Start ACL2 from the command line:
```
acl2
```

Load a book in ACL2:
```lisp
(include-book "path/to/book")
```

## Resources

- [ACL2 Documentation](https://www.cs.utexas.edu/~moore/acl2/)
- [ACL2 Manual](https://www.cs.utexas.edu/users/moore/acl2/manuals/current/manual/)
