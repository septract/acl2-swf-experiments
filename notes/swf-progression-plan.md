# Software Foundations Book 1 (Logical Foundations) - ACL2 Progression Plan

## Overview

This document maps theorems and exercises from Software Foundations Volume 1 (Logical Foundations) that we aim to replicate in ACL2. The goal is to work through fundamental concepts systematically, adapting Coq proofs to ACL2's theorem prover.

Source: https://softwarefoundations.cis.upenn.edu/lf-current/

## Chapter Status

### ✅ Chapter 3: Induction - COMPLETED
- [x] `add_0_r`: n + 0 = n
- [x] `minus_n_n`: n - n = 0
- [x] `mul_0_r`: n * 0 = 0
- [x] `plus_n_Sm`: S(n + m) = n + S(m)
- [x] `add_comm`: n + m = m + n
- [x] `add_assoc`: n + (m + p) = (n + m) + p

**Location**: `experiments/arithmetic/experiment-02-induction-basics.lisp`

### ✅ Chapter 4: Lists - COMPLETED
- [x] `nil_app`: [] ++ l = l
- [x] `app_assoc`: (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)
- [x] `rev_length`: length(rev(l)) = length(l)
- [x] `rev_app_distr`: rev(l1 ++ l2) = rev(l2) ++ rev(l1)
- [x] `rev_involutive`: rev(rev(l)) = l
- [x] `app_nil_r`: l ++ [] = l

**Location**: `experiments/lists/experiment-01-list-basics.lisp`
**Key techniques learned**: Helper lemmas about `revappend`, theory control with `:in-theory (disable ...)`

### ✅ Chapter 2: Basics - COMPLETED

Theorems about Natural Numbers:
- [x] `plus_O_n`: 0 + n = n
- [x] `plus_1_l`: 1 + n = n + 1 (adapted for ACL2)
- [x] `mult_0_l`: 0 * n = 0
- [x] `mult_n_1`: n * 1 = n
- [x] `mult_1_n`: 1 * n = n (additional)
- [x] `mult_2_n`: 2 * n = n + n (additional)
- [x] `mult_comm`: n * m = m * n (additional)
- [x] `mult_assoc`: n * (m * p) = (n * m) * p (additional)
- [x] `mult_plus_distr_l`: n * (m + p) = n * m + n * p (distributivity - left)
- [x] `mult_plus_distr_r`: (m + p) * n = m * n + p * n (distributivity - right)

**Location**: `experiments/arithmetic/experiment-03-basics.lisp`
**Note**: ACL2 doesn't have Coq's successor function (S), so `plus_1_l` adapted to commutativity

### ✅ Chapter 5: Polymorphism (Poly) - COMPLETED

Higher-order function theorems:
- [x] `map_rev`: map f (rev l) = rev (map f l)
- [x] `fold_length`: Proving fold-based length function correct
- [x] `flat_map`: Properties of flatMap operation
- [x] Theorems about `filter`, `map`, `fold`
  - map preserves length, distributes over append and reverse
  - filter length bounds, idempotence, distributes over append
  - fold_sum and fold_length correctness
  - Interaction between map and fold

**Location**: `experiments/lists/experiment-02-higher-order.lisp`
**Key techniques learned**: Helper lemmas about `revappend`, concrete types instead of polymorphism
**Note**: `fold-product-append` theorem commented out - needs complex arithmetic lemmas

### 🎯 Challenge Problems (3-4 star exercises from Chapters 2-5)

**Real Challenges** (require non-trivial proof effort in ACL2):
- [ ] **Binary Numbers** ★★★★ HARD (Induction ch.) - 4 theorems
  - Custom data type requires termination proofs and careful reasoning
  - Round-trip conversion properties, normalization, arithmetic
  - Location: `experiments/challenge-problems.lisp`
- [ ] **Function Injectivity** ★★★☆ MODERATE (Lists ch.) - 2 theorems
  - Prove reverse is injective, general involution theorem
  - Requires reasoning about function inverses
  - Location: `experiments/challenge-problems.lisp`

**Trivial Exercises** (solved automatically by ACL2, moved to separate file):
- [x] **Bag Operations** ★☆☆☆ - 3 theorems PROVED automatically (no hints)
- [x] **List Interleaving** ★☆☆☆ - 2 PROVED automatically, 1 discovered FALSE
- Location: `experiments/trivial-swf-exercises.lisp`
- Value: Demonstrates power of ACL2 automation vs manual SWF reasoning

**Excluded** (can't be properly encoded in ACL2):
- Church Numerals - Requires polymorphic higher-order functions
- Currying/Uncurrying - Requires lambdas in theorem statements

**Status**: ✅ REORGANIZED - Separated genuine challenges from trivial exercises
**Key insights**:
- SWF's pedagogical exercises may be trivial with ACL2's automation
- Custom data types (binary) are genuinely harder than built-in types
- Formal proofs caught 2 false theorems that seemed plausible!
- Higher-order function exercises don't translate well to ACL2

### 📋 Chapter 7: Logic

Logical connectives and reasoning:
- [ ] Conjunction commutativity: A ∧ B ↔ B ∧ A
- [ ] Conjunction associativity: (A ∧ B) ∧ C ↔ A ∧ (B ∧ C)
- [ ] Disjunction commutativity: A ∨ B ↔ B ∨ A
- [ ] De Morgan's laws
- [ ] Excluded middle variants (constructive logic considerations)

**Suggested location**: `experiments/logic/experiment-01-connectives.lisp`
**Challenge**: ACL2 uses classical logic, Coq uses constructive logic - some theorems may differ

### 📋 Chapter 8: Inductively Defined Propositions (IndProp)

Inductive predicates:
- [ ] `evenb` predicate and proofs
- [ ] Regular expression matching
- [ ] Reflexive transitive closure
- [ ] Permutation relation

**Suggested location**: `experiments/logic/experiment-02-inductive-predicates.lisp`
**Challenge**: ACL2's defun-sk vs Coq's Inductive propositions

### 📋 Chapter 9: Total and Partial Maps

Data structure theorems:
- [ ] Map update properties
- [ ] Map equivalence theorems
- [ ] Functional correctness of map operations

**Suggested location**: `experiments/data-structures/experiment-01-maps.lisp`

## Topics We May Skip or Adapt

### Coq-Specific Concepts
- **Tactics and proof automation** - ACL2 has different automation (hints, computed hints)
- **Proof objects and term extraction** - ACL2's architecture differs fundamentally
- **Module system details** - ACL2 uses packages differently

### Advanced Topics (for later)
- **Chapter 10+**: ImpParser, Extraction, Auto - more advanced, may tackle after basics

## Mapping Coq Concepts to ACL2

| Coq | ACL2 | Notes |
|-----|------|-------|
| `Inductive nat` | Built-in natural numbers | ACL2 has rationals, use `natp` for naturals |
| `Fixpoint` | `defun` | Must prove termination |
| `Theorem` / `Lemma` | `defthm` | Same concept |
| `simpl` | Automatic simplification | ACL2 does this automatically |
| `rewrite` | `:rewrite` rules | Similar but ACL2's are automatic |
| `induction` | Automatic induction | ACL2 chooses induction scheme |
| `destruct` | Pattern matching in proof | ACL2 does case splits |
| Polymorphism | Type-generic with guards | Different approach |

## Learning Goals

1. **Foundation**: Master basic arithmetic and list proofs (✅ Done)
2. **Techniques**: Learn helper lemmas, theory control, induction schemes
3. **Advanced**: Tackle higher-order functions, inductive predicates
4. **Patterns**: Build a library of reusable proof patterns

## Progress Tracking

- **Completed**: 50+ theorems (16 arithmetic, 34 list)
  - Induction chapter: 6 theorems ✅
  - Lists chapter: 6 theorems ✅
  - Basics chapter: 10 theorems ✅ (added distributivity)
  - Polymorphism chapter: 28 theorems ✅ (added fold-product-append)
- **Next target**: Chapter 7 (Logic) or Chapter 8 (Inductively Defined Propositions)
- **Total chapters to cover**: ~6-8 core chapters

## Notes on ACL2 vs Coq

**Advantages of ACL2**:
- Powerful automatic proof search
- Strong arithmetic decision procedures
- Mature standard library

**Challenges**:
- Must understand rewrite loops and theory control
- Need to know underlying function definitions (e.g., `revappend` for `reverse`)
- Less interactive feedback than Coq's tactic-based approach

## References

- Software Foundations: https://softwarefoundations.cis.upenn.edu/lf-current/
- ACL2 Documentation: https://www.cs.utexas.edu/~moore/acl2/
- Our quick reference: [notes/acl2-quick-reference.md](acl2-quick-reference.md)
