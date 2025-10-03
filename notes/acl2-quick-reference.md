# ACL2 Quick Reference for Beginners

## Core Concepts

**ACL2** is a programming language (based on Common Lisp) combined with a theorem prover. You write functions and then prove properties about them.

## Defining Functions

```lisp
(defun factorial (n)
  (if (zp n)
      1
      (* n (factorial (- n 1)))))
```

**Key points:**
- Use `defun` to define functions
- ACL2 requires proof that recursive functions terminate
- Use `zp` (zero predicate) for natural numbers instead of `(= n 0)`
- Must prove recursive calls decrease toward base case

## Common Predicates

- `(acl2-numberp x)` - is x a number?
- `(integerp x)` - is x an integer?
- `(natp x)` - is x a natural number (≥ 0)?
- `(zp x)` - is x zero (treating non-naturals as zero)?
- `(consp x)` - is x a cons pair (non-empty list)?
- `(endp x)` - is x the end of a list (nil or atom)?

## Proving Theorems

```lisp
(defthm name
  (implies (hypotheses)
           (conclusion)))
```

**Structure:**
- `defthm` creates a theorem
- Use `implies` for conditional theorems
- Use `equal` to show two things are the same
- Simple theorems often prove automatically

## The ACL2 Method

1. **Define functions** carefully with clear base and recursive cases
2. **Test interactively** before trying to prove
3. **State theorems** about your functions
4. **Let ACL2 try** - start simple, many proofs are automatic
5. **Check failed proofs** - look at "key checkpoints" to understand what went wrong
6. **Add lemmas** - prove simpler facts ACL2 can use as stepping stones

## Common Patterns

### Guards (type constraints)
```lisp
(defun safe-div (x y)
  (declare (xargs :guard (and (rationalp x) (rationalp y) (not (= y 0)))))
  (/ x y))
```

### Local lemmas (helper proofs)
```lisp
(local
 (defthm helper-lemma
   ...))
```
Use `local` for lemmas that help prove a theorem but shouldn't be exported.

## List Processing

- `(car lst)` - first element
- `(cdr lst)` - rest of list
- `(cons x lst)` - prepend x to lst
- `(append lst1 lst2)` - concatenate lists
- `(len lst)` - length of list
- `(nth n lst)` - nth element (0-indexed)

## When Proofs Fail

1. **Read the checkpoint** - ACL2 shows the goal it couldn't prove
2. **Check hypotheses** - did you forget to require inputs are numbers/lists?
3. **Prove simpler lemmas** - break complex proofs into steps
4. **Add hints** - guide ACL2's proof strategy (advanced)
5. **Watch for rewrite loops** - sometimes lemmas interfere with each other; use `:hints (("Goal" :in-theory (disable lemma-name)))` to control which rules fire

## Tips

- **Start small** - prove trivial facts first, build up
- **Test functions** before proving - make sure they work as expected
- **Add type hypotheses** - ACL2 functions work on all objects, specify when you need numbers/lists
- **Use built-in functions** - `+`, `*`, `append`, etc. have many lemmas already proved
- **Don't give up** - failed proofs teach you what ACL2 needs to know

## Advanced Techniques

### Understanding Built-in Functions

Many ACL2 functions have non-recursive definitions that expand to other functions:
- `reverse` is defined as `(revappend x nil)`
- `revappend` is the primitive that actually does the work

When proving theorems about functions like `reverse`, you often need lemmas about the underlying primitive (`revappend`).

### Lemma Ordering Matters

The order in which you prove lemmas affects what ACL2 can use:

```lisp
; Prove this first (doesn't depend on other lemmas)
(local
 (defthm append-revappend
   (equal (append (revappend x y) z)
          (revappend x (append y z)))))

; Then prove this (uses the first lemma)
(local
 (defthm revappend-is-append-reverse
   (equal (revappend x y)
          (append (reverse x) y))))

; Finally this (but disable lemma that causes loops!)
(local
 (defthm revappend-of-append
   (equal (revappend (append x y) acc)
          (revappend y (revappend x acc)))
   :hints (("Goal" :in-theory (disable revappend-is-append-reverse)))))
```

### Theory Control

Use `:in-theory` hints to control which lemmas are active:
- `(disable lemma-name)` - turn off a specific lemma
- `(enable lemma-name)` - turn on a specific lemma
- Prevents rewrite loops where lemmas fight each other

## Resources

- [ACL2 Documentation](https://www.cs.utexas.edu/~moore/acl2/)
- [Interactive Try ACL2](https://www.cs.utexas.edu/users/moore/acl2/manuals/current/manual/index-seo.php/ACL2____ACL2-TUTORIAL)
- [Programming Exercises](https://www.cs.utexas.edu/~moore/publications/acl2-programming-exercises1.html)
