; Correctness proofs for natural number encoding
; This file contains additional correctness theorems that link the cons-based
; nat* encoding to built-in ACL2 arithmetic. These proofs require careful
; theory management and work in an interactive session but may be fragile
; during book certification.
;
; This file is separate from experiment-04-natural-numbers.lisp to keep the
; main file stable while allowing experimentation with these more advanced proofs.

(in-package "ACL2")

; Include the base natural numbers book
(include-book "experiment-04-natural-numbers")

;;; Helper lemmas for correctness proofs

; We need to explicitly prove that S increments nat*-to-nat by 1
; This is marked local since it's subsumed by nat*-to-nat-of-s from the parent book
(local
 (defthm nat*-to-nat-of-s-explicit
   (implies (natp* n)
            (equal (nat*-to-nat (s n))
                   (+ 1 (nat*-to-nat n))))))

; plus* preserves natp* (needed for type reasoning in correctness proofs)
(defthm plus*-preserves-natp*-global
  (implies (and (natp* n) (natp* m))
           (natp* (plus* n m)))
  :hints (("Goal" :in-theory (disable plus*-comm plus*-n-sm))))

; mult* preserves natp* (needed for type reasoning in correctness proofs)
(defthm mult*-preserves-natp*-global
  (implies (and (natp* n) (natp* m))
           (natp* (mult* n m))))

;;; Main correctness theorems

; nat*-to-nat distributes over plus*
; This is the key lemma for proving plus*-correct
; We need to disable S to prevent premature expansion and use our local lemma
(defthm nat*-to-nat-of-plus*
  (implies (and (natp* n) (natp* m))
           (equal (nat*-to-nat (plus* n m))
                  (+ (nat*-to-nat n) (nat*-to-nat m))))
  :hints (("Goal" :in-theory (disable s)
                  :induct (plus* n m))))

; plus* correctly implements addition
; This proves that our encoding is correct with respect to built-in arithmetic
(defthm plus*-correct
  (implies (and (natp n) (natp m))
           (equal (nat*-to-nat (plus* (nat-to-nat* n) (nat-to-nat* m)))
                  (+ n m))))

; nat*-to-nat distributes over mult*
; This is the key lemma for proving mult*-correct
; We need to disable S to prevent premature expansion
(defthm nat*-to-nat-of-mult*
  (implies (and (natp* n) (natp* m))
           (equal (nat*-to-nat (mult* n m))
                  (* (nat*-to-nat n) (nat*-to-nat m))))
  :hints (("Goal" :in-theory (disable s))))

; mult* correctly implements multiplication
; This proves that multiplication in our encoding matches built-in multiplication
(defthm mult*-correct
  (implies (and (natp n) (natp m))
           (equal (nat*-to-nat (mult* (nat-to-nat* n) (nat-to-nat* m)))
                  (* n m))))
