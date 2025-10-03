; Natural numbers from first principles, following Software Foundations
; Source: https://softwarefoundations.cis.upenn.edu/lf-current/Basics.html
;
; In Software Foundations, natural numbers are defined inductively:
;   Inductive nat : Type :=
;     | O : nat
;     | S : nat → nat.
;
; In ACL2, we encode this as a recursive data structure:
;   - 0 represents O (zero)
;   - (cons 'S n) represents S(n) (successor)

(in-package "ACL2")

;;; Data structure for natural numbers

; Recognizer: is this a natural number in our encoding?
(defun natp* (n)
  (if (equal n 0)
      t
      (and (consp n)
           (equal (car n) 'S)
           (natp* (cdr n)))))

; Constructor: O (zero)
(defun O ()
  0)

; Constructor: S (successor)
(defun S (n)
  (declare (xargs :guard (natp* n)
                  :verify-guards nil))
  (cons 'S n))

;;; Operations on our natural numbers

; Addition: defined recursively
; In Coq: Fixpoint plus (n : nat) (m : nat) : nat :=
;   match n with
;   | O => m
;   | S n' => S (plus n' m)
;   end.
(defun plus* (n m)
  (declare (xargs :guard (and (natp* n) (natp* m))
                  :verify-guards nil))
  (if (or (not (natp* n)) (equal n 0))
      m
      (S (plus* (cdr n) m))))

; Multiplication: defined recursively
; In Coq: Fixpoint mult (n m : nat) : nat :=
;   match n with
;   | O => O
;   | S n' => plus m (mult n' m)
;   end.
(defun mult* (n m)
  (declare (xargs :guard (and (natp* n) (natp* m))
                  :verify-guards nil))
  (if (or (not (natp* n)) (equal n 0))
      0
      (plus* m (mult* (cdr n) m))))

;;; Conversion functions to/from built-in naturals

; Convert built-in natural to our representation
(defun nat-to-nat* (n)
  (declare (xargs :guard (natp n)
                  :verify-guards nil))
  (if (zp n)
      0
      (S (nat-to-nat* (- n 1)))))

; Convert our representation to built-in natural
(defun nat*-to-nat (n)
  (declare (xargs :guard (natp* n)
                  :verify-guards nil))
  (if (or (not (natp* n)) (equal n 0))
      0
      (+ 1 (nat*-to-nat (cdr n)))))

;;; Theorems: SWF Chapter "Basics"

; Theorem plus_O_n: ∀ n, 0 + n = n
; Source: Software Foundations Basics.v, plus_O_n
(defthm plus*-O-n
  (implies (natp* n)
           (equal (plus* 0 n) n)))

; Theorem plus_1_l: ∀ n, 1 + n = S n
; Source: Software Foundations Basics.v, plus_1_l
(defthm plus*-1-l
  (implies (natp* n)
           (equal (plus* (S 0) n)
                  (S n))))

; Theorem mult_0_l: ∀ n, 0 * n = 0
; Source: Software Foundations Basics.v, mult_0_l
(defthm mult*-0-l
  (implies (natp* n)
           (equal (mult* 0 n) 0)))

; Theorem plus_id_exercise: ∀ n m, n = m → n + n = m + m
; Source: Software Foundations Basics.v, plus_id_exercise
(defthm plus*-id-exercise
  (implies (and (natp* n)
                (natp* m)
                (equal n m))
           (equal (plus* n n)
                  (plus* m m))))

;;; Theorems: SWF Chapter "Induction"

; Theorem plus_n_O: ∀ n, n + 0 = n
; Source: Software Foundations Induction.v, plus_n_O
(defthm plus*-n-O
  (implies (natp* n)
           (equal (plus* n 0) n)))

; Theorem mult_0_r: ∀ n, n * 0 = 0
; Source: Software Foundations Induction.v, mult_0_r
(defthm mult*-0-r
  (implies (natp* n)
           (equal (mult* n 0) 0)))

; Theorem plus_n_Sm: ∀ n m, S(n + m) = n + S(m)
; Source: Software Foundations Induction.v, plus_n_Sm
(defthm plus*-n-Sm
  (implies (and (natp* n)
                (natp* m))
           (equal (S (plus* n m))
                  (plus* n (S m)))))

; Theorem plus_comm: ∀ n m, n + m = m + n
; Source: Software Foundations Induction.v, plus_comm
(defthm plus*-comm
  (implies (and (natp* n)
                (natp* m))
           (equal (plus* n m)
                  (plus* m n))))

;;; Correctness theorems: our operations match built-in arithmetic

; Helper: natp* implies the conversion produces natp
(defthm nat*-to-nat-is-natp
  (implies (natp* n)
           (natp (nat*-to-nat n))))

; Helper: S produces valid natp*
(local
 (defthm s-preserves-natp*
   (implies (natp* n)
            (natp* (S n)))))

; Helper: S increments the natural number representation
(local
 (defthm nat*-to-nat-of-s
   (implies (natp* n)
            (equal (nat*-to-nat (S n))
                   (+ 1 (nat*-to-nat n))))))

; Helper: plus* produces valid natp*
(local
 (defthm plus*-preserves-natp*
   (implies (and (natp* n) (natp* m))
            (natp* (plus* n m)))
   :hints (("Goal" :in-theory (disable plus*-comm plus*-n-sm)))))

; Helper: nat-to-nat* produces valid natp*
(defthm nat-to-nat*-is-natp*
  (implies (natp n)
           (natp* (nat-to-nat* n))))

;;; Correctness theorems: linking cons-based nat* operations to built-in arithmetic

; Helper: conversion round-trip preserves values
(defthm nat*-to-nat-of-nat-to-nat*
  (implies (natp n)
           (equal (nat*-to-nat (nat-to-nat* n))
                  n)))

; NOTE: Additional correctness theorems that prove plus* and mult* correctly
; implement built-in ACL2 arithmetic are available in the companion file:
;   experiment-04-natural-numbers-correctness.lisp
;
; That file proves:
;  - plus*-preserves-natp*-global: plus* preserves the natp* type
;  - mult*-preserves-natp*-global: mult* preserves the natp* type
;  - nat*-to-nat-of-plus*: nat*-to-nat distributes over plus*
;  - plus*-correct: plus* correctly implements addition
;  - nat*-to-nat-of-mult*: nat*-to-nat distributes over mult*
;  - mult*-correct: mult* correctly implements multiplication
;
; These proofs require careful theory management (disabling the S constructor
; during rewriting) and are kept separate to maintain stability of this base file.
