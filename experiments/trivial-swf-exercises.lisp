(in-package "ACL2")

;; =============================================================================
;; Trivial SWF Exercises - Proved Automatically by ACL2
;; =============================================================================
;;
;; This file contains SWF exercises that are marked as challenging (3-4 stars)
;; in Software Foundations but turn out to be trivial in ACL2 due to its
;; powerful automation.
;;
;; These exercises are pedagogically valuable in SWF because students build
;; reasoning from first principles. However, in ACL2, the built-in automation
;; (arithmetic reasoning, induction schemes, rewriting) handles them immediately.
;;
;; Purpose: Document that these SWF exercises were attempted and proved trivial,
;; so we don't waste time on them as "challenges" but can reference them as
;; examples of ACL2's automation power.
;;
;; =============================================================================

;; =============================================================================
;; BAG (MULTISET) OPERATIONS - All proved automatically (★☆☆☆ TRIVIAL)
;; =============================================================================
;; Source: Software Foundations, Lists chapter
;; SWF stars: 3 stars (advanced)
;; ACL2 difficulty: Trivial - all proofs automatic, no hints needed

(defun bag-count (v bag)
  "Count occurrences of v in bag (list of natural numbers)"
  (declare (xargs :guard (and (natp v) (nat-listp bag))))
  (cond ((endp bag) 0)
        ((equal v (car bag))
         (+ 1 (bag-count v (cdr bag))))
        (t (bag-count v (cdr bag)))))

(defun bag-remove (v bag)
  "Remove one occurrence of v from bag"
  (declare (xargs :guard (and (natp v) (nat-listp bag))))
  (cond ((endp bag) nil)
        ((equal v (car bag)) (cdr bag))
        (t (cons (car bag) (bag-remove v (cdr bag))))))

(defun bag-sum (bag1 bag2)
  "Union of two bags (concatenation)"
  (declare (xargs :guard (and (nat-listp bag1) (nat-listp bag2))))
  (append bag1 bag2))

;; ✓ SWF: remove_does_not_increase_count (★☆☆☆ TRIVIAL - proved automatically)
(defthm remove-does-not-increase-count
  (implies (and (natp v) (nat-listp bag))
           (<= (bag-count v (bag-remove v bag))
               (bag-count v bag))))

;; ⚠ ADAPTED: SWF has open-ended "bag_count_sum" exercise (★☆☆☆ TRIVIAL - proved automatically)
;; This specific formulation (count distributes over sum) is reasonable
(defthm bag-count-sum
  (implies (and (natp v) (nat-listp bag1) (nat-listp bag2))
           (equal (bag-count v (bag-sum bag1 bag2))
                  (+ (bag-count v bag1)
                     (bag-count v bag2)))))

;; ✗ INVENTED [FALSE]: Original version was false! (★☆☆☆ TRIVIAL - conditional proved automatically)
;; The original theorem (removing from both bags independently) is FALSE
;; because bag-remove only removes ONE occurrence. The correct theorem requires
;; that v is not in the first bag.
(defthm bag-remove-sum-when-not-in-first
  (implies (and (natp v)
                (nat-listp bag1)
                (nat-listp bag2)
                (equal (bag-count v bag1) 0))
           (equal (bag-remove v (bag-sum bag1 bag2))
                  (bag-sum bag1 (bag-remove v bag2)))))


;; =============================================================================
;; LIST INTERLEAVING - All proved automatically (★☆☆☆ TRIVIAL)
;; =============================================================================
;; Source: Software Foundations, Lists chapter
;; SWF: Only asks to implement, no theorems requested
;; ACL2 difficulty: Trivial - all proofs automatic

(defun alternate (l1 l2)
  "Interleave two lists, alternating elements"
  (declare (xargs :guard (and (true-listp l1) (true-listp l2))))
  (cond ((endp l1) l2)
        ((endp l2) l1)
        (t (cons (car l1)
                 (cons (car l2)
                       (alternate (cdr l1) (cdr l2)))))))

;; ✗ INVENTED: Useful property about length (★☆☆☆ TRIVIAL - proved automatically)
(defthm alternate-length
  (implies (and (true-listp l1) (true-listp l2))
           (equal (len (alternate l1 l2))
                  (+ (len l1) (len l2)))))

;; ✗ INVENTED: Identity properties (★☆☆☆ TRIVIAL - proved automatically)
(defthm alternate-nil-l
  (implies (true-listp l)
           (equal (alternate nil l) l)))

(defthm alternate-nil-r
  (implies (true-listp l)
           (equal (alternate l nil) l)))

;; ✗ INVENTED [FALSE]: This theorem is actually FALSE!
;; alternate is not symmetric:
;;   (alternate '(1 2) '(3 4)) = '(1 3 2 4)
;;   (alternate '(3 4) '(1 2)) = '(3 1 4 2)
;; Attempting to prove this revealed it's false - good example of proof catching errors!


;; =============================================================================
;; SUMMARY
;; =============================================================================
;;
;; All theorems in this file were proved automatically by ACL2 with ZERO hints.
;;
;; Why these are trivial in ACL2 but hard in SWF:
;; 1. SWF builds reasoning from scratch (students learn induction, case analysis)
;; 2. ACL2 has powerful built-in automation for:
;;    - Arithmetic reasoning
;;    - Automatic induction scheme selection
;;    - Rewriting with previously proved lemmas
;;    - List reasoning
;;
;; Educational value:
;; - Shows power of ACL2 automation
;; - Demonstrates gap between pedagogical exercises and real proof challenges
;; - Found 2 false theorems that seemed plausible (formal proofs caught them!)
;;
;; For real ACL2 challenges, see: experiments/challenge-problems.lisp
;; (Binary numbers with custom types, function injectivity proofs)
