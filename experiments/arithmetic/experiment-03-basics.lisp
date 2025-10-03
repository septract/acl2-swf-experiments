; Basic arithmetic theorems from Software Foundations Basics chapter
; Source: https://softwarefoundations.cis.upenn.edu/lf-current/Basics.html
;
; These theorems demonstrate fundamental properties of natural numbers
; and basic arithmetic operations.

(in-package "ACL2")

; Theorem plus_O_n: ∀ n, 0 + n = n
; Source: Software Foundations Basics.v, plus_O_n
; Left identity of addition
(defthm plus-0-n
  (implies (acl2-numberp n)
           (equal (+ 0 n) n)))

; Theorem plus_1_l: ∀ n, 1 + n = S n
; Source: Software Foundations Basics.v, plus_1_l
; Note: ACL2 doesn't have a separate successor function like Coq's S.
; The equivalent property in ACL2 is commutativity of addition with 1.
(defthm plus-1-l
  (implies (acl2-numberp n)
           (equal (+ 1 n) (+ n 1))))

; Theorem mult_0_l: ∀ n, 0 * n = 0
; Source: Software Foundations Basics.v, mult_0_l
; Left zero of multiplication
(defthm mult-0-l
  (implies (acl2-numberp n)
           (equal (* 0 n) 0)))

; Theorem mult_n_1: ∀ n, n * 1 = n
; Source: Software Foundations Basics.v, mult_n_1 (exercise)
; Right identity of multiplication
(defthm mult-n-1
  (implies (acl2-numberp n)
           (equal (* n 1) n)))

; Additional theorem: left identity of multiplication
(defthm mult-1-n
  (implies (acl2-numberp n)
           (equal (* 1 n) n)))

; Theorem: multiplication by 2
(defthm mult-2-n
  (implies (acl2-numberp n)
           (equal (* 2 n) (+ n n))))

; Theorem: commutativity of multiplication
(defthm mult-comm
  (implies (and (acl2-numberp n)
                (acl2-numberp m))
           (equal (* n m) (* m n))))

; Theorem: associativity of multiplication
(defthm mult-assoc
  (implies (and (acl2-numberp n)
                (acl2-numberp m)
                (acl2-numberp p))
           (equal (* n (* m p))
                  (* (* n m) p))))
