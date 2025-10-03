; Basic induction theorems inspired by Software Foundations
; Source: https://softwarefoundations.cis.upenn.edu/lf-current/Induction.html
;
; These theorems parallel the Coq proofs in the Induction chapter,
; adapted for ACL2's natural number arithmetic.

(in-package "ACL2")

; Theorem add_0_r: ∀ n, n + 0 = n
; Source: Software Foundations Induction.v, add_0_r
; Note: We need to specify that n is a number in ACL2
(defthm add-0-r
  (implies (acl2-numberp n)
           (equal (+ n 0) n)))

; Theorem minus_n_n: ∀ n, n - n = 0
; Source: Software Foundations Induction.v, minus_n_n
(defthm minus-n-n
  (implies (acl2-numberp n)
           (equal (- n n) 0)))

; Theorem mul_0_r: ∀ n, n * 0 = 0
; Source: Software Foundations Induction.v, mul_0_r (exercise)
(defthm mul-0-r
  (implies (acl2-numberp n)
           (equal (* n 0) 0)))

; Theorem plus_n_Sm: ∀ n m, S(n + m) = n + S(m)
; Source: Software Foundations Induction.v, plus_n_Sm (exercise)
; In ACL2: (1+ (+ n m)) = (+ n (1+ m))
(defthm plus-n-sm
  (implies (and (acl2-numberp n)
                (acl2-numberp m))
           (equal (+ 1 (+ n m))
                  (+ n (+ 1 m)))))

; Theorem add_comm: ∀ n m, n + m = m + n
; Source: Software Foundations Induction.v, add_comm (exercise)
; This is already proved as addition-commutative in experiment-01,
; but included here for completeness with Software Foundations
(defthm add-comm-swf
  (implies (and (acl2-numberp n)
                (acl2-numberp m))
           (equal (+ n m)
                  (+ m n))))

; Theorem add_assoc: ∀ n m p, n + (m + p) = (n + m) + p
; Source: Software Foundations Induction.v, add_assoc
; Also already proved in experiment-01, included for completeness
(defthm add-assoc-swf
  (implies (and (acl2-numberp n)
                (acl2-numberp m)
                (acl2-numberp p))
           (equal (+ n (+ m p))
                  (+ (+ n m) p))))
