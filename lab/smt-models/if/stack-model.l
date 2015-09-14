; // stack declaration
(declare-var stack (Array Int Int))
; // function parameter
(declare-var %x Int)
; // retval
(declare-var %ret Int)
; // temporary variables
(declare-var %1 Int)
(declare-var %2 Int)
(declare-var %3 Int)
(declare-var %4 Int)
(declare-var %5 Int)
(declare-var %6 Int)
(declare-var %7 Int)
(declare-var %8 Int)

; // memory allocation
;  %1 = alloca i32, align 4
(assert (= (store stack %1 0) stack))
;  %2 = alloca i32, align 4
; NEXT LINE MADE MODEL UNSATISFIABLE:
;(assert (= (store stack %2 0) stack))

; store i32 %x, i32* %2, align 4
(assert (= (store stack %2 %x) stack))
; %3 = load i32* %2, align 4
(assert (= (select stack %2) %3))

(assert (< %3 0))
(check-sat)
