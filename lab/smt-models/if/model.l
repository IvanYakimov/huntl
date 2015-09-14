; // function parameter
(declare-var %x Int)
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
; store i32 %x, i32* %2, align 4
(assert (= %2 %x))
; %3 = load i32* %2, align 4
(assert (= %3 %2))
; %4 = icmp slt i32 %3, 0
; br i1 %4, label %5, label %6
; // if (x < 0)
(assert 
  (ite (< %3 0) 
    ; // return 1;
    (= %1 1)
    ; // return 0;
    (= %1 0))
)

; %8 = load i32* %1
(assert (= %8 %1))
(assert (= %ret %8))

; test-generation !!! :)
(push)
  (assert (< %3 0))
  (check-sat)
  (echo "P:")
  (get-value (%x))
  (get-value (%ret))
(pop)
(push)
  (assert (not (< %3 0)))
  (check-sat)
  (echo "~P:")
  (get-value (%x))
  (get-value (%ret))
(pop)
