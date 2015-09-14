(declare-var %x Int)
(declare-var %y Int)
(declare-var %1 Int)
(declare-var %2 Int)
(declare-var %3 Int)
(declare-var %4 Int)
(declare-var %5 Int)
(declare-var %6 Int)
(declare-var %7 Int)
(declare-var %8 Int)
(declare-var %9 Int)
(declare-var %10 Int)
(declare-var %11 Int)
(declare-var %12 Int)

; %1 = alloca i32, align 4
; %2 = alloca i32, align 4
; %3 = alloca i32, align 4
(assert (= %1 0))
(assert (= %2 0))
(assert (= %3 0))

; store i32 %x, i32* %2, align 4
; store i32 %y, i32* %3, align 4
(assert (= %x %2))
(assert (= %y %3))

; %4 = load i32* %2, align 4
(assert (= %4 %2))
; %5 = icmp sgt i32 %4, 10
; br i1 %5, label %6, label %10
(assert 
	(ite (< %4 10)
    ; // true branch
		(
      
		; <label>:6 
		; %7 = load i32* %3, align 4
	  	; %8 = icmp slt i32 %7, 100
	  	; br i1 %8, label %9, label %10
			and 
      (= %7 %3)
      (ite (< %7 100)
				; label %9
				; store i32 1, i32* %1
        ; br label %11
				(= %1 1)
	  			
				; label %10
				; store i32 0, i32* %1
        ; br label %11
				(= %1 0)	  			
      )
		)
    ; // false branch
		; label %10
		; store i32 0, i32* %1
    ; br label %11
		(= %1 0)
	)
)

; <label>:11 
; %12 = load i32* %1
; ret i32 %12

(check-sat)

