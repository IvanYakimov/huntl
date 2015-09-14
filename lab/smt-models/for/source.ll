; ModuleID = 'source.c'
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

; Function Attrs: nounwind uwtable
define i32 @factorial(i32 %n) #0 {
  %1 = alloca i32, align 4
  %c = alloca i32, align 4
  %fact = alloca i32, align 4
  store i32 %n, i32* %1, align 4
  store i32 1, i32* %fact, align 4
  store i32 1, i32* %c, align 4
  br label %2

; <label>:2                                       ; preds = %10, %0
  %3 = load i32* %c, align 4
  %4 = load i32* %1, align 4
  %5 = icmp sle i32 %3, %4
  br i1 %5, label %6, label %13

; <label>:6                                       ; preds = %2
  %7 = load i32* %fact, align 4
  %8 = load i32* %c, align 4
  %9 = mul nsw i32 %7, %8
  store i32 %9, i32* %fact, align 4
  br label %10

; <label>:10                                      ; preds = %6
  %11 = load i32* %c, align 4
  %12 = add nsw i32 %11, 1
  store i32 %12, i32* %c, align 4
  br label %2

; <label>:13                                      ; preds = %2
  %14 = load i32* %fact, align 4
  ret i32 %14
}

attributes #0 = { nounwind uwtable "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.ident = !{!0}

!0 = metadata !{metadata !"Debian clang version 3.5.0-10 (tags/RELEASE_350/final) (based on LLVM 3.5.0)"}
