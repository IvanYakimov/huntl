; ModuleID = 'source.c'
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

; Function Attrs: nounwind uwtable
define i32 @f(i32 %x, i32 %y) #0 {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  %3 = alloca i32, align 4
  store i32 %x, i32* %2, align 4
  store i32 %y, i32* %3, align 4
  %4 = load i32* %2, align 4
  %5 = icmp sgt i32 %4, 10
  br i1 %5, label %6, label %10

; <label>:6                                       ; preds = %0
  %7 = load i32* %3, align 4
  %8 = icmp slt i32 %7, 100
  br i1 %8, label %9, label %10

; <label>:9                                       ; preds = %6
  store i32 1, i32* %1
  br label %11

; <label>:10                                      ; preds = %6, %0
  store i32 0, i32* %1
  br label %11

; <label>:11                                      ; preds = %10, %9
  %12 = load i32* %1
  ret i32 %12
}

attributes #0 = { nounwind uwtable "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.ident = !{!0}

!0 = metadata !{metadata !"Debian clang version 3.5.0-10 (tags/RELEASE_350/final) (based on LLVM 3.5.0)"}
