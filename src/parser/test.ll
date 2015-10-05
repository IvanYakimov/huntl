; ModuleID = 'test.c'
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

; Function Attrs: nounwind uwtable
define i32 @f(i32 %a, i32 %b) #0 {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  store i32 %a, i32* %1, align 4
  store i32 %b, i32* %2, align 4
  %3 = load i32* %1, align 4
  %4 = load i32* %2, align 4
  %5 = sdiv i32 %4, 2
  %6 = add nsw i32 %3, %5
  ret i32 %6
}

; Function Attrs: nounwind uwtable
define i32 @g(i32 %x) #0 {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  store i32 %x, i32* %2, align 4
  %3 = load i32* %2, align 4
  %4 = icmp slt i32 %3, 0
  br i1 %4, label %5, label %6

; <label>:5                                       ; preds = %0
  store i32 -1, i32* %1
  br label %7

; <label>:6                                       ; preds = %0
  store i32 1, i32* %1
  br label %7

; <label>:7                                       ; preds = %6, %5
  %8 = load i32* %1
  ret i32 %8
}

; Function Attrs: nounwind uwtable
define i32 @main() #0 {
  %1 = call i32 @f(i32 1, i32 2)
  %2 = call i32 @g(i32 100)
  ret i32 0
}

attributes #0 = { nounwind uwtable "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.ident = !{!0}

!0 = metadata !{metadata !"Debian clang version 3.5.0-10 (tags/RELEASE_350/final) (based on LLVM 3.5.0)"}
