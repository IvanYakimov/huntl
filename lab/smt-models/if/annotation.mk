#original function:
int f (int x)
{
  if (x < 0)
    return 1;
  return 0;
}

; Function Attrs: nounwind uwtable
define i32 @f(i32 %x) #0 {
# // initialization
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  store i32 %x, i32* %2, align 4
# // if (x < 0)
  %3 = load i32* %2, align 4
  %4 = icmp slt i32 %3, 0
  br i1 %4, label %5, label %6

# // return 1;
; <label>:5                                       ; preds = %0
  store i32 1, i32* %1
  br label %7

# // return 0;
; <label>:6                                       ; preds = %0
  store i32 0, i32* %1
  br label %7

; <label>:7                                       ; preds = %6, %5
  g%8 = load i32* %1
  ret i32 %8
}
