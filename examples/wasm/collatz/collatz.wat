(module
 (type $FUNCSIG$i (func (result i32)))
 (type $FUNCSIG$ii (func (param i32) (result i32)))
 (import "env" "getchar" (func $getchar (param i32) (result i32)))
 (table 0 anyfunc)
 (memory $0 1)
 (data (i32.const 16) ">\00")
 (export "memory" (memory $0))
 (export "collatz" (func $collatz))
 (export "main" (func $main))
 (func $collatz (; 1 ;) (param $0 i32) (result i32)
  (local $1 i32)
  (set_local $1
   (i32.const 0)
  )
  (block $label$0
   (br_if $label$0
    (i32.lt_s
     (get_local $0)
     (i32.const 2)
    )
   )
   (set_local $1
    (i32.const 0)
   )
   (loop $label$1
    (set_local $1
     (i32.add
      (get_local $1)
      (i32.const 1)
     )
    )
    (br_if $label$1
     (i32.gt_s
      (tee_local $0
       (select
        (i32.add
         (i32.mul
          (get_local $0)
          (i32.const 3)
         )
         (i32.const 1)
        )
        (i32.shr_u
         (get_local $0)
         (i32.const 1)
        )
        (i32.and
         (get_local $0)
         (i32.const 1)
        )
       )
      )
      (i32.const 1)
     )
    )
   )
  )
  (get_local $1)
 )
 (func $main (; 2 ;) (result i32)
  (local $0 i32)
  (local $1 i32)
  (set_local $1
   (i32.const 0)
  )
  (block $label$0
   (br_if $label$0
    (i32.lt_s
     (tee_local $0
      (call $getchar
       (i32.const 16)
      )
     )
     (i32.const 2)
    )
   )
   (set_local $1
    (i32.const 0)
   )
   (loop $label$1
    (set_local $1
     (i32.add
      (get_local $1)
      (i32.const 1)
     )
    )
    (br_if $label$1
     (i32.gt_s
      (tee_local $0
       (select
        (i32.add
         (i32.mul
          (get_local $0)
          (i32.const 3)
         )
         (i32.const 1)
        )
        (i32.shr_u
         (get_local $0)
         (i32.const 1)
        )
        (i32.and
         (get_local $0)
         (i32.const 1)
        )
       )
      )
      (i32.const 1)
     )
    )
   )
  )
  (get_local $1)
 )
)