(module
 (table 0 anyfunc)
 (memory $0 1)
 (export "memory" (memory $0))
 (export "collatz" (func $collatz))
 (export "main" (func $main))
 (func $collatz (; 0 ;) (param $0 i32) (result i32)
  (local $1 i32)
  (set_local $1
   (i32.const 0)
  )
  (block $label$0
   (br_if $label$0
    (i32.eq
     (get_local $0)
     (i32.const 1)
    )
   )
   (set_local $1
    (i32.const 0)
   )
   (loop $label$1
    (block $label$2
     (block $label$3
      (br_if $label$3
       (i32.and
        (get_local $0)
        (i32.const 1)
       )
      )
      (set_local $0
       (i32.div_s
        (get_local $0)
        (i32.const 2)
       )
      )
      (br $label$2)
     )
     (set_local $0
      (i32.add
       (i32.mul
        (get_local $0)
        (i32.const 3)
       )
       (i32.const 1)
      )
     )
    )
    (set_local $1
     (i32.add
      (get_local $1)
      (i32.const 1)
     )
    )
    (br_if $label$1
     (i32.ne
      (get_local $0)
      (i32.const 1)
     )
    )
   )
  )
  (get_local $1)
 )
 (func $main (; 1 ;) (result i32)
  (local $0 i32)
  (local $1 i32)
  (set_local $1
   (i32.const 0)
  )
  (set_local $0
   (i32.const 42)
  )
  (loop $label$0
   (block $label$1
    (block $label$2
     (br_if $label$2
      (i32.and
       (get_local $0)
       (i32.const 1)
      )
     )
     (set_local $0
      (i32.div_s
       (get_local $0)
       (i32.const 2)
      )
     )
     (br $label$1)
    )
    (set_local $0
     (i32.add
      (i32.mul
       (get_local $0)
       (i32.const 3)
      )
      (i32.const 1)
     )
    )
   )
   (set_local $1
    (i32.add
     (get_local $1)
     (i32.const 1)
    )
   )
   (br_if $label$0
    (i32.ne
     (get_local $0)
     (i32.const 1)
    )
   )
  )
  (get_local $1)
 )
)