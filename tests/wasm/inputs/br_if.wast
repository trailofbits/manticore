(module
    (func (export "main") (param $x i32) (result i32)
        (block (result i32)
            (i32.const 1)
            (i32.sub
                (local.get $x)
                (i32.const 88)
            )
            (br_if 0)
            (drop)
            (i32.const 0)
        )
    )
)