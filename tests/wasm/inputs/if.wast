(module
    (func (export "main") (param $x i32) (result i32)
        (if (result i32)
            (i32.sub
                (local.get $x)
                (i32.const 88)
            )
            (then
                (i32.const 1)
            )
            (else
                (i32.const 0)
            )
        )
    )
)
