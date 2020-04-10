(module
    (func (export "main") (param $x i32) (result i32) (local $ret i32)
        (local.set $ret (i32.const 2))
        (block $outer
            (block
                (block
                    (i32.sub
                        (local.get $x)
                        (i32.const 88)
                    )
                    (br_table 0 1 2)
                )
                (local.set $ret (i32.const 0))
                (br $outer)
            )
            (local.set $ret (i32.const 1))
            (br $outer)
        )
        (local.get $ret)
    )
)
