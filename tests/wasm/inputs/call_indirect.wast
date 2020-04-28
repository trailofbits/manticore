(module
    (table funcref (elem $const_zero $const_one))
    (type $no_in_one_out (func (result i32)))

    (func $const_zero (result i32)
        (i32.const 0))

    (func $const_one (result i32)
        (i32.const 1))

    (func (export "main") (param $x i32) (result i32)
        (i32.sub
            (local.get $x)
            (i32.const 88)
        )
        (call_indirect (type $no_in_one_out))
    )
)
