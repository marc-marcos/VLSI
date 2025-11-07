# Laboratory 4 VLSI

The verification process will consist in directed tests for edge cases of every operation and an arbitrary number of random tests. In this design the input space is limited enough that we could exhaustively test all combinations of operands and operations (31\*31\*7=6727 different tests) but I'll discard this option considering it ad hoc.

This is the table with the directed tests:

| Operation           | Test                  | Test number    |
|--------------------|----------------------|----------------|
| All operations     | 0 operands           | 1              |
| All operations     | max operands         | 2              |
| ADD                | smallest with carry  | 3              |
| ADD                | biggest with carry   | 4              |
| SUB                | smallest with borrow | 5              |
| SUB                | biggest with borrow  | 6              |
| Logical operations | complementary bits   | 7              |

There aren't directed tests for invalid operation values because all operation bits are valid per the spec.

The random tests will have randomized inputs for the operands (0000 to 1111) and for the operation (000 to 111).
