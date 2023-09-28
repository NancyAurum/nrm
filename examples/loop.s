OS_WriteS  * &01
OS_NewLine * &03
OS_Exit    * &11

    AREA helloworld, CODE, READONLY

    ENTRY
again
    SWI OS_WriteS
    = "Hello, world!"
    DCB 0
    ALIGN
    SWI OS_NewLine
    b again

    END

