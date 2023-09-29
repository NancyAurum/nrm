OS_WriteS * &01
OS_NewLine * &03
OS_Exit * &11

    AREA helloworld, CODE, READONLY

    ENTRY

    SWI OS_WriteS
    [ {FALSE}
      = "Hello, world!"
    | 
      = "Hi there!"
    ]
    DCB 0
    ALIGN
    SWI OS_NewLine
    MOV R0,#0
    LDR R1,abex
    MOV R2,#0
    SWI OS_Exit
abex
    DCD &58454241 ; "ABEX"

    END