OS_WriteS * &01
OS_NewLine * &03
OS_Exit * &11

    AREA helloworld, CODE, READONLY

    ENTRY

    GBLA counter
counter SETA 10
    WHILE counter > 0
      SWI OS_WriteS
      = "Hello, world!"
      DCB 0
      ALIGN
      SWI OS_NewLine
counter SETA counter-1
    WEND
    MOV R0,#0
    LDR R1,abex
    MOV R2,#0
    SWI OS_Exit
abex
    DCD &58454241 ; "ABEX"

    END