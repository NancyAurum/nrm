    AREA helloworld, CODE, READONLY

    ; NRM GET and INCLUDE RISC OS path format
    ; ../AsmHdrs/h/SWINames.s = ^.AsmHdrs.h.SWINames/s
    GET getswi/s

    ENTRY

    SWI OS_WriteS
    = "Hello, world!"
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