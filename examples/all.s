    MACRO
$lbl  PRINTLN $text="No text specified"
$lbl  SWI OS_WriteS
      = "$text"
      DCB 0
      ALIGN
      SWI OS_NewLine
    MEND

    ; NRM GET and INCLUDE expect RISC OS path format
    ; ../AsmHdrs/h/SWINames.s = ^.AsmHdrs.h.SWINames/s
    GET getswi/s

    AREA helloworld, CODE, READONLY

    ENTRY

    GBLA counter
counter SETA 10
    WHILE counter > 0
    PRINTLN "Hey, folks!"
    PRINTLN "This is a simple macro example."
    PRINTLN "Enjoy programming!"
counter SETA counter-1
    WEND
    MOV R0,#0
    LDR R1,abex
    MOV R2,#0
    SWI OS_Exit
abex
    DCD &58454241 ; "ABEX"

    END