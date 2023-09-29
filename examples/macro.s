OS_WriteS  * &01
OS_NewLine * &03
OS_Exit    * &11

    MACRO
$lbl  PRINTLN $text="No text specified"
$lbl  SWI OS_WriteS
      = "$text"
      DCB 0
      ALIGN
      SWI OS_NewLine
    MEND

    AREA helloworld, CODE, READONLY

    ENTRY

    PRINTLN "Hey, folks!"
    PRINTLN "This is a simple macro example."
    PRINTLN "Enjoy programming!"

    MOV R0,#0
    LDR R1,abex
    MOV R2,#0
    SWI OS_Exit
abex
    DCD &58454241 ; "ABEX"

    END