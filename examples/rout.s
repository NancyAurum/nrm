       AREA helloworld, CODE, READONLY

       ENTRY
memset ROUT
       MOV R3,R0
10     SUBS R2,R2,#1
       STRGEB R1,[R3],#1
       BGT %BT10
       MOV PC,LR

memcpy ROUT
       MOV R3,R0
10     SUBS R2,R2,#1
       LDRGEB R12,[R1],#1
       STRGEB R12,[R3],#1
       BGT %BT10
       MOV PC,LR

       END
