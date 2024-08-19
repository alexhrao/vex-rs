#### BEGIN BASIC BLOCK ####
        c0    ldw $r0.2 = 0x24[$r0.1]  ## restore ## t16
;;
;;
;;                                                              ## 67
        c0    ldw $r0.4 = 0x28[$r0.1]  ## restore ## t20
;;
;;
;;                                                              ## 68
        c0    ldw $r0.6 = 0x20[$r0.1]  ## restore ## t12
;;
;;
;;                                                              ## 69
        c0    ldw $r0.7 = 0x2c[$r0.1]  ## restore ## t24
;;
;;
;;                                                              ## 70
        c0    mpylu $r0.8 = $r0.2, $r0.5   ## bblock 10, line 19,  t109,  t16,  t20
;;
;;                                                              ## 71
        c0    mpyhs $r0.9 = $r0.2, $r0.5   ## bblock 10, line 19,  t110,  t16,  t20
;;
;;                                                              ## 72
        c0    add $r0.7 = $r0.6, $r0.7   ## bblock 10, line 21,  t107,  t12,  t24
;;                                                              ## 73
        c0    add $r0.8 = $r0.8, $r0.9   ## bblock 10, line 19,  t53,  t109,  t110
;;                                                              ## 74
        c0    add $r0.8 = $r0.8, $r0.7   ## bblock 10, line 21,  t113,  t53,  t107
;;                                                              ## 75
        c0    ldw $r0.9 = 0x1c[$r0.1]  ## restore ## t8
;;
;;
;;                                                              ## 76
        c0    add $r0.7 = $r0.2, $r0.7   ## bblock 10, line 17,  t108,  t16,  t107
;;                                                              ## 77
        c0    ldw $r0.10 = 0x18[$r0.1]  ## restore ## t4
;;
;;
;;                                                              ## 78
        c0    mpylu $r0.11 = $r0.9, $r0.6   ## bblock 10, line 20,  t111,  t8,  t12
;;
;;                                                              ## 79
        c0    mpyhs $r0.6 = $r0.9, $r0.6   ## bblock 10, line 20,  t112,  t8,  t12
;;
;;                                                              ## 80
        c0    add $r0.10 = $r0.10, $r0.7   ## bblock 10, line 23,  t114,  t4,  t108
;;                                                              ## 81
        c0    add $r0.11 = $r0.11, $r0.6   ## bblock 10, line 20,  t58,  t111,  t112
;;                                                              ## 82
        c0    add $r0.8 = $r0.8, $r0.11   ## bblock 10, line 21,  t106,  t113,  t58
;;                                                              ## 83
        c0    add $r0.2 = $r0.2, $r0.8   ## bblock 10, line 23,  t116,  t16,  t106
;;                                                              ## 84
        c0    add $r0.5 = $r0.5, $r0.8   ## bblock 10, line 23,  t117,  t20,  t106
;;                                                              ## 85
        c0    add $r0.2 = $r0.2, $r0.5   ## bblock 10, line 23,  t122,  t116,  t117
;;                                                              ## 86
        c0    ldw $r0.5 = 0x30[$r0.1]  ## restore ## t32
;;
;;
;;                                                              ## 87
        c0    add $r0.9 = $r0.9, $r0.7   ## bblock 10, line 23,  t115,  t8,  t108
;;                                                              ## 88
;;                                                              ## 89
        c0    add $r0.6 = $r0.5, $r0.3   ## bblock 10, line 23,  t119,  t32,  t36
;;                                                              ## 90
        c0    add $r0.10 = $r0.10, $r0.6   ## bblock 10, line 23,  t120,  t114,  t119
;;                                                              ## 91
        c0    add $r0.10 = $r0.10, $r0.2   ## bblock 10, line 23,  t123,  t120,  t122
;;                                                              ## 92
        c0    add $r0.5 = $r0.5, $r0.3   ## bblock 10, line 23,  t118,  t32,  t36
;;                                                              ## 93
        c0    add $r0.9 = $r0.9, $r0.5   ## bblock 10, line 23,  t121,  t115,  t118
;;                                                              ## 94
;;                                                              ## 95
        c0    mov $r0.3 = (_?1STRINGPACKET.1 + 0)   ## addr(_?1STRINGVAR.1)(P32)
;;                                                              ## 96
#### END BASIC BLOCK ####