;; Machine description for CORE-V vendor extensions.
;; Copyright (C) 2023 Free Software Foundation, Inc.

;; This file is part of GCC.

;; GCC is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; GCC is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GCC; see the file COPYING3.  If not see
;; <http://www.gnu.org/licenses/>.

(define_c_enum "unspec" [

  ;;CORE-V ALU
  UNSPEC_CV_ALU_CLIP
  UNSPEC_CV_ALU_CLIPR
  UNSPEC_CV_ALU_CLIPU
  UNSPEC_CV_ALU_CLIPUR

  ;; CORE-V HWLP
  UNSPEC_CV_LOOPBUG
  UNSPECV_CV_LOOPALIGN
  UNSPEC_CV_FOLLOWS
  UNSPEC_CV_LP_END_5
  UNSPEC_CV_LP_END_12

])

;; XCVMAC extension.

(define_insn "riscv_cv_mac_mac"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (plus:SI (mult:SI (match_operand:SI 1 "register_operand" "r")
                          (match_operand:SI 2 "register_operand" "r"))
                 (match_operand:SI 3 "register_operand" "0")))]

  "TARGET_XCVMAC && !TARGET_64BIT"
  "cv.mac\t%0,%1,%2"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_mac_msu"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (minus:SI (match_operand:SI 3 "register_operand" "0")
                  (mult:SI (match_operand:SI 1 "register_operand" "r")
                           (match_operand:SI 2 "register_operand" "r"))))]

  "TARGET_XCVMAC && !TARGET_64BIT"
  "cv.msu\t%0,%1,%2"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_mac_muluN"
  [(set (match_operand:SI 0 "register_operand" "=r")
    (lshiftrt:SI
      (mult:SI
        (zero_extend:SI
          (truncate:HI
            (match_operand:SI 1 "register_operand" "r")))
        (zero_extend:SI
          (truncate:HI
            (match_operand:SI 2 "register_operand" "r"))))
      (match_operand:QI 3 "const_csr_operand" "K")))]

  "TARGET_XCVMAC && !TARGET_64BIT"
  "cv.mulun\t%0,%1,%2,%3"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_mac_mulhhuN"
  [(set (match_operand:SI 0 "register_operand" "=r")
    (lshiftrt:SI
      (mult:SI
        (zero_extend:SI
          (truncate:HI
            (lshiftrt:SI (match_operand:SI 1 "register_operand" "r")
                         (const_int 16))))
        (zero_extend:SI
          (truncate:HI
            (lshiftrt:SI (match_operand:SI 2 "register_operand" "r")
                         (const_int 16)))))
      (match_operand:QI 3 "const_csr_operand" "K")))]

  "TARGET_XCVMAC && !TARGET_64BIT"
  "cv.mulhhun\t%0,%1,%2,%3"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_mac_mulsN"
  [(set (match_operand:SI 0 "register_operand" "=r")
    (ashiftrt:SI
      (mult:SI
        (sign_extend:SI
          (truncate:HI
            (match_operand:SI 1 "register_operand" "r")))
        (sign_extend:SI
          (truncate:HI
            (match_operand:SI 2 "register_operand" "r"))))
      (match_operand:QI 3 "const_csr_operand" "K")))]

  "TARGET_XCVMAC && !TARGET_64BIT"
  "cv.mulsn\t%0,%1,%2,%3"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_mac_mulhhsN"
  [(set (match_operand:SI 0 "register_operand" "=r")
    (ashiftrt:SI
      (mult:SI
        (sign_extend:SI
          (truncate:HI
            (lshiftrt:SI (match_operand:SI 1 "register_operand" "r")
                         (const_int 16))))
        (sign_extend:SI
          (truncate:HI
            (lshiftrt:SI (match_operand:SI 2 "register_operand" "r")
                         (const_int 16)))))
      (match_operand:QI 3 "const_csr_operand" "K")))]

  "TARGET_XCVMAC && !TARGET_64BIT"
  "cv.mulhhsn\t%0,%1,%2,%3"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_mac_muluRN"
  [(set (match_operand:SI 0 "register_operand" "=r")
    (lshiftrt:SI
      (fma:SI
        (zero_extend:SI
          (truncate:HI
            (match_operand:SI 1 "register_operand" "r")))
        (zero_extend:SI
          (truncate:HI
            (match_operand:SI 2 "register_operand" "r")))
        (if_then_else
          (ne:QI (match_operand:QI 3 "const_csr_operand" "K") (const_int 0))
          (ashift:SI (const_int 1)
            (minus:QI (match_dup 3)
                      (const_int 1)))
          (const_int 0)))
      (match_dup 3)))]

  "TARGET_XCVMAC && !TARGET_64BIT"
  "cv.mulurn\t%0,%1,%2,%3"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_mac_mulhhuRN"
  [(set (match_operand:SI 0 "register_operand" "=r")
    (lshiftrt:SI
      (fma:SI
        (zero_extend:SI
          (truncate:HI
            (lshiftrt:SI (match_operand:SI 1 "register_operand" "r")
                         (const_int 16))))
        (zero_extend:SI
          (truncate:HI
            (lshiftrt:SI (match_operand:SI 2 "register_operand" "r")
                         (const_int 16))))
        (if_then_else
          (ne:QI (match_operand:QI 3 "const_csr_operand" "K") (const_int 0))
          (ashift:SI (const_int 1)
            (minus:QI (match_dup 3)
                      (const_int 1)))
          (const_int 0)))
      (match_dup 3)))]

  "TARGET_XCVMAC && !TARGET_64BIT"
  "cv.mulhhurn\t%0,%1,%2,%3"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_mac_mulsRN"
  [(set (match_operand:SI 0 "register_operand" "=r")
    (ashiftrt:SI
      (fma:SI
        (sign_extend:SI
          (truncate:HI
            (match_operand:SI 1 "register_operand" "r")))
        (sign_extend:SI
          (truncate:HI
            (match_operand:SI 2 "register_operand" "r")))
        (if_then_else
          (ne:QI (match_operand:QI 3 "const_csr_operand" "K") (const_int 0))
          (ashift:SI (const_int 1)
                     (minus:QI (match_dup 3)
                               (const_int 1)))
          (const_int 0)))
      (match_dup 3)))]

  "TARGET_XCVMAC && !TARGET_64BIT"
  "cv.mulsrn\t%0,%1,%2,%3"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_mac_mulhhsRN"
  [(set (match_operand:SI 0 "register_operand" "=r")
    (ashiftrt:SI
      (fma:SI
        (sign_extend:SI
          (truncate:HI
            (lshiftrt:SI (match_operand:SI 1 "register_operand" "r")
                         (const_int 16))))
        (sign_extend:SI
          (truncate:HI
            (lshiftrt:SI (match_operand:SI 2 "register_operand" "r")
                         (const_int 16))))
        (if_then_else
          (ne:QI (match_operand:QI 3 "const_csr_operand" "K") (const_int 0))
          (ashift:SI (const_int 1)
                     (minus:QI (match_dup 3)
                               (const_int 1)))
          (const_int 0)))
      (match_dup 3)))]

  "TARGET_XCVMAC && !TARGET_64BIT"
  "cv.mulhhsrn\t%0,%1,%2,%3"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_mac_macuN"
  [(set (match_operand:SI 0 "register_operand" "=r")
    (lshiftrt:SI
      (fma:SI
        (zero_extend:SI
          (truncate:HI
            (match_operand:SI 1 "register_operand" "r")))
        (zero_extend:SI
          (truncate:HI
            (match_operand:SI 2 "register_operand" "r")))
        (match_operand:SI 3 "register_operand" "0"))
      (match_operand:QI 4 "const_csr_operand" "K")))]

  "TARGET_XCVMAC && !TARGET_64BIT"
  "cv.macun\t%0,%1,%2,%4"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_mac_machhuN"
  [(set (match_operand:SI 0 "register_operand" "=r")
    (lshiftrt:SI
      (fma:SI
        (zero_extend:SI
          (truncate:HI
            (lshiftrt:SI (match_operand:SI 1 "register_operand" "r")
                         (const_int 16))))
        (zero_extend:SI
          (truncate:HI
            (lshiftrt:SI (match_operand:SI 2 "register_operand" "r")
                         (const_int 16))))
        (match_operand:SI 3 "register_operand" "0"))
      (match_operand:QI 4 "const_csr_operand" "K")))]

  "TARGET_XCVMAC && !TARGET_64BIT"
  "cv.machhun\t%0,%1,%2,%4"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_mac_macsN"
  [(set (match_operand:SI 0 "register_operand" "=r")
    (ashiftrt:SI
      (fma:SI
        (sign_extend:SI
          (truncate:HI
            (match_operand:SI 1 "register_operand" "r")))
        (sign_extend:SI
          (truncate:HI
            (match_operand:SI 2 "register_operand" "r")))
        (match_operand:SI 3 "register_operand" "0"))
      (match_operand:QI 4 "const_csr_operand" "K")))]

  "TARGET_XCVMAC && !TARGET_64BIT"
  "cv.macsn\t%0,%1,%2,%4"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_mac_machhsN"
  [(set (match_operand:SI 0 "register_operand" "=r")
    (ashiftrt:SI
      (fma:SI
        (sign_extend:SI
          (truncate:HI
            (lshiftrt:SI (match_operand:SI 1 "register_operand" "r")
                         (const_int 16))))
        (sign_extend:SI
          (truncate:HI
            (lshiftrt:SI (match_operand:SI 2 "register_operand" "r")
                         (const_int 16))))
        (match_operand:SI 3 "register_operand" "0"))
      (match_operand:QI 4 "const_csr_operand" "K")))]

  "TARGET_XCVMAC && !TARGET_64BIT"
  "cv.machhsn\t%0,%1,%2,%4"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_mac_macuRN"
  [(set (match_operand:SI 0 "register_operand" "=r")
    (lshiftrt:SI
      (plus:SI
        (fma:SI
          (zero_extend:SI
            (truncate:HI
              (match_operand:SI 1 "register_operand" "r")))
          (zero_extend:SI
            (truncate:HI
              (match_operand:SI 2 "register_operand" "r")))
          (match_operand:SI 3 "register_operand" "0"))
        (if_then_else
          (ne:QI (match_operand:QI 4 "const_csr_operand" "K") (const_int 0))
          (ashift:SI (const_int 1)
                     (minus:QI (match_dup 4)
                               (const_int 1)))
          (const_int 0)))
      (match_dup 4)))]

  "TARGET_XCVMAC && !TARGET_64BIT"
  "cv.macurn\t%0,%1,%2,%4"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_mac_machhuRN"
  [(set (match_operand:SI 0 "register_operand" "=r")
    (lshiftrt:SI
      (plus:SI
        (fma:SI
          (zero_extend:SI
            (truncate:HI
              (lshiftrt:SI (match_operand:SI 1 "register_operand" "r")
                           (const_int 16))))
          (zero_extend:SI
            (truncate:HI
              (lshiftrt:SI (match_operand:SI 2 "register_operand" "r")
                           (const_int 16))))
          (match_operand:SI 3 "register_operand" "0"))
        (if_then_else
          (ne:QI (match_operand:QI 4 "const_csr_operand" "K") (const_int 0))
          (ashift:SI (const_int 1)
                     (minus:QI (match_dup 4)
                               (const_int 1)))
          (const_int 0)))
      (match_dup 4)))]

  "TARGET_XCVMAC && !TARGET_64BIT"
  "cv.machhurn\t%0,%1,%2,%4"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_mac_macsRN"
  [(set (match_operand:SI 0 "register_operand" "=r")
    (ashiftrt:SI
      (plus:SI
        (fma:SI
          (sign_extend:SI
            (truncate:HI
              (match_operand:SI 1 "register_operand" "r")))
          (sign_extend:SI
            (truncate:HI
              (match_operand:SI 2 "register_operand" "r")))
          (match_operand:SI 3 "register_operand" "0"))
        (if_then_else
          (ne:QI (match_operand:QI 4 "const_csr_operand" "K") (const_int 0))
          (ashift:SI (const_int 1)
                     (minus:QI (match_dup 4)
                               (const_int 1)))
          (const_int 0)))
      (match_dup 4)))]

  "TARGET_XCVMAC && !TARGET_64BIT"
  "cv.macsrn\t%0,%1,%2,%4"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_mac_machhsRN"
  [(set (match_operand:SI 0 "register_operand" "=r")
    (ashiftrt:SI
      (plus:SI
        (fma:SI
          (sign_extend:SI
            (truncate:HI
              (lshiftrt:SI (match_operand:SI 1 "register_operand" "r")
                           (const_int 16))))
          (sign_extend:SI
            (truncate:HI
              (lshiftrt:SI (match_operand:SI 2 "register_operand" "r")
                           (const_int 16))))
          (match_operand:SI 3 "register_operand" "0"))
        (if_then_else
          (ne:QI (match_operand:QI 4 "const_csr_operand" "K") (const_int 0))
          (ashift:SI (const_int 1)
                     (minus:QI (match_dup 4)
                               (const_int 1)))
          (const_int 0)))
      (match_dup 4)))]

  "TARGET_XCVMAC && !TARGET_64BIT"
  "cv.machhsrn\t%0,%1,%2,%4"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

;; XCVALU builtins

(define_insn "riscv_cv_alu_slet"
  [(set (match_operand:SI 0 "register_operand" "=r")
    (le:SI
      (match_operand:SI 1 "register_operand" "r")
      (match_operand:SI 2 "register_operand" "r")))]

  "TARGET_XCVALU && !TARGET_64BIT"
  "cv.sle\t%0, %1, %2"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_alu_sletu"
  [(set (match_operand:SI 0 "register_operand" "=r")
    (leu:SI
      (match_operand:SI 1 "register_operand" "r")
      (match_operand:SI 2 "register_operand" "r")))]

  "TARGET_XCVALU && !TARGET_64BIT"
  "cv.sleu\t%0, %1, %2"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_alu_min"
  [(set (match_operand:SI 0 "register_operand" "=r")
    (smin:SI
      (match_operand:SI 1 "register_operand" "r")
      (match_operand:SI 2 "register_operand" "r")))]

  "TARGET_XCVALU && !TARGET_64BIT"
  "cv.min\t%0, %1, %2"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_alu_minu"
  [(set (match_operand:SI 0 "register_operand" "=r")
    (umin:SI
      (match_operand:SI 1 "register_operand" "r")
      (match_operand:SI 2 "register_operand" "r")))]

  "TARGET_XCVALU && !TARGET_64BIT"
  "cv.minu\t%0, %1, %2"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_alu_max"
  [(set (match_operand:SI 0 "register_operand" "=r")
    (smax:SI
      (match_operand:SI 1 "register_operand" "r")
      (match_operand:SI 2 "register_operand" "r")))]

  "TARGET_XCVALU && !TARGET_64BIT"
  "cv.max\t%0, %1, %2"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_alu_maxu"
  [(set (match_operand:SI 0 "register_operand" "=r")
    (umax:SI
      (match_operand:SI 1 "register_operand" "r")
      (match_operand:SI 2 "register_operand" "r")))]

  "TARGET_XCVALU && !TARGET_64BIT"
  "cv.maxu\t%0, %1, %2"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_alu_exths"
  [(set (match_operand:SI 0 "register_operand" "=r")
   (sign_extend:SI
     (truncate:HI
       (match_operand:HI 1 "register_operand" "r"))))]

  "TARGET_XCVALU && !TARGET_64BIT"
  "cv.exths\t%0, %1"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_alu_exthz"
  [(set (match_operand:SI 0 "register_operand" "=r")
   (zero_extend:SI
     (truncate:HI
       (match_operand:HI 1 "register_operand" "r"))))]

  "TARGET_XCVALU && !TARGET_64BIT"
  "cv.exthz\t%0, %1"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_alu_extbs"
  [(set (match_operand:SI 0 "register_operand" "=r")
   (sign_extend:SI
     (truncate:QI
       (match_operand:QI 1 "register_operand" "r"))))]

  "TARGET_XCVALU && !TARGET_64BIT"
  "cv.extbs\t%0, %1"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_alu_extbz"
  [(set (match_operand:SI 0 "register_operand" "=r")
   (zero_extend:SI
     (truncate:QI
   (match_operand:QI 1 "register_operand" "r"))))]

  "TARGET_XCVALU && !TARGET_64BIT"
  "cv.extbz\t%0, %1"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_alu_clip"
  [(set (match_operand:SI 0 "register_operand" "=r,r")
   (unspec:SI [(match_operand:SI 1 "register_operand" "r,r")
               (match_operand:SI 2 "immediate_register_operand" "CVP2,r")]
    UNSPEC_CV_ALU_CLIP))]

  "TARGET_XCVALU && !TARGET_64BIT"
  "@
  cv.clip\t%0,%1,%X2
  cv.clipr\t%0,%1,%2"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_alu_clipu"
  [(set (match_operand:SI 0 "register_operand" "=r,r")
   (unspec:SI [(match_operand:SI 1 "register_operand" "r,r")
               (match_operand:SI 2 "immediate_register_operand" "CVP2,r")]
    UNSPEC_CV_ALU_CLIPU))]

  "TARGET_XCVALU && !TARGET_64BIT"
  "@
  cv.clipu\t%0,%1,%X2
  cv.clipur\t%0,%1,%2"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_alu_addN"
  [(set (match_operand:SI 0 "register_operand" "=r,r")
    (ashiftrt:SI
      (plus:SI
        (match_operand:SI 1 "register_operand" "r,0")
        (match_operand:SI 2 "register_operand" "r,r"))
      (and:SI (match_operand:QI 3 "csr_operand" "K,r")
              (const_int 31))))]

  "TARGET_XCVALU && !TARGET_64BIT"
  "@
  cv.addn\t%0,%1,%2,%3
  cv.addnr\t%0,%2,%3"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_alu_adduN"
  [(set (match_operand:SI 0 "register_operand" "=r,r")
    (lshiftrt:SI
      (plus:SI
        (match_operand:SI 1 "register_operand" "r,0")
        (match_operand:SI 2 "register_operand" "r,r"))
      (and:SI (match_operand:QI 3 "csr_operand" "K,r")
              (const_int 31))))]

  "TARGET_XCVALU && !TARGET_64BIT"
  "@
  cv.addun\t%0,%1,%2,%3
  cv.addunr\t%0,%2,%3"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_alu_addRN"
  [(set (match_operand:SI 0 "register_operand" "=r,r")
    (ashiftrt:SI
      (plus:SI
        (plus:SI
          (match_operand:SI 1 "register_operand" "r,0")
          (match_operand:SI 2 "register_operand" "r,r"))
        (if_then_else (eq (match_operand:QI 3 "csr_operand" "K,r")
                          (const_int 0))
          (const_int 1)
          (ashift:SI (const_int 1)
            (minus:QI (match_dup 3)
                      (const_int 1)))))
      (and:SI (match_dup 3)
              (const_int 31))))]

  "TARGET_XCVALU && !TARGET_64BIT"
  "@
  cv.addrn\t%0,%1,%2,%3
  cv.addrnr\t%0,%2,%3"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_alu_adduRN"
  [(set (match_operand:SI 0 "register_operand" "=r,r")
    (lshiftrt:SI
      (plus:SI
        (plus:SI
          (match_operand:SI 1 "register_operand" "r,0")
          (match_operand:SI 2 "register_operand" "r,r"))
        (if_then_else (eq (match_operand:QI 3 "csr_operand" "K,r")
                          (const_int 0))
          (const_int 1)
          (ashift:SI (const_int 1)
            (minus:QI (match_dup 3)
                      (const_int 1)))))
      (and:SI (match_dup 3)
              (const_int 31))))]

  "TARGET_XCVALU && !TARGET_64BIT"
  "@
  cv.addurn\t%0,%1,%2,%3
  cv.addurnr\t%0,%2,%3"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_alu_subN"
  [(set (match_operand:SI 0 "register_operand" "=r,r")
    (ashiftrt:SI
      (minus:SI
        (match_operand:SI 1 "register_operand" "r,0")
        (match_operand:SI 2 "register_operand" "r,r"))
      (and:SI (match_operand:QI 3 "csr_operand" "K,r")
              (const_int 31))))]

  "TARGET_XCVALU && !TARGET_64BIT"
  "@
  cv.subn\t%0,%1,%2,%3
  cv.subnr\t%0,%2,%3"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_alu_subuN"
  [(set (match_operand:SI 0 "register_operand" "=r,r")
    (lshiftrt:SI
      (minus:SI
        (match_operand:SI 1 "register_operand" "r,0")
        (match_operand:SI 2 "register_operand" "r,r"))
      (and:SI (match_operand:QI 3 "csr_operand" "K,r")
              (const_int 31))))]

  "TARGET_XCVALU && !TARGET_64BIT"
  "@
  cv.subun\t%0,%1,%2,%3
  cv.subunr\t%0,%2,%3"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_alu_subRN"
  [(set (match_operand:SI 0 "register_operand" "=r,r")
    (ashiftrt:SI
      (plus:SI
        (minus:SI
          (match_operand:SI 1 "register_operand" "r,0")
          (match_operand:SI 2 "register_operand" "r,r"))
        (if_then_else (eq (match_operand:QI 3 "csr_operand" "K,r")
                          (const_int 0))
          (const_int 1)
          (ashift:SI (const_int 1)
            (minus:QI (match_dup 3)
                      (const_int 1)))))
      (and:SI (match_dup 3)
              (const_int 31))))]

  "TARGET_XCVALU && !TARGET_64BIT"
  "@
  cv.subrn\t%0,%1,%2,%3
  cv.subrnr\t%0,%2,%3"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

(define_insn "riscv_cv_alu_subuRN"
  [(set (match_operand:SI 0 "register_operand" "=r,r")
    (lshiftrt:SI
      (plus:SI
        (minus:SI
          (match_operand:SI 1 "register_operand" "r,0")
          (match_operand:SI 2 "register_operand" "r,r"))
        (if_then_else (eq (match_operand:QI 3 "csr_operand" "K,r")
                          (const_int 0))
          (const_int 1)
          (ashift:SI (const_int 1)
            (minus:QI (match_dup 3)
                      (const_int 1)))))
      (and:SI (match_dup 3)
              (const_int 31))))]

  "TARGET_XCVALU && !TARGET_64BIT"
  "@
  cv.suburn\t%0,%1,%2,%3
  cv.suburnr\t%0,%2,%3"
  [(set_attr "type" "arith")
  (set_attr "mode" "SI")])

;; ??? The manual is unclear what the hardware loops actually do.
;; We are just guessing here.
(define_insn "doloop_end_i"
  [(set (pc)
	(if_then_else
	  (ne (match_operand:SI 0 "nonimmediate_operand" "+xcvl0c,xcvl1c")
	      (const_int 1))
	  (label_ref (match_operand 1 "" ""))
	  (pc)))
   (set (match_dup 0)
	(plus:SI (match_dup 0)
		 (const_int -1)))
   (use (match_operand:SI 2 "" "xcvl0s,xcvl1s"))
   (use (match_operand:SI 3 "" "xcvl0e,xcvl1e"))
   (use (match_operand:SI 4 "" "X,X"))]
  "TARGET_XCVHWLP"
{
  unsigned n_nops = 3;
  for (rtx_insn * curr = PREV_INSN (current_output_insn);
       curr && n_nops && !LABEL_P (curr);
       curr = PREV_INSN (curr))
    if (active_insn_p (curr))
      {
	n_nops--;
	if (recog_memoized (curr) == CODE_FOR_doloop_end_i)
	  break;
      }
  while (n_nops--)
    asm_fprintf (asm_out_file, "\tnop\n");
  output_asm_insn ("%4:", operands);
  if (TARGET_RVC)
    asm_fprintf (asm_out_file, "\t.option rvc\n");
  return "";
}
  [(set_attr "type" "branch")
   (set_attr "length" "0")]
)

(define_expand "doloop_end"
  [(match_operand:SI 0 "nonimmediate_operand" "")
   (match_operand 1 "" "")
   (match_operand 2 "" "")]
  "TARGET_XCVHWLP"
{
  if (GET_MODE (operands[0]) != SImode)
    FAIL;

  rtx_insn *start_label = as_a<rtx_insn *> (operands[1]);

  /* A HW loop must contain at least three insns.  If there are less than
     two insns in the loop, we must add two or more nops, which is worse
     than just using a normal loop with separate decrement and
     branch instructions.  */
  unsigned n_insns = 0;
  /* We must not set the counter register inside the loop, except for the
     increment that'll be folded into the doloop_end.  But that is already
    taken care of by loop_optimize, which creates a new register just for
    counting.  */

  /* If nesting HW loops, the inner loop must be using
     lpspart0, lpend0, lpcount0 .  It's OK if we have more than one inner
     loop, as long as they are not nested into each other; we have already
     checked the nesting depth in riscv_can_use_doloop_p.  */
  bool inner_loop_p = false;
  rtx_insn *bb_last = NULL;
  rtx_insn *bb_succ = NULL;
  for (rtx_insn *insn = start_label; ;
       insn = (insn == bb_last ? bb_succ : NEXT_INSN (insn)))
    {
      if (!insn)
	FAIL;

      /* For: int f (int i, int j) { while (--j) i = (i << 1) - 13; return i; }
	 we get passed a start label that's actually after the final branch.  */

      if (NOTE_INSN_BASIC_BLOCK_P (insn))
	{
	  basic_block bb = NOTE_BASIC_BLOCK (insn);
	  bb_last = BB_END (bb);
	  if (single_succ_p (bb))
	    bb_succ = BB_HEAD (single_succ (bb));
	  else if (recog_memoized (bb_last) == CODE_FOR_doloop_end_i)
	    bb_succ = BB_HEAD (FALLTHRU_EDGE (bb)->dest);
	  else if (bb_last == operands[2])
	    bb_succ = NULL;
	  else
	    FAIL;
	}

      if (NONJUMP_INSN_P (insn))
	n_insns++;
      else if (JUMP_P (insn))
	{
	  if (recog_memoized (insn) == CODE_FOR_doloop_end_i)
	    inner_loop_p = true;
	  else if (insn != operands[2])
	    FAIL;
	  else
	    break;
	}
    }
  /* We have counted in the counter decrement, so we need three insns for the
     cost of the HW loop to be amortized.  */
  if (n_insns < 3)
    FAIL;

  rtx start = gen_rtx_REG (SImode, LPSTART0_REGNUM + (inner_loop_p ? 3 : 0));
  rtx end = gen_rtx_REG (SImode, LPEND0_REGNUM + (inner_loop_p ?  3 : 0));
  rtx ref = gen_rtx_LABEL_REF (SImode, gen_label_rtx ());
  rtx_insn *jump
    = emit_jump_insn (gen_doloop_end_i (operands[0], operands[1],
					start, end, ref));
  add_label_op_ref (jump, ref);
  DONE;
})

;; Although the alignment can be thought of taking up to two bytes, that is
;; only the case if the assembler first saved space by creating a short insn.
;; The compiler doesn't generally take short insn into account when calculating
;; lengths.
(define_insn "doloop_align"
  [(unspec_volatile [(const_int 0)] UNSPECV_CV_LOOPALIGN)]
  "TARGET_XCVHWLP && TARGET_RVC"
  ".balign\t4\;.option norvc"
  [(set_attr "type" "ghost")])

;; Sometimes - e.g. newlib/libc/stdlib/src4random.c 
;; -Os  -march=rv32imc_zicsr_xcvhwlp - we have spagetti code at split2, with
;; the loop setup below the loop, and it's still spaghetti at peephole2, but
;; it gets sorted out at bbro.  Should we delay the doloop_begin_i split
;; until after bbro, and add another split pass - or always drive the split
;; with a '#' output pattern, to avoid this issue?

(define_insn_and_split "doloop_begin_i"
  [(set (match_operand:SI 0 "lpstart_reg_op")
	(match_operand:SI 1))
   (set (match_operand:SI 2 "lpend_reg_op")
	(match_operand:SI 3))
   (set (match_operand:SI 4 "register_operand")
	(match_operand:SI 5 "immediate_register_operand"))
   (clobber (match_scratch:SI 6))]
  "TARGET_XCVHWLP"
  {@ [cons: =0, 1, =2, 3, =4, 5, =6; attrs: length ]
    [xcvl0s, CVl0, xcvl0e, xcvlb5, xcvl0c, CV12, X ; 4] cv.setupi\t0, %5, %3
    [xcvl1s, CVl0, xcvl1e, xcvlb5, xcvl1c, CV12, X ; 4] cv.setupi\t1, %5, %3
    [xcvl0s, CVl0, xcvl0e, xcvlbe, xcvl0c, r,    X ; 4] cv.setup\t0, %5, %3
    [xcvl1s, CVl0, xcvl1e, xcvlbe, xcvl1c, r,    X ; 4] cv.setup\t1, %5, %3
    [xcvl0s,?iCVl0,xcvl0e,?ixcvlbe,xcvl0c, ?ri, &r ; 12] #
    [xcvl1s,?iCVl0,xcvl1e,?ixcvlbe,xcvl1c, ?ri, &r ; 12] #
  }
  ;; We don't know the loop length until after register allocation.
  ;; Even in the cases where we already can know before reload that we must
  ;; split, the test is costly, and splitting early could confuse RA.
  "&& reload_completed
   && (GET_CODE (operands[1]) == LABEL_REF
       || GET_CODE (operands[1]) == UNSPEC)
   && !hwloop_setupi_p (insn, operands[1], operands[3])"
  [(set (match_dup 4) (match_dup 5))]
{
  if (GET_CODE (operands[1]) == UNSPEC)
    operands[1] = XVECEXP (operands[1], 0, 0);
  else
    {
      emit_move_insn (operands[6], operands[1]);
      operands[1] = operands[6];
    }
  emit_insn (gen_rtx_SET (operands[0], operands[1]));
  if (GET_CODE (operands[3]) == UNSPEC)
    operands[3] = XVECEXP (operands[3], 0, 0);
  else
    {
      emit_move_insn (operands[6], operands[3]);
      operands[3] = operands[6];
    }
  emit_insn (gen_rtx_SET (operands[2], operands[3]));
  if (!satisfies_constraint_CV12 (operands[5]))
    {
      emit_move_insn (operands[6], operands[5]);
      operands[5] = operands[6];
    }
}
  [(set_attr "move_type" "move")]
)

(define_expand "doloop_begin"
  [(use (match_operand 0 "register_operand"))
   (use (match_operand 1 ""))]
  "TARGET_XCVHWLP"
{
  rtx pat = PATTERN (operands[1]);
  /* ??? cleanup_cfg, called from pass_rtl_loop_done::execute, deletes
     loop latches without updating LABEL_REFS in non-jump instructions
     even when marked with marked with REG_LABEL_OPEREND notes.  */
#if 0
  rtx start_label_ref
    = XEXP (SET_SRC (XVECEXP (pat, 0, 0)), 1);
#else
  rtx lst = gen_rtx_INSN_LIST (VOIDmode, operands[1], NULL_RTX);
  rtx start_label_ref
    = gen_rtx_UNSPEC (SImode, gen_rtvec (1, lst), UNSPEC_CV_LOOPBUG);
#endif
  rtx start_reg = XEXP (XVECEXP (pat, 0, 2), 0);
  rtx end_reg = XEXP (XVECEXP (pat, 0, 3), 0);
  rtx end_label_ref = XEXP (XVECEXP (pat, 0, 4), 0);
  rtx_insn *insn = emit_insn (gen_doloop_begin_i (start_reg, start_label_ref,
						  end_reg, end_label_ref,
						  operands[0], operands[0]));
  //add_label_op_ref (insn, start_label_ref);
  add_label_op_ref (insn, end_label_ref);
  DONE;
})

;; Although cv.start / cv.end / cv.count could be seen as move instructions
;; and therefore belonging to movsi_internal, that is problematic because
;; using them outside loopsetup contexts might confuse the HW loop logic
;; of the processor.  We might model this with UNSPEC_VOLATILEs, but
;; that'd likely get too much into the way of optimizations.
(define_insn "*cv_start"
  [(set (match_operand:SI 0 "lpstart_reg_op" "=xcvl0s,xcvl1s,xcvl0s,xcvl1s")
	(match_operand:SI 1 "label_register_operand" "i,i,r,r"))]
  "TARGET_XCVHWLP"
{
  if (!REG_P (operands[1]) && TARGET_RVC)
    asm_fprintf (asm_out_file, "\t.balign\t4\n");
  operands[0] = GEN_INT (REGNO (operands[0]) == LPSTART0_REGNUM ? 0 : 1);
  return REG_P (operands[1]) ? "cv.start %0,%1" : "cv.starti %0, %1";
}
  [(set_attr "move_type" "move")])

(define_insn "*cv_end"
  [(set (match_operand:SI 0 "lpend_reg_op" "=xcvl0e,xcvl1e,xcvl0e,xcvl1e")
	(match_operand:SI 1 "label_register_operand" "i,i,r,r"))]
  "TARGET_XCVHWLP"
{
  if (!REG_P (operands[1]) && TARGET_RVC)
    asm_fprintf (asm_out_file, "\t.balign\t4\n");
  operands[0] = GEN_INT (REGNO (operands[0]) == LPEND0_REGNUM ? 0 : 1);
  return REG_P (operands[1]) ? "cv.end %0,%1" : "cv.endi %0, %1";
}
  [(set_attr "move_type" "move")])

(define_insn "*cv_count"
  [(set (match_operand:SI 0 "lpcount_reg_op" "=xcvl0c,xcvl1c,xcvl0c,xcvl1c")
	(match_operand:SI 1 "immediate_register_operand" "CV12,CV12,r,r"))]
  "TARGET_XCVHWLP"
{
  operands[0] = GEN_INT (REGNO (operands[0]) == LPCOUNT0_REGNUM ? 0 : 1);
  return REG_P (operands[1]) ? "cv.count %0,%1" : "cv.counti %0, %1";
}
  [(set_attr "move_type" "move")])
