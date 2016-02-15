;; https://www.lri.fr/~melquion/doc/13-ifm-article.pdf, page 4
;; run: ./parsyn-cegis.py benchmarks/water-s4-safe.smt2 "INV_L INV_U" -K 20
;; expected result: SAFE
(declare-datatypes () ((location ON OFF SWON SWOFF)))
(declare-datatypes () ((state (mk-state (loc location) (x Int) (y Real)))))
(declare-datatypes () ((input (mk-input (err Int)))))

(define-fun LOW () Real 1.0)
(define-fun HIGH () Real 10.0)
(define-fun MIN () Real 1.0)
(define-fun MAX () Real 10.0)
(define-fun RATE_IN () Real 0.01)
(define-fun RATE_OUT () Real 0.01)
(define-fun DELAY () Int  5)

;; value V in [1,10] are SAFE and otherwise UNSAFE
(define-fun INV_L () Real 1.0)
(define-fun INV_U () Real 10.0)

;; Init(s) ---> Bool
(define-fun init ((s state)) Bool
  (and
    (= (x s) 0) (= (y s) LOW)
  )
)

;; Safe(s) ---> Bool
(define-fun safe ((s state)) Bool
  (and (>= (y s) MIN) (<= (y s) MAX))
)

;;; Inv(s) ---> Bool
(define-fun inv ((s state)) Bool
  (and (>= (y s) INV_L) (<= (y s) INV_U))
)

;; T(s,i) ---> s
(define-fun tau ((s state) (i input)) state
  (let ((new_x
    (ite (= (loc s) SWOFF) (+ (x s) 1)
    (ite (= (loc s) SWON)  (+ (x s) 1)
    (x s)))
  ))
  (let ((new_y
    (ite (= (loc s) ON)    (+ (y s) RATE_IN)
    (ite (= (loc s) SWOFF) (+ (y s) RATE_IN)
    (ite (= (loc s) OFF)   (- (y s) RATE_OUT)
    (ite (= (loc s) SWON)  (- (y s) RATE_OUT)
    (y s)))))
  ))
  (ite (and (= (loc s) ON) (>= (y s) HIGH))
    (mk-state SWOFF 0 (y s))
  (ite (and (= (loc s) SWOFF) (or (>= (x s) DELAY) (< (x s) 0)))
    (mk-state OFF (x s) (y s))
  (ite (and (= (loc s) OFF) (<= (y s) LOW))
    (mk-state SWON 0 (y s))
  (ite (and (= (loc s) SWON) (or (>= (x s) DELAY) (< (x s) 0)))
    (mk-state ON (x s) (y s))
    (mk-state (loc s) (x s) (y s))
  ))))))
)
