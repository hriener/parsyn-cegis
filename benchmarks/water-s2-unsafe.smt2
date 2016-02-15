;; http://symbolaris.com/course/lahs/LAHS-04-hybrid-examples.pdf, slide 45
;; run: ./parsyn-cegis.py benchmarks/water-s2-unsafe.smt2 "INV_U INV_L" -K 10
;; expected result: UNSAFE
(declare-datatypes () ((location ON OFF OPEN)))
(declare-datatypes () ((state (mk-state (loc location) (x Real)))))
(declare-datatypes () ((input (mk-input (err Int)))))

(define-fun INV_U () Real 0)
(define-fun INV_L () Real 0)

;; Init(s) ---> Bool
(define-fun init ((s state)) Bool
  (and
    (>= (x s) 1.0) (<= (x s) 10.0)
  )
)

;; Safe(s) ---> Bool
(define-fun safe ((s state)) Bool
  (and (>= (x s) 1.0) (<= (x s) 10.0))
)

;;; Inv(s) ---> Bool
(define-fun inv ((s state)) Bool
  (and (>= (x s) INV_L) (<= (x s) INV_U))
)

;; T(s,i) ---> s
(define-fun tau ((s state) (i input)) state
  (let ((new_x
    (ite (= (loc s) ON) (+ (x s) 1.0)
    (ite (= (loc s) OFF) (- (x s) 0.1)
    (ite (= (loc s) OPEN) (- (x s) 2.0)
    (x s))))
  ))
  (ite (and (= (loc s) ON) (or (>= (x s) 7.0) (> (x s) 9.0)))
    (mk-state OFF (+ (x s) 1.0))
  (ite (and (= (loc s) OFF) (or (< (x s) 5.0) (< (x s) 3.0)))
    (mk-state OPEN (x s))
  (ite (and (= (loc s) OPEN) (or (< (x s) 0.0) (<= (x s) 2.0)))
    (mk-state ON (x s))
    (mk-state (loc s) new_x)
  ))))
)
