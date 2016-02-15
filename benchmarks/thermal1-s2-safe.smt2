;; no source
;; run: ./parsyn-cegis.py benchmarks/thermal1-s2-safe.smt2 "INV_U INV_L" -K 10
;; expected result: SAFE
(declare-datatypes () ((location OFF HEATING COOLING)))
(declare-datatypes () ((state (mk-state (loc location) (temp Real)))))
(declare-datatypes () ((input (mk-input (err Real)))))

(define-fun INIT_LOC () location HEATING)
(define-fun INIT_TEMP () Real -7.0) ; in centigrade
(define-fun INIT_STATE () state (mk-state INIT_LOC INIT_TEMP))

(define-fun LOWER_SWITCHING_THRESHOLD () Real -10.0)
(define-fun UPPER_SWITCHING_THRESHOLD () Real -5.0)

(define-fun BAD_ABOVE () Real -3.0)
(define-fun BAD_BELOW () Real -12.0)

(define-fun INV_U () Real -3.0)
(define-fun INV_L () Real -12.0)

(define-fun CTRL_INTERVAL () Real 60.0)
(define-fun HEATING_RATE () Real 0.01)
(define-fun COOLING_RATE () Real 0.01)
(define-fun MAX_ERR () Real 0.3)

;; T(s,i) ---> s
(define-fun tau ((s state) (i input)) state
  (let ((new_temp
      (ite (= (loc s) COOLING)
        (- (temp s) (* CTRL_INTERVAL COOLING_RATE))
      (ite (= (loc s) HEATING)
        (+ (temp s) (* CTRL_INTERVAL HEATING_RATE))
      (temp s)))
       ))
  (let ((new_temp_with_err (ite (and (<= (err i) MAX_ERR) (>= (err i) (- 0 MAX_ERR)))
                            (+ new_temp (err i))
                            new_temp
                           )
       ))
    (mk-state
      (ite (> new_temp_with_err UPPER_SWITCHING_THRESHOLD) COOLING
      (ite (< new_temp_with_err LOWER_SWITCHING_THRESHOLD) HEATING
      (loc s)))
      new_temp
    )
  ))
)

;;; Init(s) ---> Bool
(define-fun init ((s state)) Bool
  (= s INIT_STATE)
)

;;; Inv(s) ---> Bool
(define-fun inv ((s state)) Bool
  (and
    (<= (temp s) INV_U)
    (>= (temp s) INV_L)
  )
)

;;; Safe(s) ---> Bool
(define-fun safe ((s state)) Bool
  (and
    (<= (temp s) BAD_ABOVE)
    (>= (temp s) BAD_BELOW)
  )
)

