;; R. Alur et al. Theoretical Computer Science 138 (1995) 3--34, Fig. 5
;; run: ./parsyn-cegis.py benchmarks/thermal2-s2-safe.smt2 "INV_CLK0 INV_CLK1 INV_THETA_M_LO INV_THETA_M_HI" -K 10
;; expected result: SAFE
(declare-datatypes () ((location v0 v1 v2)))
(declare-datatypes () ((state (mk-state (loc location) (theta Real) (clk0 Int) (clk1 Int)))))
(declare-datatypes () ((input (mk-input (nondet Bool)))))

(define-fun INV_CLK0 () Int 0)
(define-fun INV_CLK1 () Int 0)
(define-fun INV_THETA_M_LO () Real 3.0)
(define-fun INV_THETA_M_HI () Real 15.0)

(define-fun rise_rate  () Real 0.2)
(define-fun decr_rate1 () Real 0.3)
(define-fun decr_rate2 () Real 0.15)

(define-fun theta_M () Real 15.0)
(define-fun theta_m () Real  3.0)

(define-fun timer_threshold0 () Int 1)
(define-fun timer_threshold1 () Int 2)

;; Init(s) ---> Bool
(define-fun init ((s state)) Bool
  (and
    (>= (theta s) theta_m) (<= (theta s) theta_M)
    (>= (clk0 s) 0) (<= (clk0 s) timer_threshold0)
    (>= (clk1 s) 0) (<= (clk1 s) timer_threshold1)
  )
)

;; Safe(s) ---> Bool
(define-fun safe ((s state)) Bool
  (and (>= (theta s) theta_m) (<= (theta s) (+ theta_M (* 2 rise_rate))))
)

;;; Inv(s) ---> Bool
(define-fun inv ((s state)) Bool
  (and (>= (clk0 s) INV_CLK0) (>= (clk1 s) INV_CLK1) (>= (theta s) INV_THETA_M_LO) (<= (theta s) INV_THETA_M_HI))
)

;; T(s,i) ---> s
(define-fun tau ((s state) (i input)) state
  (let ((new_clk0
    (+ (clk0 s) 1)))
  (let ((new_clk1
    (+ (clk1 s) 1)))
  (let ((new_theta
    (ite (= (loc s) v0) (+ (theta s) rise_rate)
    (ite (= (loc s) v1) (- (theta s) decr_rate1)
    (ite (= (loc s) v2) (- (theta s) decr_rate2)
      (theta s)
    )))
  ))
  (ite (and (= (loc s) v0) (>= (theta s) (- theta_M rise_rate)) (>= (clk0 s) timer_threshold0))
    (mk-state v1 (theta s) new_clk0 new_clk1)
  (ite (and (= (loc s) v0) (>= (theta s) (- theta_M rise_rate)) (>= (clk1 s) timer_threshold1))
    (mk-state v2 (theta s) new_clk0 new_clk1)
  (ite (and (= (loc s) v1) (<= (theta s) (+ theta_m decr_rate1)))
    (mk-state v0 (theta s) 0 new_clk1)
  (ite (and (= (loc s) v2) (<= (theta s) (+ theta_m decr_rate2)))
    (mk-state v0 (theta s) new_clk0 0)
  (mk-state (loc s) new_theta new_clk0 new_clk1)
  )))))))
)
