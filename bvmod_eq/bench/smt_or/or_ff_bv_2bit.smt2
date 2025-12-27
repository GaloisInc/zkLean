(set-logic ALL)
(set-option :produce-models true)
(define-sort FF () (_ FiniteField 52435875175126190479447740508185965837690552500527637822603658699938581184513))
(declare-fun one () FF)
(declare-fun zero () FF)
(declare-fun neg_one () FF)
(assert (= one #f1m52435875175126190479447740508185965837690552500527637822603658699938581184513))
(assert (= zero #f0m52435875175126190479447740508185965837690552500527637822603658699938581184513))
(assert (= neg_one #f52435875175126190479447740508185965837690552500527637822603658699938581184512m52435875175126190479447740508185965837690552500527637822603658699938581184513))

(declare-fun a () (_ BitVec 2))
(declare-fun b () (_ BitVec 2))
(declare-fun out_bv () (_ BitVec 2))

(declare-fun x0 () FF)
(declare-fun x1 () FF)

(declare-fun y0 () FF)
(declare-fun y1 () FF)

(declare-fun out0 () FF)
(declare-fun out1 () FF)

(declare-fun out_ff () FF)

;; ===============================
;; Input BV → FF (x0 is MSB, x{B-1} is LSB, matching your 2-bit file)
;; ===============================
(assert (= x0 (ite (= ((_ extract 1 1) a) #b1) one zero)))
(assert (= x1 (ite (= ((_ extract 0 0) a) #b1) one zero)))
(assert (= y0 (ite (= ((_ extract 1 1) b) #b1) one zero)))
(assert (= y1 (ite (= ((_ extract 0 0) b) #b1) one zero)))
(assert (= out0 (ite (= ((_ extract 1 1) out_bv) #b1) one zero)))
(assert (= out1 (ite (= ((_ extract 0 0) out_bv) #b1) one zero)))

;; bitness constraints
(assert (= x0 (ff.mul x0 x0)))
(assert (= x1 (ff.mul x1 x1)))
(assert (= y0 (ff.mul y0 y0)))
(assert (= y1 (ff.mul y1 y1)))
(assert (= out0 (ff.mul out0 out0)))
(assert (= out1 (ff.mul out1 out1)))


(define-fun OR_FF_2 (
  (y1 FF) (x1 FF) (y0 FF) (x0 FF)) FF
  (ff.add (ff.mul #f1m52435875175126190479447740508185965837690552500527637822603658699938581184513 (ff.add y1 x1 (ff.mul neg_one (ff.mul y1 x1)))) (ff.mul #f2m52435875175126190479447740508185965837690552500527637822603658699938581184513 (ff.add y0 x0 (ff.mul neg_one (ff.mul y0 x0)))))
)

(assert (= out_ff (OR_FF_2 y1 x1 y0 x0)))

(assert (= out_bv (bvor a b)))

;; Bit decomposition link (same shape as your 2-bit: out_ff = out_{LSB} + 2*out_{next} + ...)
(assert (not (= out_ff (ff.add (ff.mul #f1m52435875175126190479447740508185965837690552500527637822603658699938581184513 out1) (ff.mul #f2m52435875175126190479447740508185965837690552500527637822603658699938581184513 out0)))))

(check-sat)
