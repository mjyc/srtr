(define-fun absolute ((x Real)) Real
  (ite (>= x 0) x (- x)))
(declare-const w0 Real)
(declare-const w1 Real)
(declare-const delta_paramA Real)
(assert
  (and
    (and true (xor (= w0 20) (and (= w0 0) (= "B" (ite (> 1 (+ 1 delta_paramA)) "B" "A")))))
    (xor (= w1 20) (and (= w1 0) (= "A" (ite (<= -1 (+ 1 delta_paramA)) "A"
"B"))))))
(minimize (+ w0 w1 (absolute delta_paramA)))
(check-sat)
(get-model)


(define-fun absolute ((x Real)) Real
  (ite (>= x 0) x (- x)))

(declare-const w0 Real)
(declare-const w1 Real)
(declare-const w2 Real)
(declare-const w3 Real)
(declare-const w4 Real)
(declare-const w5 Real)
(declare-const w6 Real)
(declare-const w7 Real)
(declare-const delta_paramA Real)
(assert (and (and (and (and (and (and (and (and true (xor (= w0 1) (and (= w0 0) (= "B" "B")))) (xor (= w1 1) (and (= w1 0) (= "A" "B")))) (xor (= w2 1) (and (= w2 0) (= "A" "B")))) (xor (= w3 1) (and (= w3 0) (= "A" "B")))) (xor (= w4 1) (and (= w4 0) (= "B" (ite (> -1 (+ 0 delta_paramA)) "B" "A"))))) (xor (= w5 1) (and (= w5 0) (= "B" (ite (> -1.5 (+ 0 delta_paramA)) "B" "A"))))) (xor (= w6 1) (and (= w6 0) (= "B" (ite (> -0.5 (+ 0 delta_paramA)) "B" "A"))))) (xor (= w7 1) (and (= w7 0) (= "B" (ite (> 1 (+ 0 delta_paramA)) "B" "A"))))))
(minimize (+ w0 w1 w2 w3 w4 w5 w6 w7 (absolute delta_paramA)))
(check-sat)
(get-model)


(define-fun absolute ((x Real)) Real
  (ite (>= x 0) x (- x)))
(declare-const w0 Real)
(declare-const w1 Real)
(declare-const w2 Real)
(declare-const w3 Real)
(declare-const w4 Real)
(declare-const w5 Real)
(declare-const delta_paramA Real)
(assert (and (and (and (and (and (and true
  (xor (= w0 1) (and (= w0 0) (= "B" "B"))))
  (xor (= w1 1) (and (= w1 0) (= "A" "B"))))
  (xor (= w2 1) (and (= w2 0) (= "A" "B"))))
  (xor (= w3 1) (and (= w3 0) (= "B" (ite (> -1 (+ 0 delta_paramA)) "B" "A")))))
  (xor (= w4 1) (and (= w4 0) (= "B" (ite (> -1.5 (+ 0 delta_paramA)) "B" "A")))))
  (xor (= w5 1) (and (= w5 0) (= "B" (ite (> -0.5 (+ 0 delta_paramA)) "B" "A"))))))
(minimize (+ w0 w1 w2 w3 w4 w5 (absolute delta_paramA)))
(check-sat)
(get-model)
