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
(declare-const delta_paramA Real)
(assert (and (and (and (and (and (and true
  (xor (= w0 0.1) (and (= w0 0) (= "B" (ite (> 1 (+ (- 2) (absolute delta_paramA))) "B" "A")))))
  (xor (= w1 0.1) (and (= w1 0) (= "B" (ite (> 1.5 (+ (- 2) (absolute delta_paramA))) "B" "A")))))
  (xor (= w2 0.1) (and (= w2 0) (= "B" (ite (> -0.5 (+ (- 2) (absolute delta_paramA))) "B" "A")))))
  (xor (= w3 0.1) (and (= w3 0) (= "A" (ite (> -1 (+ (- 2) (absolute delta_paramA))) "B" "A")))))
  (xor (= w4 0.1) (and (= w4 0) (= "A" (ite (> -1.5 (+ (- 2) (absolute delta_paramA))) "B" "A")))))
  (xor (= w5 0.1) (and (= w5 0) (= "A" (ite (> 0.5 (+ (- 2) (absolute delta_paramA))) "B" "A"))))))
(minimize (+ w0 w1 w2 w3 w4 w5 (absolute delta_paramA)))

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
(assert (and (and (and (and true
  (xor (= w0 10) (and (= w0 0) (= "B" (ite (> 1 (+ (- 2) (absolute delta_paramA))) "B" "A")))))
  (xor (= w1 10) (and (= w1 0) (= "B" (ite (> 1.5 (+ (- 2) (absolute delta_paramA))) "B" "A")))))
  (xor (= w3 10) (and (= w3 0) (= "A" (ite (> -1 (+ (- 2) (absolute delta_paramA))) "B" "A")))))
  (xor (= w4 10) (and (= w4 0) (= "A" (ite (> -1.5 (+ (- 2) (absolute delta_paramA))) "B" "A"))))))
(minimize (+ w0 w1 w2 w3 w4 w5 (absolute delta_paramA)))

(check-sat)
(get-model)
