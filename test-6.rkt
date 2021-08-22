#lang racket
(let ((double_sum (lambda (x y) (+ (+ x x) (+ y y)))))
    (double_sum 15))