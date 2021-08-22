#lang racket
(let ((double_sum (lambda (x y) (+ (+ x x) (+ y y)))))
    (let ((triple_add (lambda (x y z) (+ x (+ y z))))) 
        ((triple_add 1 (double_sum 15 10)) 2)))