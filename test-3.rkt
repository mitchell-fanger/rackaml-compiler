#lang racket
(begin 
    (define (f x y z) (+ x (+ y z)))
    (let ((g (f 1))) (g 2 3)))
