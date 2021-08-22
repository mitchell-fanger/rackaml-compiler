#lang racket
(begin 
    (define (f x y z) (+ x (+ y z)))
    (let ((g (f 1))) (apply g (cdr (cons 1 (cons 2 (cons 3 '())))))))
