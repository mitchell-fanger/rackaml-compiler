#lang racket
(begin 
    (define (f x y z) (+ x (+ y z)))
    (let ((g (f 1))) 
        (let ((list (cons 1 (cons 2 (cons 3 (cons 4 '())))))) 
            (apply g (cdr (cdr list))))))