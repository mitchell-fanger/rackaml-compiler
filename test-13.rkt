#lang racket
(let ((a 12)) 
    (let ((b 13)) 
        (let ((a 23))
            (let ((f (lambda (x y) (+ x (+ y (+ a b)))))) 
                (apply (f 11) (cons 12 '()))))))
                