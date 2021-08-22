#lang racket
(provide main)
(require "ast.rkt" "parse.rkt" "compile.rkt" a86/printer)

;; String -> Void
;; Compile contents of given file name,
;; emit asm code on stdout
(define (main fn)
  (let ((p (open-input-file fn)))
    (begin
      (read-line p) ; ignore #lang racket line
      (displayln (label-λ (desugar (parse (read p)))))
      (close-input-port p))))
