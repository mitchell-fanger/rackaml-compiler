#lang racket
(provide (all-defined-out))
(require "ast.rkt" "types.rkt" a86/ast)

;; Registers used
(define rax 'rax) ; return
(define rbx 'rbx) ; heap
(define rcx 'rcx) ; scratch
(define rdx 'rdx) ; return, 2
(define r8  'r8)  ; scratch in +, -
(define r9  'r9)  ; scratch in assert-type and tail-calls
(define rsp 'rsp) ; stack
(define rdi 'rdi) ; arg

;; type CEnv = [Listof Variable]

;; Expr -> Asm
(define (compile p)
  (match (label-λ (desugar p))                ; <-- changed!
    [(Prog '() e)  
     (prog (Extern 'peek_byte)
           (Extern 'read_byte)
           (Extern 'write_byte)
           (Extern 'raise_error)
           (Label 'entry)
           (Mov rbx rdi)
           (compile-e e '(#f))
           (Mov rdx rbx)
           (Ret)
           (compile-λ-definitions (λs e)))])) ; <-- changed!

;; [Listof Defn] -> Asm
(define (compile-λ-definitions ds)
  (seq
    (match ds
      ['() (seq)]
      [(cons d ds)
       (seq (compile-λ-definition d)
            (compile-λ-definitions ds))])))

;; This is the code generation for the lambdas themselves.
;; It's not very different from generating code for user-defined functions,
;; because lambdas _are_ user defined functions, they just don't have a name
;;
;; Defn -> Asm
(define (compile-λ-definition l)
  (match l
    [(Lam '() xs e) (error "Lambdas must be labelled before code gen (contact your compiler writer)")]
    [(Lam f xs e)     ;; (f x y z)    env: (z y x free1 free2 free3 ) (x y z fv1 fv2 fv3) -> (fv3 fv2 fv1 z y x) -> (#f #args 3 fv3 fv2 fv1 z y x) 
     (let* ((free (remq* xs (fvs e)))
            ; leave space for RIP


            ;; (env (parity (cons #f (cons (length free) (reverse (append xs free)))))))  ORIGINAL
            ;; We add another item to the env because for apply (and partial app probably ?) we need to know the amount things on the stack 
            ;; since we do not know at compile time
            (env (parity (cons #f (cons #f (cons (length free) (reverse (append xs free))))))))
           (seq (Label (symbol->label f))
             ; we need the #args on the frame, not the length of the entire
             ; env (which may have padding)
             (compile-e e env)
             (Ret)))]))

(define (parity c)
  (if (even? (length c))
      (append c (list #f))
      c))

;; Expr CEnv -> Asm
(define (compile-e e c)
  (seq
       (match e
         [(? imm? i)      (compile-value (get-imm i))]
         [(Var x)         (compile-variable x c)]
         [(App f es)      (compile-call f es c)]
         [(Lam l xs e0)   (compile-λ xs l (fvs e) c)] ; why do we ignore e0?
         [(Prim0 p)       (compile-prim0 p c)]
         [(Prim1 p e)     (compile-prim1 p e c)]
         [(Prim2 p e1 e2) (compile-prim2 p e1 e2 c)]
         [(If e1 e2 e3)   (compile-if e1 e2 e3 c)]
         [(Begin e1 e2)   (compile-begin e1 e2 c)]
         [(LetRec bs e1)  (compile-letrec (map car bs) (map cadr bs) e1 c)]
         [(Let x e1 e2)   (compile-let x e1 e2 c)]
         
         ;; FINAL PROJECT: compiling apply just calls function 
         [(Apply f lst)   (compile-apply f lst c)])))


;; Value -> Asm
(define (compile-value v)
  (seq (Mov rax (imm->bits v))))

;; Id CEnv -> Asm
(define (compile-variable x c)
  (let ((i (lookup x c)))       
    (seq (Mov rax (Offset rsp i)))))

;; (Listof Variable) Label (Listof Variable) CEnv -> Asm
(define (compile-λ xs f ys c)
  (seq
    ; Save label address
    (Lea rax (symbol->label f))
    (Mov (Offset rbx 0) rax)

    ; Save the environment
    (%% "Begin saving the env")
    
    ;; moving the expected #args to function closure 
    (Mov r8 (length xs))
    (Mov (Offset rbx 8) r8)

    ;; FINAL PROJECT: add number of predefined args to closure
    (Mov r8 0)
    (Mov (Offset rbx 16) r8)

    ;; FINAL PROJECT: add # of fvs to closure and add free vars
    (Mov r8 (length ys))
    (Mov (Offset rbx 24) r8)
    (Mov r9 rbx)
    (Add r9 32)
    (copy-env-to-heap ys c 0)

    (%% "end saving the env")

    ; Return a pointer to the closure
    (Mov rax rbx)
    (Or rax type-proc)

    ;; FINAL PROJECT: changed 3->4 for #pdargs in closure
    (Add rbx (* 8 (+ 4 (length ys))))))

;; (Listof Variable) CEnv Natural -> Asm
;; Pointer to beginning of environment in r9
(define (copy-env-to-heap fvs c i)
  (match fvs
    ['() (seq)]
    [(cons x fvs)
     (seq
       ; Move the stack item  in question to a temp register
       (Mov r8 (Offset rsp (lookup x c)))

       ; Put the iterm in the heap
       (Mov (Offset r9 i) r8)

       ; Do it again for the rest of the items, incrementing how
       ; far away from r9 the next item should be
       (copy-env-to-heap fvs c (+ 8 i)))]))

;; Id CEnv -> Asm
(define (compile-fun f)
       ; Load the address of the label into rax
  (seq (Lea rax (symbol->label f))
       ; Copy the value onto the heap
       (Mov (Offset rbx 0) rax)
       ; Copy the heap address into rax
       (Mov rax rbx)
       ; Tag the value as a proc
       (Or rax type-proc)
       ; Bump the heap pointer
       (Add rbx 8)))

;; Op0 CEnv -> Asm
(define (compile-prim0 p c)
  (match p
    ['void      (seq (Mov rax val-void))]
    ['read-byte (seq (pad-stack c)
                     (Call 'read_byte)
                     (unpad-stack c))]
    ['peek-byte (seq (pad-stack c)
                     (Call 'peek_byte)
                     (unpad-stack c))]))

;; Op1 Expr CEnv -> Asm
(define (compile-prim1 p e c)
  (seq (compile-e e c)
       (match p
         ['add1
          (seq (assert-integer rax)
               (Add rax (imm->bits 1)))]
         ['sub1
          (seq (assert-integer rax)
               (Sub rax (imm->bits 1)))]         
         ['zero?
          (let ((l1 (gensym)))
            (seq (assert-integer rax)
                 (Cmp rax 0)
                 (Mov rax val-true)
                 (Je l1)
                 (Mov rax val-false)
                 (Label l1)))]
         ['char?
          (let ((l1 (gensym)))
            (seq (And rax mask-char)
                 (Xor rax type-char)
                 (Cmp rax 0)
                 (Mov rax val-true)
                 (Je l1)
                 (Mov rax val-false)
                 (Label l1)))]
         ['char->integer
          (seq (assert-char rax)
               (Sar rax char-shift)
               (Sal rax int-shift))]
         ['integer->char
          (seq assert-codepoint
               (Sar rax int-shift)
               (Sal rax char-shift)
               (Xor rax type-char))]
         ['eof-object? (eq-imm val-eof)]
         ['write-byte
          (seq assert-byte
               (pad-stack c)
               (Mov rdi rax)
               (Call 'write_byte)
               (unpad-stack c)
               (Mov rax val-void))]
         ['box
          (seq (Mov (Offset rbx 0) rax)
               (Mov rax rbx)
               (Or rax type-box)
               (Add rbx 8))]
         ['unbox
          (seq (assert-box rax)
               (Xor rax type-box)
               (Mov rax (Offset rax 0)))]
         ['car
          (seq (assert-cons rax)
               (Xor rax type-cons)
               (Mov rax (Offset rax 8)))]
         ['cdr
          (seq (assert-cons rax)
               (Xor rax type-cons)
               (Mov rax (Offset rax 0)))]
         ['empty? (eq-imm val-empty)]
         ['procedure-arity 
          (seq (assert-proc rax)
               (Xor rax type-proc)
               (Mov rax (Offset rax 8)))]
         )))

;; Op2 Expr Expr CEnv -> Asm
(define (compile-prim2 p e1 e2 c)
  (seq (compile-e e1 c)
       (Push rax)
       (compile-e e2 (cons #f c))
       (match p
         ['+
          (seq (Pop r8)
               (assert-integer r8)
               (assert-integer rax)
               (Add rax r8))]
         ['-
          (seq (Pop r8)
               (assert-integer r8)
               (assert-integer rax)
               (Sub r8 rax)
               (Mov rax r8))]
         ['eq?
          (let ((l (gensym)))
            (seq (Cmp rax (Offset rsp 0))
                 (Sub rsp 8)
                 (Mov rax val-true)
                 (Je l)
                 (Mov rax val-false)
                 (Label l)))]
         ['cons
          (seq (Mov (Offset rbx 0) rax)
               (Pop rax)
               (Mov (Offset rbx 8) rax)
               (Mov rax rbx)
               (Or rax type-cons)
               (Add rbx 16))])))

;; FINAL PROJECT: compiles apply, where expr-lst evaluates to a list of any size
;; need to move everything on stack and make sure sizes are correct 
(define (compile-apply f expr-lst c)
  (let ((loop (gensym 'listsize))   (end (gensym 'endlistsize))) 
    (seq 
        (compile-e f c)      ;; compile the function and assert that it actually is procedure
        (assert-proc 'rax) 
        (Push 'rax)

        (compile-e expr-lst (cons #f c))
        (Mov 'rdx 'rax)

        (Mov 'rax (Offset 'rsp 0))     ;; moves the closure into rax for future use
        (Xor 'rax type-proc)           ;; remove proc tag

        ;; need to add the predefined args
        (push-predef-args)

        
        (Mov 'r9 'rdx)                 ;; r9 for loop
        (Mov 'r8 0)                    ;; start with length 0


        
        (Label loop)
        (Cmp 'r9 val-empty)
        (Je end)

        (Push 'r9)
        (assert-cons 'r9)
        (Pop 'r9)

        (Xor 'r9 type-cons)

        (Add 'r8 1)
        (Mov 'rcx (Offset 'r9 8))
        (Push 'rcx)                ;; we can add everything to the stack as we go since we know exactly how much we added in r8
        (Mov 'r9 (Offset 'r9 0))   ;; updated the pointer
        (Jmp loop) 
   
        (Label end)

        ;; we will do arity checking here
        (Mov r9 (Offset 'rax 8))
        (Cmp r9 r8)
        (Jne 'raise_error)


        ;; only reach this point if stuff is on the stack and we have reached the end of a list
        ;; so we need to add the env vars as well 
        
        (Add 'r8 (Offset 'rax 16))
        (Mov 'rdx 'r8) ;; save # of args before closure clobbers r8
        (copy-closure-env-to-stack)
        (Mov 'r8 'rdx)

        ;; also need to add the # of free vars 
        (Mov 'rcx (Offset 'rax 24))
        (Push 'rcx)
        (Push 'r8)  ;; add the size of list to stack to know how much to remove

        
        (Mov 'rax (Offset 'rax 0))
        (Call 'rax)


        ;; so now we have the following on the stack and registers: 
        ;; rax:          r8: length of list passed in;     r9: end of list;  rcx: # free vars
        ;; | | |closure|a1|a2|a3|... |fv1 |fv2|... |#freevars|#args| | | | 

        (Pop 'r8)           ;; # args
        (Pop 'r9)           ;; # free vars
        (Add 'r9 'r8)       ;; # free vars + args 
        (Add 'r9 1)         ;; # free vars + args + 1
        (Sal 'r9 3)         ;; ^ * 8
        (Add 'rsp 'r9))))   ;; add to the rsp
        
  

;;       8 16 .. 
;; 0 ... |0|1|2|3|x|y|z| ... MAXRAM
;;            --^


;; ======================================
; c = '(c b a #f)
; (let ((a 13)) 
;   (let ((b 12)) 
;     (let ((c 11)) 
;       ((lambda (x) (+ (+ a x) b)) 10)))

;     func | x | b | a

; c = '(a #f)
; (let ((a 13)) 
;   ((lambda (x) (+ a x)) 10))

;   | func | x | a 

;; ======================================



;; Id [Listof Expr] CEnv -> Asm
;; Here's why this code is so gross: you have to align the stack for the call
;; but you have to do it *before* evaluating the arguments es, because you need
;; es's values to be just above 'rsp when the call is made.  But if you push
;; a frame in order to align the call, you've got to compile es in a static
;; environment that accounts for that frame, hence:
(define (compile-call f es c)
  (let* ((cnt (length es))
         (aligned (even? (+ cnt (length c) 1))) ;; ADDED 1 BECAUSE WE WILL NEED TO PAD THE STACK
         (i (if aligned 1 2))
         (c+ (if aligned
                 c
                 (cons #f c)))
         (c++ (cons #f c+))
         (partial-app (gensym 'partial))
         (end         (gensym 'end))
         (shift-loop  (gensym 'shiftstack))
         (shift-end   (gensym 'shiftend))
         (copyfvs    (gensym 'copyfvs))
         (predef     (gensym 'predef))
         (copypredef (gensym 'copypredef))
         (endpredef (gensym 'endpredef)))
    (seq

      (%% (~a "Begin compile-call: aligned = " aligned " function: " f))
      ; Adjust the stack for alignment, if necessary
      (if aligned
          (seq)
          (Sub rsp 8))

      ; Generate the code for the thing being called
      ; and push the result on the stack
      (compile-e f c+)
      (%% "Push function on stack")
      (Push rax)

      (%% (~a "Begin compile-es: es = " es))
      ; Generate the code for the arguments
      ; all results will be put on the stack (compile-es does this)
      (compile-es es c++)
  
      ; Get the function being called off the stack
      ; Ensure it's a proc and remove the tag
      ; Remember it points to the _closure_
      (%% "Get function off stack")
      (Mov rax (Offset rsp (* 8 cnt)))
      (assert-proc rax)
      (Xor rax type-proc)

      ;; get # of predef args from closure
      (Mov r9 (Offset rax 16))
      (Sal r9 3)
      (Mov 'rcx 'rsp)
      (Sub 'rcx r9)

      (Mov 'r8 cnt)
      (Label shift-loop)
      (Cmp 'r8 0)
      (Je shift-end)
      
      (Mov 'r9 (Offset 'rsp 0))
      (Mov (Offset 'rcx 0) 'r9)
      (Add 'rsp 8)
      (Add 'rcx 8)
      (Sub 'r8 1)
      (Jmp shift-loop)

      (Label shift-end)

      ;; FINAL PROJECT: push predefined arguments onto stack
      (push-predef-args)

      (Sub 'rsp (* 8 cnt))

     

      ;; we will do arity checking here
      (Mov r9 (Offset rax 8))
      (Mov r8 cnt)
      (Cmp r9 r8)
      (Jg  partial-app)
      (Jne 'raise_error)


      (%% "Get closure env")
      (copy-closure-env-to-stack)
      (%% "finish closure env")

      ; get the size of the env and save it on the stack
      (Mov rcx (Offset rax 24))
      (Push rcx)

      (Mov 'rcx (Offset 'rax 16))
      (Push 'rcx)
  
      ; Actually call the function
      (Mov rax (Offset rax 0))
      (Call rax)

      ;; number of predefined variables 
      (Pop 'r9)
      (Sal 'r9 3)
  
      ; Get the size of the env off the stack
      (Pop rcx)
      (Sal rcx 3)

      ; pop args
      ; First the number of arguments + alignment + the closure
      ; then captured values

      (Add rsp (* 8 (+ i cnt)))
      ;(Add rsp (* 8 cnt))
      (Add 'rsp 'rcx)
      (Add 'rsp 'r9)
      (Jmp end)


      (Label partial-app)
      
      ;; TODO: create a new closure on the heap and return an address to it
      ;; how: 
      ;; 1. copy function address 
      ;; 2. expected # of arguments = original expected - cnt 
      ;; 3. # predef = original predef + cnt
      ;; 4. #fvs is same
      ;; 5. all fvs stay same
      ;; 6. new predef args added to end
      ;; 7. fix the stack 
      
      ;; have closure in rax

      ;;1. copy function addr
      (Mov 'r9 (Offset 'rax 0))
      (Mov (Offset 'rbx 0) 'r9)  

      ;;2. new expected # of args
      (Mov 'r9 (Offset 'rax 8))
      (Mov 'r8 cnt)
      (Sub 'r9 'r8)
      (Mov (Offset 'rbx 8) 'r9)

      ;;3. new # of predef args
      (Mov 'r9 (Offset 'rax 16))
      (Mov 'r8 cnt)
      (Add 'r9 'r8)
      (Mov (Offset 'rbx 16) 'r9)

      ;;4. #fvs
      (Mov 'r9 (Offset 'rax 24))
      (Mov (Offset 'rbx 24) 'r9)

      ;;5. copy all old fvs

      (Push 'rax)

      (Mov 'r8 'rbx)
      (Add 'r8 32)

      (Mov 'rcx 'rax)
      (Add 'rcx 32)
      
      (Label copyfvs)

      (Cmp 'r9 0)
      (Je predef)
      (Sub 'r9 1)
      (Mov 'rax (Offset 'rcx 0))
      (Mov (Offset 'r8 0) 'rax)
      (Add 'r8 8)
      (Add 'rcx 8)

      (Jmp copyfvs)

      (Label predef)

      (Pop 'rax)


      ;;6. we have all the new predef args on the stack, which means we can just add them to the closure from the stack
      (Mov 'r9 (Offset 'rbx 16))
      (Sub 'r9 1)
      (Sal 'r9 3)
      (Mov 'rcx 'rsp)
      (Add 'rcx 'r9)

      (Label copypredef)

      (Cmp 'rcx 'rsp)
      (Jl endpredef)
      (Mov 'rax (Offset 'rcx 0))
      (Mov (Offset 'r8 0) 'rax)
      (Add 'r8 8)
      (Sub 'rcx 8)

      (Jmp copypredef)
      (Label endpredef)

      ;; actually get our function ptr
      (Mov 'rax 'rbx)

      ;; move rbx to next empty location
      (Mov 'rbx 'r8)

      ;; pop stack
      (Mov 'r9 (Offset 'rax 16))
      (Add 'r9 1)
      (Sal 'r9 3)
      (Add 'rsp 'r9)

      (if aligned (seq) (Add 'rsp 8))

      (Or 'rax type-proc)

      (Label end))))





;; cnt + predef args ) * 8 
      ;; cnt * 8 + (Sal #predefargs 3)
      ;; (Mov rax rsp)                                  || | | | || | | | | 
      ;; (Add/Sub rax (8 * cnt))                       rax--^   
      ;; (Mov r9 predefargs)
      ;; (Sal r9 3)
      ;; (Add/Sub rax r9)
      ;; (Mov rax (Offset rax 0))

(define (push-predef-args) 
  (let ((loop (gensym 'predefloop)) (end (gensym 'predefend)))  
  (seq (Mov r9 (Offset rax 16)) ;; r9 = # predef args
       (Mov r8 (Offset rax 24)) ;; r8 = #fvs 
       (Add r8 4)               ;; # fvs + 4
       (Sal r8 3)               ;; # (fvs + 4) * 8
       (Mov rcx rax)            ;; rcx = rax
       (Add rcx r8)             ;; rcx = rax + r8 -> address of first predefined arg

       (Label loop)             ;; while (# predef args != 0)
       (Cmp r9 0)
       (Je end) 
       (Mov r8 (Offset rcx 0))
       (Push r8)
       (Add rcx 8)
       (Sub r9 1)
       (Jmp loop)
       (Label end))))



;; -> Asm
;; Copy closure's (in rax) env to stack in rcx
(define (copy-closure-env-to-stack)
  (let ((copy-loop (symbol->label (gensym 'copy_closure)))
        (copy-done (symbol->label (gensym 'copy_done))))
    (seq
      (Mov r8 (Offset rax 24)) ; length
      (Mov r9 rax)
      (Add r9 32)             ; start of env
      (Label copy-loop)
      (Cmp r8 0)
      (Je copy-done)
      (Mov rcx (Offset r9 0))
      (Push rcx)              ; Move val onto stack
      (Sub r8 1)
      (Add r9 8)
      (Jmp copy-loop)
      (Label copy-done))))

;; (f (add1 2) ())
;; [Listof Expr] CEnv -> Asm
(define (compile-es es c)
  (match es
    ['() '()]
    [(cons e es)
     (seq (compile-e e c)
          (Push rax)
          (compile-es es (cons #f c)))]))

;; Imm -> Asm
(define (eq-imm imm)
  (let ((l1 (gensym)))
    (seq (Cmp rax imm)
         (Mov rax val-true)
         (Je l1)
         (Mov rax val-false)
         (Label l1))))

;; Expr Expr Expr CEnv -> Asm
(define (compile-if e1 e2 e3 c)
  (let ((l1 (gensym 'if))
        (l2 (gensym 'if)))
    (seq (compile-e e1 c)
         (Cmp rax val-false)
         (Je l1)
         (%% (~a "Compiling then: " e2))
         (compile-e e2 c)
         (Jmp l2)
         (Label l1)
         (%% (~a "Compiling else: " e3))         
         (compile-e e3 c)
         (Label l2))))

;; Expr Expr CEnv -> Asm
(define (compile-begin e1 e2 c)
  (seq (compile-e e1 c)
       (compile-e e2 c)))

;; Id Expr Expr CEnv -> Asm
(define (compile-let x e1 e2 c)
  (seq (compile-e e1 c)
       (Push rax)
       (compile-e e2 (cons x c))
       (Add rsp 8)))

;; (Listof Variable) (Listof Lambda) Expr CEnv -> Asm
(define (compile-letrec fs ls e c)
  (seq
    (%% (~a  "Start compile letrec with" fs))
    (compile-letrec-λs ls c)
    (%% "letrec-init follows")
    (compile-letrec-init fs ls (append (reverse fs) c))
    (%% "Finish compile-letrec-init")
    (compile-e e (append (reverse fs) c))
    (Add rsp (* 8 (length fs)))))

;; (Listof Lambda) CEnv -> Asm
;; Create a bunch of uninitialized closures and push them on the stack
(define (compile-letrec-λs ls c)
  (match ls
    ['() (seq)]
    [(cons l ls)
     (match l
       [(Lam lab as body)
        (let ((ys (fvs l)))
             (seq
               (Lea rax (symbol->label lab))
               (Mov (Offset rbx 0) rax)

               (Mov r8 (length as))
               (Mov (Offset rbx 8) r8)

               ;; FINAL PROJECT: Add the # of predefined vars
               (Mov r8 0)
               (Mov (Offset rbx 16) r8)

               (Mov rax (length ys))
               (Mov (Offset rbx 24) rax)

               (Mov rax rbx)
               (Or rax type-proc)
               (%% (~a "The fvs of " lab " are " ys))
               (Add rbx (* 8 (+ 4 (length ys))))
               (Push rax)
               (compile-letrec-λs ls (cons #f c))))])]))

;; (Listof Variable) (Listof Lambda) CEnv -> Asm
(define (compile-letrec-init fs ls c)
  (match fs
    ['() (seq)]
    [(cons f fs)
     (let ((ys (fvs (first ls))))
          (seq
            (Mov r9 (Offset rsp (lookup f c)))
            (Xor r9 type-proc)
            (Add r9 32) ; move past label and length
            (copy-env-to-heap ys c 0)
            (compile-letrec-init fs (rest ls) c)))]))

;; (begin (define (f x) (if (zero? x) 1 (+ x (g (- x 1))))
;;        (define (g x) (if (zero? x) 2 ((f (- x 1)))))))



;; CEnv -> Asm
;; Pad the stack to be aligned for a call with stack arguments
(define (pad-stack-call c i)
  (match (even? (+ (length c) i))
    [#f (seq (Sub rsp 8) (% "padding stack"))]
    [#t (seq)]))

;; CEnv -> Asm
;; Pad the stack to be aligned for a call
(define (pad-stack c)
  (pad-stack-call c 0))

;; CEnv -> Asm
;; Undo the stack alignment after a call
(define (unpad-stack-call c i)
  (match (even? (+ (length c) i))
    [#f (seq (Add rsp 8) (% "unpadding"))]
    [#t (seq)]))

;; CEnv -> Asm
;; Undo the stack alignment after a call
(define (unpad-stack c)
  (unpad-stack-call c 0))

;; Id CEnv -> Integer
(define (lookup x cenv)
  (match cenv
    ['() (error "undefined variable:" x " Env: " cenv)]
    [(cons y rest)
     (match (eq? x y)
       [#t 0]
       [#f (+ 8 (lookup x rest))])]))

(define (in-frame cenv)
  (match cenv
    ['() 0]
    [(cons #f rest) 0]
    [(cons y rest)  (+ 1 (in-frame rest))]))

(define (assert-type mask type)
  (λ (arg)
    (seq (%% "Begin Assert")
         (Mov r9 arg)
         (And r9 mask)
         (Cmp r9 type)
         (Jne 'raise_error)
         (%% "End Assert"))))

(define (type-pred mask type)
  (let ((l (gensym)))
    (seq (And rax mask)
         (Cmp rax type)
         (Mov rax (imm->bits #t))
         (Je l)
         (Mov rax (imm->bits #f))
         (Label l))))
         
(define assert-integer
  (assert-type mask-int type-int))
(define assert-char
  (assert-type mask-char type-char))
(define assert-box
  (assert-type ptr-mask type-box))
(define assert-cons
  (assert-type ptr-mask type-cons))
(define assert-proc
  (assert-type ptr-mask type-proc))

(define assert-codepoint
  (let ((ok (gensym)))
    (seq (assert-integer rax)
         (Cmp rax (imm->bits 0))
         (Jl 'raise_error)
         (Cmp rax (imm->bits 1114111))
         (Jg 'raise_error)
         (Cmp rax (imm->bits 55295))
         (Jl ok)
         (Cmp rax (imm->bits 57344))
         (Jg ok)
         (Jmp 'raise_error)
         (Label ok))))
       
(define assert-byte
  (seq (assert-integer rax)
       (Cmp rax (imm->bits 0))
       (Jl 'raise_error)
       (Cmp rax (imm->bits 255))
       (Jg 'raise_error)))
       
;; Symbol -> Label
;; Produce a symbol that is a valid Nasm label
(define (symbol->label s)
  (string->symbol
   (string-append
    "label_"
    (list->string
     (map (λ (c)
            (if (or (char<=? #\a c #\z)
                    (char<=? #\A c #\Z)
                    (char<=? #\0 c #\9)
                    (memq c '(#\_ #\$ #\# #\@ #\~ #\. #\?)))
                c
                #\_))
         (string->list (symbol->string s))))
    "_"
    (number->string (eq-hash-code s) 16))))
