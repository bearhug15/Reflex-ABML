(uiop:define-package Reflex-semantics
  (:use #:cl))
(in-package #:Reflex-semantics)


(mot "env")

(mot "agent"
    :atv "state num" int 0
    :at "value" (uniont string (listt string)))

(defun state-name (agent)
    (format nil "st~a" (aget agent "state num")))

(aclosure c :attribute "print" :type "blank program state" :stage nil 
    :agent a
    :do (state-name a))
(aclosure c :attribute "print" :type "outer var" :stage nil 
    :instance i
    :do i)


;(mot "term" (uniont "actuatable term" "nonactuatable term"))
;(mot "actuatable term" (uniont "binary operation" "unary operation" "value getter"  "cast operation"))
;(mot "nonactuatable term" (uniont "constant" "pstate compare" "outer var" "value list" "value map"))
;(mot "value list" (uniont (listt "term")))
;(mot "value map" (uniont cot))

;(mot "access" (uniont "term" "field name"))

(aclosure c :attribute "print" :type "variable access" :stage nil
    :instance i 
    :ap i "name" name 
    :ap i "path" path 
    :do (if (null path)
            (list name)
            (progn (update-push-aclosure c :av "stage" 'iter :av "path" path :av "res path" (list name))
                (clear-update-eval-aclosure c :av "instance" (car path)))))
(aclosure c :attribute "print" :type "variable access" :stage 'iter 
    :ap "path" path 
    :value val
    :p (if (is-instance (car path) string)
            (concatenate 'string "(AccessField " val ")")
            (concatenate 'string "(AccessIndex " val ")"))
    :ap "res path" res-path
    :do (if (> (length path) 1) 
            (progn (update-push-aclosure c :av "stage" 'iter :av "path" (cdr path) :av "res-path" (cons val res-path))
                (clear-update-eval-aclosure c :av "instance" (car (cdr path))))
            (cons val (reverse res-path))))

(aclosure c :attribute "print" :type "value getter" :stage nil
    :instance i
    :ap i "state" state 
    :do (update-push-aclosure c :ap "stage" 'state-def)
        (clear-update-eval-aclosure c :ap "instance" state))

(aclosure c :attribute "print" :type "value getter" :stage 'state-def
    :instance i
    :ap i "access" access 
    :value val
    :do (update-push-aclosure c :ap "stage" 'access-def :ap "state" val)
        (clear-update-eval-aclosure c :ap "instance" access))

(aclosure c :attribute "print" :type "value getter" :stage 'access-def
    :ap "state" state 
    :value access
    :p (car access) name 
    :p (cdr access) access-list
    :p (format nil "~{~a ~}" access-list) access-list-res
    :do (format nil "(getVarVal ~a ~a [~a])" state name access-list-res))

(aclosure c :attribute "print" :type "value setter" :stage nil
    :instance i
    :ap i "state" state 
    :do (update-push-aclosure c :ap "stage" 'state-def)
        (clear-update-eval-aclosure c :ap "instance" state))

(aclosure c :attribute "print" :type "value setter" :stage 'state-def
    :instance i
    :ap i "access" access 
    :value val
    :do (update-push-aclosure c :ap "stage" 'access-def :ap "state" val)
        (clear-update-eval-aclosure c :ap "instance" access))

(aclosure c :attribute "print" :type "value setter" :stage 'access-def
    :ap "state" state 
    :value access
    :instance i
    :ap i "value" value 
    :do (update-push-aclosure c :ap "stage" 'val-def :ap "access" access)
        (clear-update-eval-aclosure c :ap "instance" value))

(aclosure c :attribute "print" :type "value setter" :stage 'val-def
    :ap "state" state 
    :ap "access" access 
    :value val
    :p (car access) name 
    :p (cdr access) access-list
    :p (format nil "~{~a ~}" access-list) access-list-res
    :do (format nil "(setVarVal ~a ~a [~a] ~a)" state name access-list-res val))

(aclosure c :attribute "print" :type "binary operation" :stage nil 
    :instance i
    :ap i "left" left 
    :do (update-push-aclosure c :ap "stage" 'left)
        (clear-update-eval-aclosure c :ap "instance" left))
(aclosure c :attribute "print" :type "binary operation" :stage 'left 
    :instance i
    :ap i "right" right 
    :value left
    :do (update-push-aclosure c :ap "stage" 'right :ap "left" left)
        (clear-update-eval-aclosure c :ap "instance" right))
(aclosure c :attribute "print" :type "binary operation" :stage 'right 
    :instance i 
    :ap i "op" op
    :value right
    :ap "left" left
    :do (cond
    ;; Логические
    ((equal op "&&")
     (concatenate 'string "(" left " \\<and> " right ")"))
    
    ((equal op "||")
     (concatenate 'string "(" left " \\<or> " right ")"))
    
    ;; Сравнения
    ((equal op "==")
     (concatenate 'string "(" left " = " right ")"))
    
    ((equal op "!=")
     (concatenate 'string "(\\<not> (" left " = " right "))"))
    
    ((equal op "<")
     (concatenate 'string "(" left " < " right ")"))
    
    ((equal op "<=")
     (concatenate 'string "(" left " \\<le> " right ")"))
    
    ((equal op ">")
     (concatenate 'string "(" left " > " right ")"))
    
    ((equal op ">=")
     (concatenate 'string "(" left " \\<ge> " right ")"))
    
    ;; Арифметика
    ((equal op "+")
     (concatenate 'string "(" left " + " right ")"))
    
    ((equal op "-")
     (concatenate 'string "(" left " - " right ")"))
    
    ((equal op "*")
     (concatenate 'string "(" left " * " right ")"))
    
    ((equal op "/")
     (concatenate 'string "(" left " / " right ")"))
    
    ((equal op "%")
     (concatenate 'string "(" left " mod " right ")"))
    
    ;; Побитовые
    ((equal op "&")
     (concatenate 'string "(" left " AND " right ")"))
    
    ((equal op "|")
     (concatenate 'string "(" left " OR " right ")"))
    
    ((equal op "^")
     (concatenate 'string "(" left " XOR " right ")"))
    
    ((equal op "<<")
     (concatenate 'string "(push_bit " right " " left ")"))
    
    ((equal op ">>")
     (concatenate 'string "(drop_bit " right " " left ")"))
    
    ;; fallback
    (t (error "Unknown operator: ~A" op))))

(aclosure c :attribute "print" :type "unary operation" :stage nil 
    :instance i
    :ap i "right" right 
    :do (update-push-aclosure c :ap "stage" 'right)
        (clear-update-eval-aclosure c :ap "instance" right))
(aclosure c :attribute "print" :type "unary operation" :stage 'right 
    :instance i 
    :ap i "op" op
    :ap i (aseq "right" "type") ty 
    :p (cond 
        (equal ty 'int8))
    :value right
    :do (cond
    ((equal op "-.")
     (concatenate 'string "(- " right ")"))
    ((equal op "-.")
     (concatenate 'string "(\\<neg> " right ")"))
    ((equal op "~.")
        (cond 
            ((equal ty 'nat8) (concatenate 'string "((2^8 - 1) - "  right ")"))
            ((equal ty 'nat16) (concatenate 'string "((2^16 - 1) - "  right ")"))
            ((equal ty 'nat32) (concatenate 'string "((2^32 - 1) - "  right ")"))
            ((equal ty 'nat64) (concatenate 'string "((2^64 - 1) - "  right ")"))
            ((equal ty 'int8) (concatenate 'string "((2^8 - 1) - ("  right " mod 2^8))"))
            ((equal ty 'int16) (concatenate 'string "((2^16 - 1) - ("  right " mod 2^16))"))
            ((equal ty 'int32) (concatenate 'string "((2^32 - 1) - ("  right " mod 2^32))"))
            ((equal ty 'int64) (concatenate 'string "((2^64 - 1) - ("  right " mod 2^64))")))
    )
    ;; fallback
    (t (error "Unknown operator: ~A" op))))


(defstruct type-info
  kind     ;; :int | :uint | :float | :bool
  bits     ;; разрядность (для float можно 32/64)
  is-signed)

(defparameter *type-info-map*
  (list 
    (cons 'int8    (make-type-info :kind :int  :bits 8  :is-signed t))
    (cons 'int16   (make-type-info :kind :int  :bits 16 :is-signed t))
    (cons 'int32   (make-type-info :kind :int  :bits 32 :is-signed t))
    (cons 'int64   (make-type-info :kind :int  :bits 64 :is-signed t))
    (cons 'uint8   (make-type-info :kind :uint :bits 8  :is-signed nil))
    (cons 'uint16  (make-type-info :kind :uint :bits 16 :is-signed nil))
    (cons 'uint32  (make-type-info :kind :uint :bits 32 :is-signed nil))
    (cons 'uint64  (make-type-info :kind :uint :bits 64 :is-signed nil))
    (cons 'float   (make-type-info :kind :float :bits 32 :is-signed t))
    (cons 'double  (make-type-info :kind :float :bits 64 :is-signed t))
    (cons 'bool    (make-type-info :kind :bool :bits 1  :is-signed nil))))

(defparameter *isabelle-type-map*
  (list (cons 'int8  "int") (cons 'int16  "int") (cons 'int32  "int") (cons 'int64  "int")
    (cons 'uint8  "int") (cons 'uint16  "int") (cons 'uint32  "int") (cons 'uint64  "int")
    (cons 'float  "real") (cons 'double  "real") (cons 'bool  "bool")))

(defun lookup-info (tname)
  (or (cdr (assoc tname *type-info-map* :test #'eq))
      (error "Unknown type: ~a" tname)))

(defun lookup-isa-type (tname)
  (or (cdr (assoc tname *isabelle-type-map* :test #'eq))
      (error "Unknown type: ~a" tname)))

(defun int-bounds (info)
  (let ((b (type-info-bits info)))
    (if (type-info-is-signed info)
        (let* ((max (1- (expt 2 (1- b))))
               (min (- (expt 2 (1- b)))))
          (values min max))
        (values 0 (1- (expt 2 b))))))

(defun narrowing-p (from to)
  (or
   ;; целые: меньше разрядность или смена signed→unsigned с потерей
   (and (member (type-info-kind from) '(:int :uint))
        (member (type-info-kind to) '(:int :uint))
        (or (< (type-info-bits to) (type-info-bits from))
            (and (type-info-is-signed from)
                 (not (type-info-is-signed to)))))
   ;; float -> int всегда потенциально с потерей
   (and (eq (type-info-kind from) :float)
        (member (type-info-kind to) '(:int :uint)))
   ;; double -> float (снижение точности)
   (and (eq (type-info-kind from) :float)
        (eq (type-info-kind to) :float)
        (< (type-info-bits to) (type-info-bits from)))))

(defun clamp-int-expr (term to-info)
  (multiple-value-bind (min max) (int-bounds to-info)
    ;; Isabelle: min (max x MIN) MAX
    (format nil "(min (max (~a) ~a) ~a)" term min max)))

(defun c-mod-expr (term bits)
  (let ((modulus (expt 2 bits)))
    (format nil "(~a mod ~a)" term modulus)))

(defun float->int-expr (term)
  (format nil "(floor (~a))" term))

(defun bool->int-expr (term)
  (format nil "(if ~a then 1 else 0)" term))

(defun to-bool-expr (term from-type)
    (if (eq (type-info-kind from-type) :float)
            (format nil "((~a \\<noteq> 0.0) :: bool)" term)
            (format nil "((~a \\<noteq> 0) :: bool)" term)))

(defun make-isabelle-cast (type pretype term)
  (let* ((to   (lookup-info type))
         (from (lookup-info pretype))
         (to-kind (type-info-kind to))
         (from-kind (type-info-kind from))
         (bits (type-info-bits to)))

    (cond
        ((and (eq to-kind from-kind)
            (= (type-info-bits to) (type-info-bits from)))
            term)
        ((eq to-kind :bool)
            (to-bool-expr term from))
        ((not (narrowing-p from to))
            term)
        ((and (eq (type-info-kind from) :float) (member (type-info-kind to) '(:int :uint)))
            (format nil "(~a mod ~a)"
               (float->int-expr term)
               (expt 2 bits)))
        ((member to-kind '(:int :uint))
            (format nil "(~a mod ~a)" term (expt 2 bits)))
        ((eq to-kind :float)
            term)
        (t
            term))))

(aclosure c :attribute "print" :type "cast operation" :stage nil 
    :instance i 
    :ap i "right" term 
    :do (clear-update-push-aclosure c :av "stage" 'term)
        (clear-update-eval-aclosure c :av "instance" term))

(aclosure c :attribute "print" :type "cast operation" :stage 'term 
    :value term 
    :instance i 
    :ap i "type" ty 
    :ap i "pretype" pty 
    :do (make-isabelle-cast pty ty term))

(aclosure  c :attribute "print" :type "pstate compare" :stage nil
    :agent a
    :instance i 
    :ap i "state" state
    :ap i "process" process 
    :ap i "pstate" pstate
    :do (if (is-instance state "blank program state")(equal state "blank")
            (format nil "(getPstate ~a ~a = ~a)" (state-name a) process pstate)
            (error "Unknown state: ~a" state)))

(aclosure c :attribute "print" :type "implication" :stage nil 
    :instance i 
    :ap i "left" left 
    :do (clear-update-push-aclosure c :av "stage" 'left)
        (clear-update-eval-aclosure c :av "instance" left))

(aclosure c :attribute "print" :type "implication" :stage left 
    :instance i 
    :ap i "right" right 
    :value left
    :do (clear-update-push-aclosure c :av "stage" 'right :av "left" left)
        (clear-update-eval-aclosure c :av "instance" right))

(aclosure c :attribute "print" :type "implication" :stage right 
    :value right 
    :ap "left" left 
    :do (format nil "(~a \\<longrightarrow> ~a)" left right))

(aclosure c :attribute "print" :type "conjunction" :stage nil 
    :instance i 
    :ap i "formulas" formulas 
    :do (update-push-aclosure c :av "stage" 'iter :av "rest" (cdr formulas) )
        (clear-update-eval-aclosure c :av "instance" (car formulas)))
(aclosure c :attribute "print" :type "conjunction" :stage 'iter 
    :ap "rest" rst 
    :value formula
    :ap "collected" coll 
    :do (if rst 
            (progn (update-push-aclosure c :av "stage" 'iter :av "rest" (cdr rst) :av "collected" (cons formula coll))
                (clear-update-eval-aclosure c :av "instance" (car rst)))
            (format nil "(~{~A ~^\\<and> ~})" (reverse (cons formula coll))))
    )

(aclosure c :attribute "print" :type "disjunction" :stage nil 
    :instance i 
    :ap i "formulas" formulas 
    :do (update-push-aclosure c :av "stage" 'iter :av "rest" (cdr formulas) )
        (clear-update-eval-aclosure c :av "instance" (car formulas)))
(aclosure c :attribute "print" :type "disjunction" :stage 'iter 
    :ap "rest" rst 
    :value formula
    :ap "collected" coll 
    :do (if rst 
            (progn (update-push-aclosure c :av "stage" 'iter :av "rest" (cdr rst) :av "collected" (cons formula coll))
                (clear-update-eval-aclosure c :av "instance" (car rst)))
            (format nil "(~{~A ~^\\<and> ~})" (reverse (cons formula coll)))))

(aclosure c :attribute "print" :type "process activity" :stage nil 
    :instance i 
    :ap i "state" state
    :do (clear-update-push-aclosure c :av "stage" 'state)
        (clear-update-eval-aclosure c :av "instance" state))
(aclosure c :attribute "print" :type "process activity" :stage 'state 
    :value state
    :instance i 
    :ap i "process" process 
    :ap i "activity" activity
    :do (cond 
            ((equal activity 'active)
                (format nil "(getPstate ~a ~a \\<noteq> ''stop'')\\<and>(getPstate ~a ~a \\<noteq> ''error'')" state process))
            ((equal activity 'stop)
                (format nil "(getPstate ~a ~a = ''stop'')" state process))
            ((equal activity 'error)
                (format nil "(getPstate ~a ~a = ''error'')" state process))
            ((equal activity 'inactive)
                (format nil "(getPstate ~a ~a = ''stop'')\\<or>(getPstate ~a ~a = ''error'')" state process))
            ((equal activity 'nonstop)
                (format nil "(getPstate ~a ~a \\<noteq> ''stop'')" state process))
            ((equal activity 'active)
                (format nil "(getPstate ~a ~a \\<noteq> ''error'')" state process))))


(aclosure c :attribute "print" :type "process activity block" :stage nil 
    :instance i 
    :do (update-push-aclosure c :av "stage" 'iter :av "rest" (cdr i) )
        (clear-update-eval-aclosure c :av "instance" (car i)))
(aclosure c :attribute "print" :type "process activity block" :stage 'iter 
    :ap "rest" rst 
    :value formula
    :ap "collected" coll 
    :do (if rst 
            (progn (update-push-aclosure c :av "stage" 'iter :av "rest" (cdr rst) :av "collected" (cons formula coll))
                (clear-update-eval-aclosure c :av "instance" (car rst)))
            (format nil "(~{~A ~^\\<and> ~})" (reverse (cons formula coll)))))

(aclosure c :attribute "print" :type "arg name" :stage nil
    :instance i 
    :do i)

(aclosure c :attribute "print" :type "forall" :stage nil 
    :instance i 
    :ap i "formula" formula 
    :do (clear-update-push-aclosure c :av "stage" 'formula)
        (clear-update-eval-aclosure c :av "instance" formula))
(aclsoure c :attribute "print" :type "forall" :stage 'formula
    :value val
    :instance i 
    :ap i "args" args
    :p (format nil "~{~a ~}" args) new-args
    :do (format nil "(\\<forall>~a.~a)" new-args val))

(aclosure c :attribute "print" :type "exists" :stage nil 
    :instance i 
    :ap i "formula" formula 
    :do (clear-update-push-aclosure c :av "stage" 'formula)
        (clear-update-eval-aclosure c :av "instance" formula))
(aclsoure c :attribute "print" :type "exists" :stage 'formula
    :value val
    :instance i 
    :ap i "args" args
    :p (format nil "~{~a ~}" args) new-args
    :do (format nil "(\\<exists>~a.~a)" new-args val))

(aclsoure c :attribute "print" :type "ltime check" :stage nil
    :instance i 
    :ap i "state" state 
    :do (clear-update-push-aclosure c :av "stage" 'state)
        (clear-update-eval-aclosure c :av "instance" state))
(aclosure c :attribute "print" :type "ltime check" :stage 'state
    :value state
    :instance i
    :ap i "compare val" cval
    :do (clear-update-push-aclosure c :av "stage" 'cval :av "state" state)
        (clear-update-eval-aclosure c :av "instance" cval))
(aclosure c :attribute "print" :type "ltime check" :stage 'state
    :value cval 
    :ap "state" state
    :instance i
    :ap i "process" process
    :ap i "exceed" exceed
    :do (if exceed 
            (format nil "(ltime ~a ~a) \\<ge> ~a" state process cval)
            (format nil "(ltime ~a ~a) < ~a" state process cval)))

(aclosure c :attribute "print" :type "reset" :stage nil 
    :instance i 
    :ap i "state" state
    :do (clear-update-push-aclosure c :av "stage" 'state)
        (clear-update-eval-aclosure c :av "instance" state))
(aclosure c :attribute "print" :type "reset" :stage 'state 
    :value state 
    :instance i 
    :ap i "process" process
    :do (format nil "(reset ~a ~a)" state process))

(aclosure c :attribute "print" :type "to env" :stage nil 
    :instance i 
    :ap i "state" state
    :do (clear-update-push-aclosure c :av "stage" 'state)
        (clear-update-eval-aclosure c :av "instance" state))
(aclosure c :attribute "print" :type "to env" :stage 'state 
    :value state 
    :do (format nil "(toEnv ~a)" state))

(aclosure c :attribute "print" :type "pstate setter" :stage nil 
    :instance i 
    :ap i "state" state
    :do (clear-update-push-aclosure c :av "stage" 'state)
        (clear-update-eval-aclosure c :av "instance" state))
(aclosure c :attribute "print" :type "pstate setter" :stage 'state 
    :value state 
    :instance i 
    :ap i "process" process
    :ap i "pstate" pstate
    :do (format nil "(setPstate ~a ~a ~a)" state process pstate))

(mot "inv plug" :at "num" int)

;(mot "state notupdating formula" (uniont "forall" "exists" "ltime check" "term" "implication" "inv plug" "conjunction" "disjunction" "process activity" "process activity block"))

;(mot "state updating formula" (uniont "program state" "pstate setter" "reset" "to env"))

;(mot "formula" (uniont "state notupdating formula" "state updating formula"))

(aclosure c :attribute "print" :type "vc lemma" :stage nil 
    :instance i 
    :ap i "precondition" precondition
    :do (clear-update-push-aclosure c :av "stage" 'precondition)
        (clear-update-eval-aclosure c :av "instance" precondition))

(aclosure c :attribute "print" :type "vc lemma" :stage 'precondition 
    :instance i 
    :ap i "steps" steps
    :value precondition
    :do (clear-update-push-aclosure c :av "stage" 'steps :av "precondition" precondition :av "current" (car steps) :av "rest" (cdr steps))
        (clear-update-eval-aclosure c :av "instance" (car steps)))

(aclosure c :attribute "print" :type "vc lemma" :stage 'steps
    :ap "steps" steps 
    :ap "current" cur
    :value val
    :agent a
    :ap "collected" coll
    :instance i 
    :ap i "postcondition" post
    :p (if (is-instance cur "state updating formula")
            (progn (aset a "state num" (+ (aget a "state num") 1))
                (format nil "\"~a = ~a\"" (state-name a) val))
            (format nil "\"~a\"" val)) new-val
    :do (if steps 
            (progn (update-push-aclosure c :av "stage" 'steps :av "current" (car steps) :av "rest" (cdr steps) :av "collected" (cons new-val coll))
                (clear-update-eval-aclosure c :av "instance" (car steps)))
            (progn (update-push-aclosure c :av "stage" 'postcondition :av "collected" (cons new-val coll))
                (clear-update-eval-aclosure c :av "instance" post))))

(aclosure c :attribute "print" :type "vc lemma" :stage 'postcondition 
    :instance i 
    :ap "collected" coll
    :ap "precondition" precondition
    :value postcondition
    :do (format nil "lemma \n assume ~a~%~{and ~a~%~}shows ~a" pre steps post))

(defun create-vc-theory (name content) 
    (format nil "theory ~a \n
    imports Main Hol.Real Reflex Requirements\n
    begin\n\n 
    ~a \n\n
    end\n" name content))