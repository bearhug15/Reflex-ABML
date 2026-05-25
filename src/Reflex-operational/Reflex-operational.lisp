(uiop:define-package Reflex-semantics
  (:use #:cl))
(in-package #:Reflex-semantics)


(mot "env"
    :at "agents" (listt "agent")
    :at "aclosures" (cot :amap "agent" (listt cot))
    :at "variable type" (cot :amap "variable name" "type")
    :at "port type" (cot :amap "port name" "port type")
    :at "input variables" (cot :amap "variable name" "port name")
    :at "output variables" (cot :amap "variable name" "port name")
    :at "variable init" (cot :amap "variable name" "reflex init")
    :at "variable direct" (cot :amap "variable name" bool)
    :at "process states names" (cot :amap "process name" (listt "state name"))
    :at "struct fields" (cot :amap "structure name" (listt "field name"))
    :at "struct types" (cot :amap "structure name" (cot :amap "field name" "type"))
    :at "enum value" (cot :amap "enum name" (cot :amap "constant name" "int"))
    :at "global variables" (cot :amap "node name" (listt "variable name"))
    :at "function" (cot :amap "function name" "function declaration")
    :atv "clock" nat 100
)

(mot "agent" 
    :at "variable value" (cot :amap "variable name" "reflex value")
    :at "process state" (cot :amap "process name" "state name")
    :at "process time" (cot :amap "process name" "natural constant")
    :at "current process" "process name"
    :at "current state" "state name"
    :at "process state offset" (mot :amap "process name" int)
    :at "processes to start" (listt "process name")
    :at "return" "reflex value"
    :at "value" "reflex value"
)

(typedef "reflex value" (uniont "defined value" "lvalue" ))
(typedef "defined value" (uniont "constant" "array value" "struct value"))
(cot "struct value" :amap "field name" "reflex value")
(typedef "array value" (listt "reflex value"))
(mot "lvalue" :av "name" "string")

(aclosure c :attribute "opsem" :type "time constant" :stage nil
    :instance i 
  :do (let ((days (aget i "d"))
            (hours (aget i "h"))
            (minutes (aget i "m"))
            (seconds (aget i "s"))
            (milis (aget i "ms")))
        (+ (if milis milis 0)
            (* (+ (if seconds seconds 0)
            (* (+ (if minutes minutes 0)
                (* (+ (if hours hours 0)
                (* (if days days 0) 24)) 60)) 60)) 1000))))


(aclosure c :attribute "opsem" :type "number constant" :stage nil
    :instance i
    :do i)

(aclosure c :attribute "opsem" :type "char constant" :stage nil
    :instance i
    :do i)

(aclosure c :attribute "opsem" :type "string constant" :stage nil
    :instance i
    :do i)

(aclosure c :attribute "opsem" :type "element access" :stage nil
    :instance i 
    :ap i "variable" name 
    :ap i "accesses" rst 
    :agent a 
    :do (if (and (not (nil rst)) (> (length rst) 0)) 
            (update-push-aclosure c :av "stage" 'access :av "current" (car rst) :av "rest" (cdr rst) :av "values" (aget a (aseq "variable value" "name")))
            (if (aget a (aseq "variable direct" name)) 
                (mo "lvalue" :av "name" (aget i "name"))
                (read-input-value env a name)))
)

(aclosure c :attribute "opsem" :type "element access" :stage 'access
    :instance i 
    :ap "current" cur
    :ap "rest" rst
    :ap "values" vals 
    :ap "path" path
    :do
    (match :t cur "field name" :do 
        (let ((val (aget vals cur)))
            (if rst 
                (update-push-aclosure c :av "stage" 'access :av "current" (car rst) :av "rest" (cdr rst) :av "values" val :av "path" (cons cur path))
                val))
    )               
    (match :t cur "expression" :do 
        (update-push-aclosure c :av "stage" 'access-act)
        (clear-update-eval-aclosure c :av "instance" cur))
)
(aclosure c :attribute "opsem" :type "element access" :stage 'access-act
    :instance i 
    :ap "rest" rst
    :ap "current" cur
    :ap "rest" rst
    :ap "values" vals 
    :ap "path" path
    :value val
    :agent a
    :ap i "name" name 
    :do (let* ((actuated (act val a))
                (var (nth actuated vals)))
            (if (and (<= 0 actuated) (< actuated (get-array-size env name (reverse path))))
                (if rest
                    (update-push-aclosure c :av "stage" 'access :av "current" (car rest) :av "rest" (cdr rest) :av "values" var :av "path" (cons actuated path))
                    var)
                (make-error env a "Array index out of bounds")))
)

(aclosure c :attribute "opsem" :type "enum element access" :stage nil
    :instance i 
    :env env 
    :ap i "name" name 
    :ap i "field" fname
    :do (aget env (aseq "enum values" name fname))
)

(aclosure c :attribute "opsem" :type "common binary expression" :stage nil
    :instance i
    :ap i "left" left 
    :do (progn (update-push-aclosure c :av "stage" 'left)
            (clear-update-eval-aclosure c :av "instance" left))
)
(aclosure c :attribute "opsem" :type "common binary expressions" :stage 'left
    :instance i
    :value left
    :ap i "right" right 
    :do (progn (update-push-aclosure c :av "stage" 'right :av "left" left)
            (clear-update-eval-aclosure c :av "instance" right))
)
(aclosure c :attribute "opsem" :type "common binary expressions" :stage 'right
    :instance i
    :agent a
    :ap "left" left
    :value right  
    :do (def-bin-op (aget i "op") (act left a) (act right a))
)

(aclosure c :attribute "opsem" :type "division binary expressions" :stage nil
    :instance i
    :ap i "left" left
    :do (progn (update-push-aclosure c :av "stage" 'left)
            (clear-update-eval-aclosure c :av "instance" left))
)
(aclosure c :attribute "opsem" :type "division binary expressions" :stage 'left
    :instance i
    :value left
    :ap i "right" right
    :do (progn (update-push-aclosure c :av "stage" 'right :av "left" left)
            (clear-update-eval-aclosure c :av "instance" right))
)
(aclosure c :attribute "opsem" :type "division binary expressions" :stage 'right
    :instance i
    :agent a 
    :env env 
    :value right 
    :ap c "left" left
    :p (act left a) left
    :p (act right a) right 
    :do (if (= right 0)
                (make-error env a "Division by zero")
                (if (string= (aget i "op") "/")
                    (/ left right)
                    (mod left right)))
)

(aclosure c :attribute "opsem" :type "conjunction binary expression" :stage nil
    :instance i
    :ap i "left" left 
    :do (progn (update-push-aclosure c :av "stage" 'left)
            (clear-update-eval-aclosure c :av "instance" left))
)
(aclosure c :attribute "opsem" :type "conjunction binary expression" :stage 'left
    :instance i
    :value val 
    :agent a
    :ap i "right" right
    :p (act val a) left
    :do (if (or (= left 'false) (= left 0) (= left 0.0))
            'false
            (clear-update-eval-aclosure c :av "instance" right))
)
(aclosure c :attribute "opsem" :type "disjunction binary expression" :stage nil
    :instance i
    :ap i "left" left 
    :do (progn (update-push-aclosure c :av "stage" 'left)
            (clear-update-eval-aclosure c :av "instance" left))
)
(aclosure c :attribute "opsem" :type "disjunction binary expression" :stage 'left
    :instance i
    :value val 
    :agent a
    :ap i "right" right
    :p (act val a) left
    :do (if (or (= left 'true) (/= left 0) (/= left 0.0))
            'true
            (clear-update-eval-aclosure c :av "instance" right))
)

(aclosure c :attribute "opsem" :type "cast" :stage nil
    :instance i
    :ap i "expression" expr
    :do (progn (update-push-aclosure c :av "stage" 'expr)
            (clear-update-eval-aclosure c :av "instance" expr))
)
(aclosure c :attribute "opsem" :type "cast" :stage 'expr
    :instance i
    :at i "type" rtype
    :agent a 
    :value val 
    :do 
    (match :t rtype "integer type" 
        :do (floor val))
    (match :t rtype "natural type"
        :do (if (>= val 0)
                (floor val)
                (+ (floor val) (aget i "type" "max value"))))
    (match :t rtype "bool type"
        :do (if (= val 0)
                'false
                'true))
    (match :t rtype "float type" 
        :do (+ val 0.0))
)

(aclosure c :attribute "opsem" :type "!." :stage nil
    :instance i
    :ap i "expression" operand
    :do (progn (update-push-aclosure c :av "stage" 'operand)
            (clear-update-eval-aclosure c :av "instance" operand))
)
(aclosure c :attribute "opsem" :type "!." :stage 'operand
    :value val 
    :agent a 
    :do (not (act val a))
)

(aclosure c :attribute "opsem" :type "-." :stage nil
    :instance i
    :ap i "expression" operand
    :do (progn (update-push-aclosure c :av "stage" 'operand)
            (clear-update-eval-aclosure c :av "instance" operand))
)
(aclosure c :attribute "opsem" :type "-." :stage 'operand
    :value val 
    :agent a 
    :do (- 0 (act val a))
)


(aclosure c :attribute "opsem" :type "~." :stage nil
    :instance i
    :ap i "expression" operand
    :do (progn (update-push-aclosure c :av "stage" 'operand)
            (clear-update-eval-aclosure c :av "instance" operand))
)
(aclosure c :attribute "opsem" :type "~." :stage 'operand
    :value val 
    :agent a 
    :do (lognot 0 (act val a))
)



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

(defun lookup-info (tname)
  (or (cdr (assoc tname *type-info-map* :test #'eq))
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
    ;(format nil "(min (max (~a) ~a) ~a)" term min max)
    (min (max term min) max)
    ))

(defun c-mod-expr (term bits)
  (let ((modulus (expt 2 bits)))
    (mod term modulus)
    ;(format nil "(~a mod ~a)" term modulus)
    ))

(defun float->int-expr (term)
    (floor term)
  ;(format nil "(floor (~a))" term)
)

(defun bool->int-expr (term)
    (if (= term 'true) 1 0)
  ;(format nil "(if ~a then 1 else 0)" term)
)

(defun to-bool-expr (term from-type)
    (if (eq (type-info-kind from-type) :float)
            (if (= term 0.0) 'true 'false)
            ;(format nil "((~a \\<noteq> 0.0) :: bool)" term)
            (if (= term 0) 'true 'false)
            ;(format nil "((~a \\<noteq> 0) :: bool)" term)
    ))


(aclosure c :attribute "opsem" :type "cast" :stage nil 
    :instance i
    :ap i "right" right 
    :do (update-push-aclosure c :av "stage" 'res)
        (clear-update-eval-aclosure c :av "insatnce" right)
)
(aclosure c :attribute "opsem" :type "cast" :stage 'res
    :value val 
    :instance i 
    :ap i "type" ty 
    :ap i (aseq "right" "restype") pretype
    :do (if pretype 
            (let* ((to (lookup-info type))
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
                        (mod (float->int-expr term) (expt 2 bits))
                        ;(format nil "(~a mod ~a)"
                        ;(float->int-expr term)
                        ;(expt 2 bits))
                    )
                    ((member to-kind '(:int :uint))
                        (mod term (expt 2 bits))
                        ;(format nil "(~a mod ~a)" term (expt 2 bits))
                    )
                    ((eq to-kind :float)
                        term)
                    (t
                        term)))
            (cond 
                ((is-instance ty "integer type")
                    (floor val))
                ((is-instance ty "natural type")
                    (if (> val 0)
                        (floor val)
                        0))
                ((is-instance ty "float type")
                    (* val 1.0))
                ((is-instance ty "boolean type")
                    (if val 
                        'true 
                        'false)))))

#|
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
|#

#|
(aclosure c :attribute "opsem" :type "=" :stage nil
    :instance i 
    :ap i "right" right
    :do (progn (update-push-aclosure c :av "stage" 'right)
            (clear-update-eval-aclosure c "instance" right))
)
(aclosure c :attribute "opsem" :type "=" :stage 'right
    :agent a
    :instance i 
    :value val
    :ap i "left" access 
    :ap access "variable" name 
    :ap access "accesses" rst
    :do (let ((var (aget a (aseq "variable name" name))))
            (if (and (not (nil rst)) (> (length rst) 0)) 
                (update-push-aclosure c :av "stage" 'access :av "current" (car rest) :av "rest" (cdr rest) :av "values" var :av "collected" nil :av "res" (act val a))
                (progn
                    (aset a (aseq "variable name" name) (act val a))
                    (mo "lvalue" :av name))))
)
(aclosure c :attribute "opsem" :type "=" :stage 'access
    :ap "current" cur 
    :ap "rest" rst 
    :ap "values" vals 
    :ap "collected" coll 
    :ap "res" res
    :do 
    (match :t cur "field name" :do 
        (let ((var (aget vals cur)))
            (if rst 
                (update-push-aclosure c :av "stage" 'access :av "current" (car rst) :av "rest" (cdr rst) :av "values" var :av "collected" (cons cur coll) )
                (progn (aset a (aseql (cons "variable value" (reverse (cons act-val coll)))) res)
                    res)))
    )               
    (match :t cur "expression" :do 
        (update-push-aclosure c :av "stage" 'access-act)
        (clear-update-eval-aclosure c :av "instance" cur))
)|#

(aclosure c :attribute "opsem" :type "common assignment" :stage nil
    :instance i 
    :ap i "right" right
    :ap i "left" access 
    :ap access "variable" name 
    :ap access "accesses" rst 
    :agent a
    :do (if (and (not (nil rst)) (> (length rst) 0)) 
                (update-push-aclosure c :av "stage" 'access :av "current" (car rst) :av "rest" (cdr rst) :av "values" var :av "collected" nil :av "collected values" nil :av "res" (act val a))
                (progn
                    (update-push-aclosure c :av "stage" 'right :av "cur var" (aget a "variable value" name))
                    (clear-update-eval-aclosure c "instance" right)))
)
(aclosure c :attribute "opsem" :type "common assignment" :stage 'access
    :instance i 
    :agent a 
    :value val
    :ap "current" cur
    :ap "rest" rst 
    :ap "values" vals 
    :ap "collected" coll
    :do 
    (match :t cur "field name" :do 
        (let ((var (aget vals cur)))
            (if rst 
                (update-push-aclosure c :av "stage" 'access :av "current" (car rst) :av "rest" (cdr rst) :av "values" var :av "collected" (cons cur coll) :av "collected values" (cons var collval))
                (progn (update-push-aclosure c :av "stage" 'right :av "cur var" var :av "collected" (cons cur coll))
                    (clear-update-eval-aclosure c "instance" right))
            ))
    )               
    (match :t cur "expression" :do 
        (update-push-aclosure c :av "stage" 'access-act)
        (clear-update-eval-aclosure c :av "instance" cur))
)
(aclosure c :attribute "opsem" :type "common assignment" :stage 'access-act
    :instance i 
    :agent a 
    :value val
    :ap "current" cur
    :ap "rest" rst 
    :ap "values" vals 
    :ap "collected" coll 
    :do (let ((act-val (act val a))
                (var (nth act-val vals)))
            (if (and (<= 0 act-val) (< act-val (length vals)))
                (if rest 
                    (update-push-aclosure c :av "stage" 'access :av "current" (car rst) :av "rest" (cdr rst) :av "values" var :av "collected" (cons act-val coll))
                    (progn (update-push-aclosure c :av "stage" 'right :av "cur var" var :av "collected" (cons act-val coll))
                        (clear-update-eval-aclosure c "instance" right))
                )
                (make-error env a "Array index out of bounds")))
)
(aclosure c :attribute "opsem" :type "common assignment" :stage 'right
    :instance i 
    :ap i "op" op
    :agent a 
    :value val
    :ap i "left" access 
    :ap access "variable" name 
    :ap access "accesses" rst 
    :ap "collected" coll
    :ap "cur var" cur-var
    :ap (def-com-assign op var (act val a)) res
    :do (if (nil coll)
            (progn
                (aset a (aseq "variable value" name) res)
                (if (aget env (aseq "variable direct" name))
                    (write-output-value env a name))
                (mo "lvalue" :av name))
            (progn 
                (aset a (aseql (cons "variable value" (cons name (reverse coll)))) res)
                res))
)

(aclosure c :attribute "opsem" :type "division assignment" :stage nil
    :instance i 
    :ap i "right" right
    :ap i "left" access 
    :ap access "variable" name 
    :ap access "accesses" rst 
    :do (if (and (not (nil rst)) (> (length rst) 0)) 
                (update-push-aclosure c :av "stage" 'access :av "current" (car rst) :av "rest" (cdr rst) :av "values" var :av "collected" nil :av "collected values" nil :av "res" (act val a))
                (progn
                    (update-push-aclosure c :av "stage" 'right :av "cur var" (aget a "variable value" name))
                    (clear-update-eval-aclosure c "instance" right)
                ))
)
(aclosure c :attribute "opsem" :type "division assignment" :stage 'right
    :instance i 
    :ap i "op" op
    :agent a 
    :value val
    :ap i "left" access 
    :ap access "variable" name 
    :ap access "accesses" rst 
    :ap "collected" coll
    :ap "cur var" cur-var
    :ap (act val a) val-res
    :do (if (= (val-res) 0)
            (make-error env a "Array index out of bounds")
            (let ((res (def-com-assign op var val-res)))
                (if (nil coll)
                    (progn
                        (aset a (aseq "variable value" name) res)
                        (if (aget env (aseq "variable direct" name))
                            (write-output-value env a name))
                        (mo "lvalue" :av name))
                    (progn 
                        (aset a (aseql (cons "variable value" (cons name (reverse coll)))) res)
                        res))))
)


(aclosure c :attribute "opsem" :type "++."
    :instance i 
    :do
    (match :av c "stage" nil :ap c "agent" a :ap i "left" access :ap access "variable" name :ap access "accesses" rest :do 
        (if (and (not (nil rest)) (> (length rest) 0)) 
                (update-push-aclosure c :av "stage" 'access :av "collected" nil :av "collected values" nil)
                (progn
                    (aset a (aseq "variable name" name) (+ (aget a (aseq "variable name" name)) 1))
                    (mo "lvalue" :av name)))
    )
    (match :av c "stage" 'access :ap c "current" cur :t cur "field name" :ap c "rest" rest :ap c "values" vals :ap c "collected" coll :ap c "collected values" collval :ap c "res" res :do 
        (let ((var (aget vals cur)))
            (if rest 
                (update-push-aclosure c :av "stage" 'access :av "current" (car rest) :av "rest" (cdr rest) :av "values" var :av "collected" (cons cur coll) :av "collected values" (cons var collval))
                (update-push-aclosure c :av "stage" 'unwind :av "res" (+ vals 1) :av "fin" (+ vals 1))))
    )               
    (match :av c "stage" 'access :ap c "current" cur :t cur "expression" :do 
        (update-push-aclosure c :av "stage" 'access-act)
        (clear-update-eval-aclosure c :av "instance" cur))
    (match :av c "stage" 'access-act :ap c "rest" rest :ap c "values" vals :ap c "agent" a :ap a "value" val :ap c "collected" coll :ap c "collected values" collval :ap c "res" res :do
        (let ((act-val (act val a))
                (var (nth act-val vals)))
            (if rest 
                (update-push-aclosure c :av "stage" 'access :av "current" (car rest) :av "rest" (cdr rest) :av "values" var :av "collected" (cons act-val coll) :av "collected values" (cons var collval))
                (update-push-aclosure c :av "stage" 'unwind :av "res" (+ vals 1) :av "fin" (+ vals 1)))))
    (match :av c "stage" 'unwind :ap c "rest" rest :ap c "values" vals :ap c "agent" a :ap a "value" val :ap c "collected" coll :ap c "collected values" collval :ap c "res" res 
    :ap i "left" access :ap access "variable" name :ap c "fin" fin :do 
        (if coll 
            (update-push-aclosure c :av "collected" (cdr coll) :av "collected values" (cdr collval) :av "res" (aset collval coll res))
            (progn (aset a (aseq "variable name" name) res)
                fin)))
)

(aclosure c :attribute "opsem" :type ".++"
    :instance i 
    :do 
    (match :av c "stage" nil :ap c "agent" a :ap i "left" access :ap access "variable" name :ap access "accesses" rest :do 
        (if (and (not (nil rest)) (> (length rest) 0)) 
                (update-push-aclosure c :av "stage" 'access :av "collected" nil :av "collected values" nil)
                (let ((prev (aget a (aseq "variable name" name))))
                    (aset a (aseq "variable name" name) (+ prev 1))
                    prev))
    )
    (match :av c "stage" 'access :ap c "current" cur :t cur "field name" :ap c "rest" rest :ap c "values" vals :ap c "collected" coll :ap c "collected values" collval :do 
        (let ((var (aget vals cur)))
            (if rest 
                (update-push-aclosure c :av "stage" 'access :av "current" (car rest) :av "rest" (cdr rest) :av "values" var :av "collected" (cons cur coll) :av "collected values" (cons var collval))
                (update-push-aclosure c :av "stage" 'unwind :av "res" (+ vals 1) :av "fin" vals)))
    )               
    (match :av c "stage" 'access :ap c "current" cur :t cur "expression" :do 
        (update-push-aclosure c :av "stage" 'access-act)
        (clear-update-eval-aclosure c :av "instance" cur))
    (match :av c "stage" 'access-act :ap c "rest" rest :ap c "values" vals :ap c "agent" a :ap a "value" val :ap c "collected" coll :ap c "collected values" collval :do
        (let ((act-val (act val a))
                (var (nth act-val vals)))
            (if rest 
                (update-push-aclosure c :av "stage" 'access :av "current" (car rest) :av "rest" (cdr rest) :av "values" var :av "collected" (cons act-val coll) :av "collected values" (cons var collval))
                (update-push-aclosure c :av "stage" 'unwind :av "res" (+ vals 1) :av "fin" vals))))
    (match :av c "stage" 'unwind :ap c "rest" rest :ap c "values" vals :ap c "agent" a :ap a "value" val :ap c "collected" coll :ap c "collected values" collval :ap c "res" res 
    :ap i "left" access :ap access "variable" name :ap c "fin" fin :do 
        (if coll 
            (update-push-aclosure c :av "collected" (cdr coll) :av "collected values" (cdr collval) :av "res" (aset collval coll res))
            (progn (aset a (aseq "variable name" name) res)
                fin)))
)

(aclosure c :attribute "opsem" :type "--."
    :instance i 
    :do 
    (match :av c "stage" nil :ap c "agent" a :ap i "left" access :ap access "variable" name :ap access "accesses" rest :do 
        (if (and (not (nil rest)) (> (length rest) 0)) 
                (update-push-aclosure c :av "stage" 'access :av "collected" nil :av "collected values" nil)
                (progn
                    (aset a (aseq "variable name" name) (- (aget a (aseq "variable name" name)) 1))
                    (mo "lvalue" :av name)))
    )
    (match :av c "stage" 'access :ap c "current" cur :t cur "field name" :ap c "rest" rest :ap c "values" vals :ap c "collected" coll :ap c "collected values" collval :do 
        (let ((var (aget vals cur)))
            (if rest 
                (update-push-aclosure c :av "stage" 'access :av "current" (car rest) :av "rest" (cdr rest) :av "values" var :av "collected" (cons cur coll) :av "collected values" (cons var collval))
                (update-push-aclosure c :av "stage" 'unwind :av "res" (- vals 1) :av "fin" (- vals 1))))
    )               
    (match :av c "stage" 'access :ap c "current" cur :t cur "expression" :do 
        (update-push-aclosure c :av "stage" 'access-act)
        (clear-update-eval-aclosure c :av "instance" cur))
    (match :av c "stage" 'access-act :ap c "rest" rest :ap c "values" vals :ap c "agent" a :ap a "value" val :ap c "collected" coll :ap c "collected values" collval :do
        (let ((act-val (act val a))
                (var (nth act-val vals)))
            (if rest 
                (update-push-aclosure c :av "stage" 'access :av "current" (car rest) :av "rest" (cdr rest) :av "values" var :av "collected" (cons act-val coll) :av "collected values" (cons var collval))
                (update-push-aclosure c :av "stage" 'unwind :av "res" (- vals 1) :av "fin" (- vals 1)))))
    (match :av c "stage" 'unwind :ap c "rest" rest :ap c "values" vals :ap c "agent" a :ap a "value" val :ap c "collected" coll :ap c "collected values" collval :ap c "res" res 
    :ap i "left" access :ap access "variable" name :ap c "fin" fin :do 
        (if coll 
            (update-push-aclosure c :av "collected" (cdr coll) :av "collected values" (cdr collval) :av "res" (aset collval coll res))
            (progn (aset a (aseq "variable name" name) res)
                fin)))
)

(aclosure c :attribute "opsem" :type ".--"
    :instance i 
    :do 
    (match :av c "stage" nil :ap c "agent" a :ap i "left" access :ap access "variable" name :ap access "accesses" rest :do 
        (if (and (not (nil rest)) (> (length rest) 0)) 
                (update-push-aclosure c :av "stage" 'access :av "collected" nil :av "collected values" nil)
                (let ((prev (aget a (aseq "variable name" name))))
                    (aset a (aseq "variable name" name) (- prev 1))
                    prev))
    )
    (match :av c "stage" 'access :ap c "current" cur :t cur "field name" :ap c "rest" rest :ap c "values" vals :ap c "collected" coll :ap c "collected values" collval :do 
        (let ((var (aget vals cur)))
            (if rest 
                (update-push-aclosure c :av "stage" 'access :av "current" (car rest) :av "rest" (cdr rest) :av "values" var :av "collected" (cons cur coll) :av "collected values" (cons var collval))
                (update-push-aclosure c :av "stage" 'unwind :av "res" (- vals 1) :av "fin" vals)))
    )               
    (match :av c "stage" 'access :ap c "current" cur :t cur "expression" :do 
        (update-push-aclosure c :av "stage" 'access-act)
        (clear-update-eval-aclosure c :av "instance" cur))
    (match :av c "stage" 'access-act :ap c "rest" rest :ap c "values" vals :ap c "agent" a :ap a "value" val :ap c "collected" coll :ap c "collected values" collval :do
        (let ((act-val (act val a))
                (var (nth act-val vals)))
            (if rest 
                (update-push-aclosure c :av "stage" 'access :av "current" (car rest) :av "rest" (cdr rest) :av "values" var :av "collected" (cons act-val coll) :av "collected values" (cons var collval))
                (update-push-aclosure c :av "stage" 'unwind :av "res" (- vals 1) :av "fin" vals))))
    (match :av c "stage" 'unwind :ap c "rest" rest :ap c "values" vals :ap c "agent" a :ap a "value" val :ap c "collected" coll :ap c "collected values" collval :ap c "res" res 
    :ap i "left" access :ap access "variable" name :ap c "fin" fin :do 
        (if coll 
            (update-push-aclosure c :av "collected" (cdr coll) :av "collected values" (cdr collval) :av "res" (aset collval coll res))
            (progn (aset a (aseq "variable name" name) res)
                fin)))
)

(aclosure c :attribute "opsem" :type "active" :stage nil
    :ap "process" process
    :agent a
    :do (if (and (not (equal (aget a (aseq "process state" process)) "stop"))
                (not (equal (aget a (aseq "process state" process)) "error")))
            'true
            'false)
)
(aclosure c :attribute "opsem" :type "inactive" :stage nil
    :ap "process" process
    :agent a
    :do (if (or (equal (aget a (aseq "process state" process)) "stop")
                (equal (aget a (aseq "process state" process)) "error"))
            'true 
            'false)
)
(aclosure c :attribute "opsem" :type "rstop" :stage nil
    :ap "process" process
    :agent a
    :do (if (equal (aget a (aseq "process state" process)) "stop")
            'true 
            'false )
)
(aclosure c :attribute "opsem" :type "rerror" :stage nil
    :ap "process" process
    :agent a
    :do (if (equal (aget a (aseq "process state" process)) "error")
            'true 
            'false)
)

(aclosure c :attribute "opsem" :type "process state checking" :stage nil
    :instance i 
    :ap i "process" process 
    :ap i "activity" act 
    :do (clear-update-eval-aclosure c :av "instance" act :av "process" process)
)

(aclosure c :attribute "opsem" :type "function call" :stage nil 
    :instance i 
    :ap i "args" args 
    :do (update-push-aclosure c :av "stage" 'args :av "rest" rst))

(aclosure c :attribute "opsem" :type "function call" :stage 'args 
    :ap "rest" rst 
    :ap "args" args
    :value val
    :do (if rst 
            (progn (update-push-aclosure c :av "stage" 'args :av "rest" (cdr rst) :av "args" (cons val args))
                (clear-update-eval-aclosure c :av "instance" (car rst)))
            (if val 
                (update-push-aclosure c :av "stage" 'prepare :av "args" (reverse (cons val args)))
                (update-push-aclosure c :av "stage" 'prepare))))
(aclosure c :attribute "opsem" :type "function call" :stage 'args 
    :instance i 
    :ap i "name" func-name
    :ap "args" args 
    :env env 
    :ap env (aseq "function" name) function-decl
    :agent a 
    :do (update-push-aclosure c :av "stage" 'end)
        (clear-update-eval-aclosure c :av "instance" function-decl :av "args" args))

(aclsoure c :attribute "opsem" :type "function call" :stage 'end 
    :agent a 
    :ap a "return" ret 
    :do (aset a "return" nil)
        ret)

(aclosure c :attribute "opsem" :type "function decl" :stage nil 
    :instance i 
    :ap i "params" fargs
    :do (update-push-aclosure c :av "stage" 'fargs :av 'fargs :av "fargs" fargs))
(aclosure c :attribute "opsem" :type "function decl" :stage 'fargs 
    :ap "args" args
    :ap "fargs" fargs
    :agent a
    :instance i
    :ap i "body" body
    :do (if fargs 
            (progn (aset a (aseq "variable value" (car fargs)) (car args))
                (update-push-aclosure c :av "fargs" (cdr fargs) :av "args" (cdr args)))
            (progn (update-push-aclosure c :av "stage" 'function-end)
                (clear-update-eval-aclosure c :av "instance" body))))

(aclosure c :attribute "opsem" :type "function decl" :stage 'function-end)

(aclsoure c :attribute "opsem" :type "return statement" :stage nil
    :instance i 
    :ap i "expression" expr 
    :do (update-push-aclosure c :av "stage" 'expr)
        (clear-update-eval-aclosure c :av "insatnce" expr))
(aclsoure c :attribute "opsem" :type "return statement" :stage 'expr 
    :value val 
    :agent a
    :env env 
    :ap env (aseq "aclosures" a) stack
    :do (aset a "return" val)
        (aset env (aseq "aclosures" a) 
            (member nil stack :test (lambda (n c) (= (aget c"stage") 'function-end)))))


(aclosure c :attribute "opsem" :type "array init" :stage nil 
    :instance i 
    :do (update-push-aclosure c :av "stage" 'exprs :av "exprs" (cdr i))
        (clear-update-eval-aclosure c "instance" (car i))
)
(aclosure c :attribute "opsem" :type "array init" :stage 'exprs 
    :ap "exprs" exprs
    :do (if exprs 
            (progn (update-push-aclosure :av "exprs" (cdr exprs))
                (clear-update-eval-aclosure c "instance" (car exprs)))
            (reverse exprs))
)


(aclosure c :attribute "opsem" :type "struct init" :stage nil 
    :instance i 
    :do (update-push-aclosure c :av "stage" 'fields :av "fields" (attributes i) :av "new init" (co "struct value"))
        (clear-update-eval-aclosure c iob (aget i (car (attributes i))))
)
(aclosure c :attribute "opsem" :type "struct init" :stage nil 
    :instance i 
    :ap "fields" fields 
    :ap "new init" ninit 
    :value val  
    :do (if (> (length fields) 1)
            (progn 
                (update-push-aclosure c :av "fields" (cdr fields) :av "new init" (aset ninit (car fields) val))
                (clear-update-eval-aclosure c iob (aget i (car (cdr fields)))))
            (aset ninit (car fields) val))
)        


;Transformations: statements




(aclosure c :attribute "opsem" :type "reset timer" :stage nil
    :instance i
    :agent a 
    :do (aset a "process time" (aget a "current process") 0)
)

(aclosure c :attribute "opsem" :type "set state" :stage nil
    :instance i
    :agent a 
    :env env 
    :ap i "state" state 
    :ap a "current process" proc
    :do (aset a (aseq "process state" proc ) state)
        (aset a (aseq "process time" proc ) 0)
        (aset a (aseq "process state offset" proc ) nil)
)

(aclosure c :attribute "opsem" :type "restart process" :stage nil
    :instance i
    :agent a 
    :ap a "current process" cur-proc
    :do (aset a :av "processes to start" (cons (aget a "processes to start") cur-proc) 
            :av "processes state" cur-proc (first-state a cur-proc) 
            :av "process time" cur-proc 0)
)

(aclosure c :attribute "opsem" :type "start process" :stage nil
    :instance i 
    :ap i "process" proc
    :agent a
    :ap a "current process" cur-proc
    :do (if (equal proc cur-proc)
            (clear-update-eval-aclosure c :av "instance" (mo "restart process"))
            (aset a :av "processes to start" (cons (aget a "processes to start") proc) 
                :av "processes state" proc (first-state a proc) 
                :av "process time" proc 0))
)

(aclosure c :attribute "opsem" :type "stop current process" :stage nil
    :instance i
    :agent a 
    :ap a "current process" cur-proc 
    :do (aset a
            :av "processes state" cur-proc 'stop
            :av "process time" cur-proc 0)
)

(aclosure c :attribute "opsem" :type "stop process" :stage nil
    :instance i 
    :agent a
    :ap a "current process" cur-proc 
    :ap i "process" proc 
    :do (if (equal proc cur-proc)
            (clear-update-eval-aclosure c :av "instance" (mo "stop current process"))
            (aset a
                :av "processes state" proc 'stop
                :av "process time" proc 0))
)

(aclosure c :attribute "opsem" :type "error current process" :stage nil
    :instance i
    :agent a 
    :ap a "current process" cur-proc 
    :do (aset a
            :av "processes state" cur-proc 'error
            :av "process time" cur-proc 0)
)

(aclosure c :attribute "opsem" :type "error process" :stage nil
    :instance i 
    :agent a 
    :ap a "current process" cur-proc 
    :ap i "process" proc 
    :do (if (equal proc cur-proc)
            (clear-update-eval-aclosure c :av "instance" (mo "error current process"))
            (aset a
                :av "processes state" proc 'error
                :av "process time" proc 0))
)

(aclosure c :attribute "opsem" :type "statement list" :stage nil
    :instance i 
    :do (update-push-aclosure c :av "stage" 'rest :av "rest" (cdr i))
        (clear-update-eval-aclosure c :av "instance" (car i))
)
(aclosure c :attribute "opsem" :type "statement list" :stage nil
    :ap "rest" rst
    :do (update-push-aclosure c :av "rest" (cdr rst))
        (clear-update-eval-aclosure c :av "instance" (car rst))
)

(aclosure c :attribute "opsem" :type "if then else statement" :stage nil 
    :instance i 
    :ap i "condition" env 
    :do (update-push-aclosure c :av "stage" 'condition)
        (clear-update-eval-aclosure c :av "instance" con)
)
(aclosure c :attribute "opsem" :type "if then else statement" :stage 'condition 
    :instance i
    :ap i "then" then 
    :ap i "else" else
    :agent a 
    :value val 
    :do (if (= (act val a) 'true)  
            (clear-update-eval-aclosure c :av "instance" then)
            (clear-update-eval-aclosure c :av "instance" else))
)

(aclosure c :attribute "opsem" :type "if then statement"
    :instance i 
    :do
    (match :av c "stage" nil :ap i "condition" env :do
        (progn (update-push-aclosure c :av "stage" 'condition)
            (clear-update-eval-aclosure c :av "instance" con)))
    (match :av c "stage" 'condition :ap i "then" then :ap c "agent" a :ap a "value" val :do
        (if (= (act val a) 'true)  
            (clear-update-eval-aclosure c :av "instance" then))))

(aclosure c :attribute "opsem" :type "switch statement" :stage nil 
    :instance i 
    :ap i "controlling expression" con
    :ap i "cases" cases
    :do (update-push-aclosure c :av "stage" 'condition :av "cases" cases)
        (clear-update-eval-aclosure c :av "instance" con)
)
(aclosure c :attribute "opsem" :type "switch statement" :stage 'condition  
    :value val 
    :ap "cases" cases 
    :agent a
    :do (update-push-aclosure c :av "stage" 'case-label :av "val" (act val a)))
(aclosure c :attribute "opsem" :type "switch statement" :stage 'case-lable  
    :ap "val" val 
    :ap "cases" cases 
    :p (car cases) cs 
    :do (if cases 
            (if (equal (aget cs "label") val)
                (clear-update-eval-aclosure c :av "instance" cs)
                (update-push-aclosure c :av "cases" (cdr cases)))
            (update-push-aclosure c :av "stage" 'default)) 
)
(aclosure c :attribute "opsem" :type "switch statement" :stage 'default
    :instance i   
    :ap i "default" def 
    :do (if def 
            (clear-update-eval-aclosure c :av "instance" def))
)

(aclosure c :attribute "opsem" :type "deafault statement" :stage nil
    :instance i 
    :ap i "statements" sts
    :do (clear-update-eval-aclosure c :av "instance" sts)    
)

(aclosure c :attribute "opsem" :type "case statement" :stage nil
    :instance i 
    :ap i "statements" sts 
    :do (clear-update-eval-aclosure c :av "instance" sts)      
)

(aclosure c :attribute "opsem" :type "statement block" :stage nil
    :instance i 
    :ap i "statements" sts
    :do (clear-update-eval-aclosure c :av "instance" sts)
)

(aclosure c :attribute "opsem" :type "expression statement" :stage nil
    :instance i 
    :do (clear-update-eval-aclosure c :av "instance" (aget i "expression")))

(aclosure c :attribute "opsem" :type "timeout statement"  :stage nil 
    :instance i 
    :ap i "controlling expression" expr 
    :do (update-push-aclosure c :av "stage" 'cond)
        (clear-update-eval-aclosure c :av "instance" expr)
) 
(aclosure c :attribute "opsem" :type "timeout statement"  :stage nil 
    :instance i 
    :ap i "statements" sts
    :agent a 
    :ap a "current process" cur-proc
    :value val
    :do (if (<= (act val a) 
            (aget a (aseq "process time" cur-proc))
            (clear-update-eval-aclosure c :av "instance" sts)))
)

(aclosure c :attribute "opsem" :type "for statement" :stage nil 
    :insatnce i 
    :ap i "init" init 
    :do (update-push-aclosure c :av "stage" 'init :av "init" (cdr init))
        (clear-update-eval-aclosure c :av "instance" (car init)))
(aclosure c :attribute "opsem" :type "for statement" :stage 'init 
    :ap "init" init 
    :do (if init 
            (progn (update-push-aclosure c :av "init" (cdr init))
                (clear-update-eval-aclosure c :av "instance" (car init)))
            (update-push-aclosure c :av "stage" 'condition)))
(aclosure c :attribute "opsem" :type "for statement" :stage 'condition 
    :insatnce i 
    :ap i "condition" cnd 
    :do (update-push-aclosure c :av "stage" 'iter)
        (clear-update-eval-aclosure c :av "instance" cnd)
)
(aclosure c :attribute "opsem" :type "for statement" :stage 'iter 
    :insatnce i 
    :value val
    :ap i "statement" stm 
    :do (if (equal val 'true) 
            (progn (update-push-aclosure c :av "stage" 'update)
                (clear-update-eval-aclosure c :av "instance" stm)))
)
(aclosure c :attribute "opsem" :type "for statement" :stage 'update 
    :insatnce i 
    :ap i "update" upd
    :do (update-push-aclosure c :av "stage" 'condition)
        (clear-update-eval-aclosure c :av "instance" upd)
)


(aclosure c :attribute "opsem" :type "wait" :stage nil
    :instance i 
    :do (clear-update-eval-aclosure c :av "instance" (aget i "condition")))
(aclosure c :attribute "opsem" :type "slice" :stage nil
    :instance i 
    :do nil)
(aclosure c :attribute "opsem" :type "wait on timeout" :stage nil
    :instance i 
    :do (clear-update-eval-aclosure c :av "instance" (aget i "condition")))


;Declaratioins 

(aclosure c :attribute "opsem" :type "statement variable declaration" :stage nil
    :instance i 
    :do (clear-update-eval-aclosure c :av "attribute" "opsem init" :av "instance" i)
)


(aclosure c :attribute "opsem" :type "state declaration" :stage nil 
    :instance i 
    :ap i "statements" sts 
    :agent a 
    :ap a "current process" cur-proc
    :p (aget a (aseq "process state offset" cur-proc)) offset
    :do (update-push-aclosure c :av "stage" 'statements :av "index" offset :av "length" (length sts))
)
(aclosure c :attribute "opsem" :type "state declaration" :stage 'statements 
    :instance i 
    :ap "index" index 
    :ap "length" len 
    :ap i "statements" sts 
    :do (if (< index len)
            (progn (if (is-instance (nth index sts) "barrier statement")
                        (update-push-aclosure c :av "stage" 'barrier)
                        (update-push-aclosure c :av "stage" 'statements :av "index" (+ index 1)))
                (clear-update-eval-aclosure c :av "instance" (nth index sts))))
)
(aclosure c :attribute "opsem" :type "state declaration" :stage 'barrier 
    :instance i
    :ap "index" index 
    :ap "length" len 
    :ap i "statements" sts 
    :ap (nth index sts) st 
    :value val 
    :agent a
    :ap a "current process" cur-proc
    :p (aget a (aseq "process state offset" cur-proc)) offset
    :do (match :t st "slice"
            :do (aset a (aseq "process state offset" cur-proc) (+ index 1))
                (aset a (aseq "process time" cur-proc) 0))
        (match :t st "wait" 
            :do (if (not (equal st (nth offset sts)))
                    (aset a (aseq "process time" cur-proc) 0))
                (if (equal val 'true)
                    (progn (update-push-aclosure c :av "stage" 'statements :av  index (+ index 1))
                        (aset a "process state offset" cur-proc (+ index 1)))
                    (aset a "process state offset" cur-proc index)))
        (match :t st "wait on timeout"  :ap st "controlling expression" expr
            :do (if (not (equal st (nth offset sts)))
                    (aset a (aseq "process time" cur-proc) 0))
                (if (equal val 'true)
                    (progn (update-push-aclosure c :av "stage" 'statements :av  index (+ index 1))
                        (aset a "process state offset" cur-proc (+ index 1)))
                    (progn (update-push-aclosure c :av "stage" 'timeout)
                        (clear-update-eval-aclosure c :av "instance" expr))))
)
(aclosure c :attribute "opsem" :type "state declaration" :stage 'timeout 
    :instance i 
    :ap i "statements" sts
    :ap "index" index 
    :value val 
    :agent a 
    :ap a "current process" cur-proc 
    :p (aget a (aseq "process time" cur-proc)) proc-time 
    :do (if (> val proc-time)
            (progn (aset a "process state offset" (aget a "current process") index) 
                (clear-update-eval-aclosure c :av "instance" sts))
            (aset a "process state offset" (aget a "current process") index)))

(aclosure c :attribute "opsem" :type "process declaration"
    :instance i 
    :ap i "name" name
    :ap i "states" states
    :agent a 
    :env env
    :p (find-if (lambda state (equal (aget state "name") (aget a "current state"))) states) state
    :do (aset a "current process" name)
        (aset a "current state" (aget a (aseq "process state" name)))   
        (if state 
            (progn (clear-update-eval-aclosure c :av "instance" state)
                (aset a "process time" (+ (aget a (aseq "process time" name)) (aget env "clock")))))
)

(defun read-input-value (env a name)
    (random 100))

(aclosure c :attribute "opsem" :type "program declaration" :stage nil
    :env env 
    :do (update-push-aclosure c :av "stage" 'init-input :av "input" (aget env "input variables"))
)
(aclosure c :attribute "opsem" :type "program declaration" :stage 'init-input
    :instance i
    :ap "input" input 
    :agent a 
    :env env
    :do (if input 
            (progn
                (update-push-aclosure c (cdr input))
                (aset a "variable value" (car input) (read-input-value (aget env "variable type" (car input)))))
            (update-push-aclosure c :av "stage" 'work :av "processes" (aget i "processes")))
)
(aclosure c :attribute "opsem" :type "program declaration" :stage 'work
    :ap "processes" processes 
    :p (car processes) proc
    :agent a
    :p (aget a (aseq "process state" (aget proc "name"))) proc-state
    :do (if proc
            (if (or (equal proc-state "stop") (equal proc-state "error"))
                (update-push-aclosure c :av "processes" (cdr processes))
                (progn (update-push-aclosure c :av "processes" (cdr processes))
                    (update-push-aclosure c :av "stage" 'init-started)
                    (clear-update-eval-aclosure c :av "instance" proc)))
            (update-push-aclosure c :av "stage" 'init-input :av "input" (aget env "input variables")))
)
(aclosure c :attribute "opsem" :type "program declaration" :stage 'init-started 
    :agent a 
    :do (update-push-aclosure c :av "stage" 'init-started-procs :av "procs to start" (aget a "processes to start"))
)
(aclosure c :attribute "opsem" :type "program declaration" :stage 'init-started-procs
    :instance i
    :ap "procs to start" procs-to-start 
    (if procs-to-start 
        (progn (update-push-aclosure c :av "index" (cdr procs-to-start))
                (clear-update-eval-aclosure c
                    :av "attribute" "opsem init" 
                    :av "instance" (find-if 
                                (lambda (process) (equal (aget process "name") (car procs-to-start))) 
                                (aget i "processes"))))
        (progn (aset a (aseq "processes to start") nil)
            (update-push-aclosure c :av "stage" 'init-input))) 
)
(aclosure c :attribute "opsem" :type "program declaration" :stage 'write-outputs 
    :env env 
    :agent a
    :ap "variables to write" vtw 
    :do (if vtw 
            (progn (update-push-aclosure c :av "variables to write" (cdr vtw)) 
                (write-output-value env a (car vtw)))
            (update-push-aclosure c :av "stage" 'init-input)))


(aclosure c :attribute "opsem prepare" :type "program declaration" 
    :instance i
    :do 
    (match :av c "stage" nil :do 
        (update-push-aclosure c :av "stage" 'named)
        (clear-update-eval-aclosure c :av "attribute" "map name" :av "instance" i))
    (match :av c "stage" 'named :do 
        (update-push-aclosure c :av "stage" 'casted)
        (clear-update-eval-aclosure c :av "attribute" "type spec" :av "instance" i))
    (match :av c "stage" 'casted :do 
        (update-push-aclosure c :av "stage" 'first-init)
        (clear-update-eval-aclosure c :av "attribute" "opsem decl" :av "instance" i))
    (match :av c "stage" 'first-init :ap c "env" env :do 
        (update-push-aclosure c :av "stage" 'init-input :av "input" (aget env "input variables"))
        (clear-update-eval-aclosure c :av "attribute" "opsem init" :av "instance" i)))



;opsem decl

(aclosure c :attribute "opsem decl" :type "constant declaration" :stage nil 
    :instance i 
    :ap i "expression" expr 
    :do (update-push-aclosure c :av "stage" 'val)
        (clear-update-eval-aclosure c :av "instance" expr)
)
(aclosure c :attribute "opsem decl" :type "constant declaration" :stage 'val 
    :instance i 
    :ap i "name" name :ap c "env" con
    :ap c "agent" a :ap a "value" val 
    :do (aset a (aseq "variable value" name) val)
)
        
(aclosure c :attribute "opsem decl" :type "simple variable declaration" :stage nil
    :instance i 
    :ap i "init" init :ap i "type" rtype :ap c "env" env 
    :do (update-push-aclosure c :av "stage" 'first :av "init" (if init init (type-default-val env rtype)))
)
(aclosure c :attribute "opsem decl" :type "simple variable declaration" :stage nil
    :instance i    
    :ap i "name" name :ap c "init" init :ap c "env" env :ap i "type" rtype 
    :do (aset env (aseq "variable init" name) init)
        (aset env (aseq "variable type" name) rtype)                  
)

(aclosure c :attribute "opsem decl" :type "array variable declaration"
    :instance i
    :do
    (match :av c "stage" nil :ap i "init" init :ap i "type" rtype :ap i "size" size :ap c "env" env :do 
        (update-push-aclosure c :av "stage" 'first :av "init" (if init init (type-default-val env rtype))))
    (match :av c "stage" 'first :ap i "name" name :ap c "init" init :ap c "env" env :ap i "type" rtype :ap i "size" size :do 
        (aset env (aseq "variable init" name) init)
        (aset env (aseq "variable type" name) rtype))
)

(aclosure c :attribute "opsem decl" :type "imported variable declaration" :stage nil
    :instance i 
    :do nil)

(aclosure c :attribute "opsem decl" :type "physical variable declaration" :stage nil
    :instance i 
    :env env
    :ap i "name" name 
    :ap i "type" rtype 
    :ap i "port" pname 
    :do (if (equal (aget env (aseq "port type" pname)) 'input)
            (progn (aset env "input variables" (adjoin (aget env "input variables") name))
                (aset env (aseq "variable type" name ) rtype ))
            (progn (aset env "output variables" (adjoin (aget env "input variables") name))
                (aset env (aseq "variable type" name ) rtype)))
)

(aclosure c :attribute "opsem decl" :type "structure declaration"
    :instance i 
    :do 
    (match :av c "stage" :ap i "fields" fields :ap i "name" name :do
        (update-push-aclosure c :av "stage" 'fields :av "index" 0 :av "length" (length fields)))
    (match :av c "stage" fields :ap i "fields" fields :ap i "name" name :ap c "index" index :ap c "length" len 
        :ap c "env" env :do 
        (if (< index len)
            (let ((field (aget fields index)))
                (progn (update-push-aclosure c :av "index" (+ index 1))
                (aset env (aseq "struct types" name (aget field "name")) (aget field "type"))))))
)

(aclosure c :attribute "opsem decl" :type "structure variable declaration" :stage nil
    :instance i 
    :ap i "name" name 
    :ap i "type" rtype 
    :ap i "init" init :do
    :env env 
    :do (aset env (aseq "variable type" name) rtype)
        (if init 
            (aset env (aseq "variable init" name) init)
            (aset env (aseq "variable init" name) (mo "struct init")))
)

(aclosure c :attribute "opsem decl" :type "enum declaration"
    :instance i 
    :do 
    (match :av c "stage" nil :ap i "fileds" fields :do 
        (update-push-aclosure c :av "stage" 'fields :av "index" 0 :av "length" (length fields) :av "last value" -1))
    (match :av c "stage" 'fields :ap i "fields" fields :ap c "index" index :ap fields "index" field 
        :ap c "length" len :ap c "last" value lv  :ap c "env" env :ap i 'name name :do 
        (if (< index len)
            (if (aget field "value")
                (progn (update-push-aclosure c :av "index" (+ index 1) :av "last value" (aget field "value"))
                    (aset env (aseq "enum value" name (aget field "name")) (aget field "value")))
                (progn (update-push-aclosure c :av "index" (+ index 1) :av "last value" (+ lv 1))
                    (aset env (aseq "enum value" name (aget field "name")) (+ lv 1)))))))

(aclosure c :attribute "opsem decl" :type "enum variable declaration" :stage nil
    :instance i 
    :env env 
    :ap i "init" init
    :ap i "type" rtype 
    :do (if init 
            (aset env (aseq "variable init" name) init)
            (aset env (aseq "variable init" name) (type-default-val env rtype)))
)

(aclosure c :attribute "opsem decl" :type "port declaration" :stage nil
    :instance i 
    :env env 
    :ap i "name" name 
    :ap i "port type" pt
    :do (aset env (aseq "port type" name ) pt)
)

(aclosure c :attribute "opsem decl" :type "process declaration"
    :instance i 
    :do 
    (match :av c "stage" nil :ap i "variables" variables :do 
        (update-push-aclosure c :av "stage" 'decls :av "index" 0 :av "length" (length variables)))
    (match :av c "stage" 'decls :ap i "variables" variables :ap c "index" index :ap length "length" 
        :ap c "env" env :ap i "name" name :do 
        (if (< index len)
            (progn (update-push-aclosure c :av "index" (+ index 1))
                (clear-update-eval-aclosure c :av "instance" (nth index variables)))
                ;Можно ли с listt применятьь все операции как к list?
            (aset c (aseq "process states names" ) name (reduce (lambda (col el) (append (aget el "name") col)) (aget i states)))))

)

(aclosure c :attribute "opsem decl" :type "program decl"
    :instance i 
    :do
    (match :av c "stage" nil :ap i "clock" clock :do 
        (update-push-aclosure c :av "stage" 'clock)
        (clear-update-eval-aclosure c :av "attribute" "opsem" :av "instance" clock))
    (match :av c "stage" 'clock :ap i "declarations" decls :ap c "agent" a :ap a "value" val
        :ap c "env" env :do
        (aset env (aseq clock ) val)
        (update-push-aclosure c :av "stage" 'decls :av "decls" decls))
    (match :av c "stage" decls :ap c "decls" decls :do 
        (if decls 
            (progn (update-push-aclosure c :av "decls" (cdr decls))
                (clear-update-eval-aclosure c :av "instance" (car decls)))
            (update-push-aclosure c :av "stage" 'procs :av "procs" (aget i "processes"))))
    (match :av c "stage" procs :ap c "procs" procs :do 
        (if procs 
            (progn (update-push-aclosure c :av "procs" (cdr procs))
                (clear-update-eval-aclosure c :av "instance" (car procs)))))
)

;opsem init

(aclosure c :attribute "opsem init" :type "statement variable declaration" :stage nil
    :instance i 
    :ap i "name" name 
    :env env 
    :do (update-push-aclosure c :av "stage" 'inited)
        (clear-update-eval-aclosure c :av "attribute" "opsem" :av "instance" (aget env (aseq "variable init" name)))
)
(aclosure c :attribute "opsem init" :type "statement variable declaration" :stage 'inited
    :instance i 
    :ap i "name" name 
    :value val 
    :agent a
    :do (aset a (aseq "variable value" name) val)
)

(aclosure c :attribute "opsem init" :type "simple init" :stage nil 
    :instance i 
    :do (clear-update-eval-aclosure c :av "attribute" "opsem" :av "instance" i))

(aclosure c :attribute "opsem init" :type "array variable declaration" :stage nil
    :instance i 
    :ap i "name" name 
    :env env 
    :do (update-push-aclosure c :av "stage" 'init)
        (clear-update-eval-aclosure c :av "instance" (aget env (aseq "variable init" name)))
)
(aclosure c :attribute "opsem init" :type "array variable declaration" :stage 'init
    :instance i 
    :ap i "name" name 
    :env env 
    :agent a 
    :value val 
    :do (aset a (aseq "variable value" name) val)
)
(aclosure c :attribute "opsem init" :type "array init" :stage nil 
    :instance i 
    :do (update-push-aclosure c :av "stage" 'exprs :av "collected" nil :av "exprs" (cdr i))
        (clear-update-eval-aclosure c :av "attribute" "opsem" :av "instance" (car i)))
(aclosure c :attribute "opsem init" :type "array init" :stage 'exprs 
    :value val 
    :ap "exprs" exprs 
    :ap "collected" col
    :p (cons val col) new-col
    :do (if exprs 
            (progn (update-push-aclosure c :av "stage" 'exprs :av "collected" new-col :av "exprs" (cdr exprs))
                (clear-update-eval-aclosure c :av "attribute" "opsem" :av "instance" (car exprs)))
            (reverse col)))


(aclosure c :attribute "opsem init" :type "structure variable declaration" :stage nil
    :instance i
    :ap i "name" name 
    :ap i "type" ty
    :env env  
    :do (update-push-aclosure c :av "stage" 'init)
        (clear-update-eval-aclosure c :av "instance" (aget env (aseq "variable init" name)) 
            :av "result" (type-default-val env ty) 
            :av "struct type" ty)
)
(aclosure c :attribute "opsem init" :type "structure variable declaration" :stage 'init
    :instance i
    :ap i "name" name 
    :env env 
    :agent a 
    :value val 
    :do (aset a (aseq "variable value" name) val)
)

(aclosure c :attribute "opsem init" :type "struct init" :stage nil
    :instance i
    :agent a
    :ap i "struct name" sname
    :ap i "fields" fields
    :env env
    :p (aget env (aseq "struct fields" sname)) fnames
    :do 
        (update-push-aclosure c 
            :av "stage" 'override 
            :av "fnames" fnames 
            :av "fields" fields
            :av "last idx" -1)
        (clear-update-eval-aclosure c :av "instance" (car fields))
)
(aclosure c :attribute "opsem init" :type "struct init" :stage 'override
    :instance i
    :agent a
    :env env
    :ap "fields" fields
    :ap "result" res
    :ap "last idx" lidx
    :value val
    :p (car fields) field
    :p (aget field "name") fname
    :p (aget env (aseq "struct fields" sname)) fnames
    :do (if (> (length fields) 1)
            (progn
                (if fname 
                    (progn (aset res fname val)
                        (update-push-aclosure c 
                            :av "fields" (cdr fields)
                            :av "last idx" (position fname fnames :test #'string=))
                        (clear-update-eval-aclosure c :instance (car (cdr fields))))
                    (progn (aset res (nth (+ lidx 1) fnames) val)
                        (update-push-aclosure c 
                            :av "fields" (cdr fields)
                            :av "last idx" (+ lidx 1))
                        (clear-update-eval-aclosure c :instance (car (cdr fields))))
                ))
            (progn
                (if fname 
                    (progn (aset res fname val)
                        res)
                    (progn (aset res (nth (+ lidx 1) fnames) val)
                        res)
                )))
)


(aclosure c :attribute "opsem init" :type "enum variable declaration" :stage nil
    :instance i 
    :ap i "name" name 
    :env env  
    :do (update-push-aclosure c :av "stage" 'init)
        (clear-update-eval-aclosure c :av "attribute" "opsem" :av "instance" (aget env (aseq "variable init" name)))
)
(aclosure c :attribute "opsem init" :type "enum variable declaration" :stage 'init
    :instance i
    :ap i "name" name 
    :env env 
    :agent a 
    :value val 
    :do (aset a (aseq "variable value" name) val)
)
(aclosure c :attribute "opsem init" :type "enum element access" :stage nil 
    :instance i 
    :do (clear-update-eval-aclosure c :av "attribute" "opsem" :av "instance" i))

(aclosure c :attribute "opsem init" :type "process declaration" :stage nil 
    :instance i 
    :agent a 
    :env env 
    :ap i "name" name 
    :ap i "variables" variables
    :do (aset a (aseq "process time" name) 0)
        (aset a (aseq "process state" name) (first-state env name))
        (aset a (aseq "process state offset" proc ) nil)
        (update-push-aclosure c :av "stage" 'init-vars :av "vars" variables)
)
(aclosure c :attribute "opsem init" :type "process declaration" :stage 'init-vars 
    :instance i 
    :ap "vars" vars 
    :do (if vars
            (progn (update-push-aclosure c :av "vars" (cdr vars))
                (clear-update-eval-aclosure c :av "instance" (car vars))))
)

(aclosure c :attribute "opsem init" :type "node declaration" :stage nil 
    :instance i 
    :agent a 
    :env env 
    :ap i "name" name 
    :ap i "variables" variables
    :do (update-push-aclosure c :av "stage" 'init-vars :av "vars" variables))
(aclosure c :attribute "opsem init" :type "node declaration" :stage nil 
    :instance i 
    :ap "vars" vars 
    :do (if vars
            (progn (update-push-aclosure c :av "vars" (cdr vars))
                (clear-update-eval-aclosure c :av "instance" (car vars)))))

(aclosure c :attribute "opsem init" :type "program declaration" :stage nil
    :instance i 
    :ap i "declarations" decls 
    :do (update-push-aclosure c :av "stage" 'decls :av "decls" decls)
)
(aclosure c :attribute "opsem init" :type "program declaration" :stage 'decls
    :instance i 
    :ap "decls" decls
    :ap i "nodes" nodes
    :do (if decls 
            (progn (update-push-aclosure c :av "decls" (cdr decls))
                (clear-update-eval-aclosure c :av "instance" (car decls)))
            (update-push-aclosure c :av "stage" 'nodes :av "nodes" nodes))       
)
(aclosure c :attribute "opsem init" :type "program declaration" :stage 'nodes
    :instance i 
    :ap "nodes" nodes
    :ap i "processes" procs
    :do (if nodes 
            (progn (update-push-aclosure c :av "nodes" (cdr nodes))
                (clear-update-eval-aclosure c :av "instance" (car nodes)))
            (update-push-aclosure c :av "stage" 'procs :av "procs" (remove-if (lambda (el) (aget el "active")) procs)))       
)
(aclosure c :attribute "opsem init" :type "program declaration" :stage 'procs
    :instance i 
    :ap "procs" procs 
    :do (if procs 
            (progn (update-push-aclosure c :av "stage" 'procs :av "procs" (cdr procs))
                (clear-update-eval-aclosure c :av "instance" (car procs))))
)