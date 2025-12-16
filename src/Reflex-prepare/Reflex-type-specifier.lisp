(uiop:define-package Reflex-semantics
  (:use #:cl))
(in-package #:Reflex-semantics)

(defun cons-to-inner-list (a aseq val)
    (aset a (aseql aseq) (cons val (aget a (aseql aseq)))))

(defun make-error (env agent message)
    (progn 
        (print message)
        (delete-agent-aclosures env agent)))

(defun delete-agent-aclosures (env agent)
    (progn 
        (aset env "agents" (remove-if (lambda (val) (= (aget val "uid") (aget agent "uid"))) (aget env "agents")))
        (aset env (aseq "aclosures" agent) nil)))

(defun get-variable-type-sup (env type fields)
    (cond 
        ((is-instance type "simple type") (if (null fields) type nil))
        ((is-instance type "array type")
            (if (stringp (car fields))
                nil
                (get-variable-type-sup env (aget type "element type") (cdr fields))))
        ((is-instance type "structure type")
            (let* ((struct-name (aget type "name"))
                    (field-type (aget (aget env (aseq "struct fields" struct-name))) (car fields)))
                (get-variable-type-sup env field-type (cdr fields))))
        ((is-instance t "enum type") (if (null fields) 'int32 nil))
    ))
(defun get-variable-type (env name fields)
    (get-variable-type-sup env (aget env (aseq "variable type" name)) fields))


(defun order-int-types (left right)
    (if (= left right)
        "="
        (let* ((type-list '(bool int8 uint8 int16 uint16 int32 uint32 int64 uint64))
                (tail1 (member left type-list))
                (tail2 (member right type-list)))
            (if (> (length tail1) (length tali2))
                "<"
                ">"))))

(defun def-type (op left right)
    (if (is-instance left "undefined type")
        (if (is-instance right "unidefined type")
            (if (or (is-instance right 'unidefined-float-type) (is-instance left 'unidefined-float-type))
                'undefined-float-type
                'undefined-int-type)
            right)
        (if (is-instance right "unidefined type")
            left
            (if (or (is-instance left "float type") (is-instance right "float type"))
                (if (or (= left 'double) (= right 'double))
                    'double
                    'float)
                (cond 
                    ((member op '("+" "-" "*" "/" "%" ">>" "<<" "==" "!=" ">=" "<=" ">" "<"))
                        (let ((intl (order-int-types left 'int32))
                                (intr (order-int-types right 'int32))
                                (comp (order-int-types left right)))
                            (if (and (= intl "<") (= intr "<"))
                                'int32
                                (if (= comp "<")
                                    right 
                                    left))))
                  ((member op '("&&" "||")) 'bool)
                  ((member op '("&" "|" "^")) (order-int-types left right))
                  ((member op '("!.")) 'bool)
                  ((member op '("-." "~.")) 
                    (let ((intr (order-int-types right 'int32)))
                        (if (= intr ">")
                            right 
                            'int32)))
                  ((member op '("=" "+=" "-=" "*=" "/=" "<<=" ">>=")) 
                        (let ((intl (order-int-types left 'int32))
                                (intr (order-int-types right 'int32))
                                (comp (order-int-types left right)))
                            (if (and (= intl "<") (= intr "<"))
                                'int32
                                (if (= comp "<")
                                    right 
                                    left))))
                  ((member op '("&=" "|=" "^=")) (order-int-types left right))
                  ((member op '("++." ".++" "--." ".--")) right))))))

(mot "env" 
    :at "agents" (listt "agent")
    :at "aclosures" (cot :amap "agent" (listt (cot)))
    :at "variable type" (cot :amap "variable name" "type")
    :at "port type" (cot :amap "port name" "port type")
    :at "input variables" (listt "variable name")
    :at "output variables" (listt "variable name")
    :at "variable init" (cot :amap "variable name" "reflex init")
)

(mot "agent"
    :at "value" "type")
#| 
(mot "typed value"
    :at "type" "type"
    :at "value" any)
|#

;(att "cast" :at "pretype" "type")
;можно ли на union атрибуты добавлять?
(att "expression" :at "restype" "type")

(aclosure c :attribute "type spec" :type "bool constant"
    'bool)

(aclosure c :attribute "type spec" :type "integer constant"
    'undefined-int-type)

(aclosure c :attribute "type spec" :type "natural constant"
    'undefined-int-type)

(aclosure c :attribute "type spec" :type "float constant"
    'undefined-float-type)

(aclosure c :attribute "type spec" :type "time constant"
    'undefined-int-type)

(aclosure c :attribute "type spec" :type "element access" :stage nil 
    :instance i
    :env env
    :ap i "variable" name 
    :ap i "accesses" rst
    :p (get-variable-type env name nil) ty
    :do (if rst 
            (update-push-aclosure c :av "stage" 'access :av "current" (car rst) :av "rest" (cdr rst))
            (progn 
                (aset i "restype" ty)
                ty))
)    
(aclosure c :attribute "type spec" :type "element access" :stage 'access    
    :instance i
    :env env
    :ap i "variable" name 
    :ap "current" cur 
    :ap "rest" rst 
    :ap "path" path
    :p (get-variable-type env name (reverse path)) ty
    :do        
    (match :t cur "field name"  :do
        (if rst 
            (update-push-aclosure c :av "stage" 'access :av "current" (car rest) :av "rest" (cdr rest) :av "path" (cons cur path))
            (progn
                (aset i "restype" ty)
                ty)) 
    )               
    (match :t cur "expression" :do 
        (update-push-aclosure c :av "stage" 'access-act)
        (clear-update-eval-aclosure c :av "instance" cur))
)
(aclosure c :attribute "type spec" :type "element access" :stage 'access-act
    :instance i
    :env env
    :agent a
    :ap "rest" rst 
    :ap "path" path 
    :ap i "name" name
    :p (get-variable-type env name (reverse path)) ty
    :do (if rst
            (update-push-aclosure c :av "stage" 'access :av "current" (car rst) :av "rest" (cdr rst) :av "path" (cons 0 path))
            (progn 
                (aset i "restype" ty)
                ty))
)

(aclosure c :attribute "type spec" :type "binary expression" :stage nil 
    :instance i 
    :ap i "left" left 
    :do (update-push-aclosure c :av "stage" 'left)
        (clear-update-eval-aclosure c :av "instance" left)
)
(aclosure c :attribute "type spec" :type "binary expression" :stage 'left 
    :instance i 
    :ap i "right" right 
    :value left 
    :do (update-push-aclosure c :av "stage" 'right :av "left" left)
        (clear-update-eval-aclosure c :av "instance" right)
)
(aclosure c :attribute "type spec" :type "binary expression" :stage 'right 
    :instance i 
    :value right
    :ap "left" left 
    :ap i "left" left-arg 
    :ap i "right" right-arg 
    :p (def-type (otype i) left right) new-type
    :do (if (not (= new-type left))
            (if (or (not (is-instance left "undefined type")) (is-instance new-type "undefined type"))
                (aset i "left" (iobj "cast" :av "type" new-type :av "expression" left-arg :av "pretype" left))))
        (if (not (= new-type right))
            (if (or (not (is-instance right "undefined type")) (is-instance new-type "undefined type"))
                (aset i "right" (iobj "cast" :av "type" new-type :av "expression" right-arg :av "pretype" right))))
        (aset i "restype" new-type)
        new-type
)

(aclosure c :attribute "type spec" :type "binary bool expression" :stage nil
    :instance i 
    :ap i "left" left 
    :do (update-push-aclosure c :av "stage" 'left)
        (clear-update-eval-aclosure c :av "instance" left)
)
(aclosure c :attribute "type spec" :type "binary bool expression" :stage 'left
    :instance i 
    :ap i "right" right 
    :value left 
    :do (update-push-aclosure c :av "stage" 'right :av "left" left)
        (clear-update-eval-aclosure c :av "instance" right)
)
(aclosure c :attribute "type spec" :type "binary bool expression" :stage 'left
    :instance i
    :value right
    :ap "left" left 
    :ap i "left" left-arg 
    :ap i "right" right-arg 
    :do (if (not (= new-type left))
            (if (or (not (is-instance left "undefined type")) (is-instance new-type "undefined type"))
                (aset i "left" (iobj "cast" :av "type" new-type :av "expression" left-arg :av "pretype" left))))
        (if (not (= new-type right))
            (if (or (not (is-instance right "undefined type")) (is-instance new-type "undefined type"))
                (aset i "right" (iobj "cast" :av "type" new-type :av "expression" right-arg :av "pretype" right))))
        (aset i "restype" 'bool)
        'bool
)

(aclosure c :attribute "type spec" :type "cast" :stage nil
    :instance i 
    :ap i "expression" expr 
    :do (update-push-aclosure c :av "stage" 'expr)
        (clear-update-eval-aclosure c :av "instance" expr)
)
(aclosure c :attribute "type spec" :type "cast" :stage 'expr
    :instance i 
    :value val 
    :ap i "type" new-type
    :do (aset i "restype" new-type)
        new-type
)

(aclosure c :attribute "type spec" :type "unary expression" :stage nil 
    :instance i 
    :ap i "right" right 
    :do (update-push-aclosure c :av "stage" 'expr)
        (clear-update-eval-aclosure c :av "instance" right)
)
(aclosure c :attribute "type spec" :type "unary expression" :stage 'expr 
    :instance i
    :ap i "type" new-type
    :value right
    :p (def-type (otype i) nil right) new-type
    :do (if (not (= new-type right))
            (if (or (not (is-instance right "undefined type")) (is-instance new-type "undefined type"))
                (aset i "right" (iobj "cast" :av "type" new-type :av "expression" right-arg :av "pretype" right))))
        (aset i "restype" new-type)
        new-type
)

(aclosure c :attribute "type spec" :type "assignments" :stage nil
    :instance i 
    :ap i "right" 
    :do (update-push-aclosure c :av "stage" 'right)
        (clear-update-eval-aclosure c :av "instance" right)
)
(aclosure c :attribute "type spec" :type "assignments" :stage 'right
    :instance i 
    :ap i "left" left
    :value right
    :do (update-push-aclosure c :av "stage" 'left :av "right" right)
        (clear-update-eval-aclosure c :av "instance" left)
)
(aclosure c :attribute "type spec" :type "assignments" :stage 'right
    :instance i
    :value left
    :ap "right" right 
    :ap i "right" right-base
    :do (if (and (/= left right) (not (is-instance right "undefined type")))
            (aset i "right" (iobj "cast" :av "type" left :av "expression" right-base :av "pretype" right)))
        (aset i "restype" left)
        left
)

(aclosure c :attribute "type spec" :type "increment&decrement" :stage nil
    :instance i
    :ap i "access" access 
    :do (update-push-aclosure c :av "stage" 'next)
        (clear-update-eval-aclosure c :av "instance" access)
)
(aclosure c :attribute "type spec" :type "increment&decrement" :stage 'next
    :instance i
    :value val 
    :do (aset i "restype" val)
        val
)

(aclosure c :attribute "type spec" :type "process state checking"
    :instance i 
    :do (aset i "restype" 'bool)
        'bool)

;Statements
(aclosure c :attribute "type spec" :type "statement list" :stage nil
    :instance i 
    :do (update-push-aclosure c :av "stage" 'rest :av "rest" (cdr i))
        (clear-update-eval-aclosure c :av "instance" (car i))
)
(aclosure c :attribute "type spec" :type "statement list" :stage 'rest
    :av "rest" rst 
    :do (if rst 
            (progn (update-push-aclosure c :av "rest" (cdr rst))
                (clear-update-eval-aclosure c :av "instance" (car rst))))
)

(aclosure c :attribute "type spec" :type "timeout statement"
    :instance i 
    :ap i "statements" sts
    :do (clear-update-eval-aclosure c :av "instance" sts)
)

(aclosure c :attribute "type spec" :type "wait"
    :instance i 
    :ap i "condition" expr 
    :do (clear-update-eval-aclosure c :av "instance" expr)
)

(aclosure c :attribute "type spec" :type "wait on timeout"
    :instance i 
    :ap i "condition" expr 
    :ap i "controlling expression" expr 
    :at i "statements" sts
    :do (clear-update-eval-aclosure c :av "instance" expr)
        (clear-update-eval-aclosure c :av "instance" sts)
)

(aclosure c :attribute "type spec" :type "if then statement" :stage nil
    :instance i 
    :ap i "condition" con
    :do (update-push-aclosure c :av "stage" 'con)
        (clear-update-eval-aclosure c :av "instance" con)
)
(aclosure c :attribute "type spec" :type "if then statement" :stage 'con
    :instance i 
    :value val 
    :ap i "then" th
    :do (if (not (is-instance val "boolean type"))
            (iobj "cast" :av "type" 'bool :av "expression" val :av "pretype" val))
        (clear-update-eval-aclosure c :av "instance" th)
)

(aclosure c :attribute "type spec" :type "if then else statement" :stage nil
    :instance i 
    :ap i "condition" con
    :do (update-push-aclosure c :av "stage" 'con)
        (clear-update-eval-aclosure c :av "instance" con)
)
(aclosure c :attribute "type spec" :type "if then else statement" :stage 'con
    :instance i
    :value val
    :ap i "then" th
    :do (if (not (is-instance val "boolean type"))
            (iobj "cast" :av "type" 'bool :av "expression" val :av "pretype" val))
        (update-push-aclosure c "stage" 'th)
        (clear-update-eval-aclosure c :av "instance" th)
)
(aclosure c :attribute "type spec" :type "if then else statement" :stage 'th
    :instance i
    ap i "else" el
    :do (clear-update-eval-aclosure c :av "instance" el)
)

(aclosure c :attribute "type spec" :type "switch statement" :stage nil
    :instance i 
    :ap i "controlling expression" expr 
    :ap i "cases" cs
    :do (update-push-aclosure c :av "stage" 'cs :av "rest" cs)
        (clear-update-eval-aclosure c :av "instance" expr)
)
(aclosure c :attribute "type spec" :type "switch statement" :stage 'cs
    :instance i 
    :ap c "rest" rst
    :do (if rst 
            (progn (update-push-aclosure c :av "rest" (cdr rst))
                (clear-update-eval-aclosure c :av "instance" (car rst)))
            (progn (update-push-aclosure c :av "stage" 'def)
                (clear-update-eval-aclosure c :av "instance" (aget i "default"))))
)
(aclosure c :attribute "type spec" :type "switch statement" :stage 'def
    :instance i 
    :ap i "default" def 
    :do (clear-update-eval-aclosure c :av "instance" def)
)

(aclosure c :attribute "type spec" :type "case statement"
    :instance i 
    (clear-update-eval-aclosure c :av "instance" (aget i "statements")))
(aclosure c :attribute "type spec" :type "default statement"
    :instance i 
    (clear-update-eval-aclosure c :av "instance" (aget i "statements")))
 
(aclosure c :attribute "type spec" :type "statement block"
    :instance i 
    :ap i "statements" sts
    (clear-update-eval-aclosure c :av "instance" sts)
)

(aclosure c :attribute "type spec" :type "expression statement"
    :instance i 
    (clear-update-eval-aclosure c :av "instance" (aget i "expression"))
)

;Declarations

(aclosure c :attribute "type spec" :type "state declaration"
    :instance i 
    (clear-update-eval-aclosure c :av "instance" (aget i "statements"))
)

(aclosure c :attribute "type spec" :type "process declaration" :stage nil
    :instance i 
    :ap i "states" states
    :do (update-push-aclosure c "stage" 'states :av "rest" states)
)
(aclosure c :attribute "type spec" :type "process declaration" :stage nil
    :instance i 
    :ap "rest" rst
    :do (if rst 
            (progn 
                (update-push-aclosure c :av "rest" (cdr rst)))
                (clear-update-eval-aclosure c :av "instance" (car rst)))
)

(aclosure c :attribute "type spec" :type "program declaration" :stage nil
    :instance i 
    :ap i "processes" procs
    :do (update-push-aclosure c "stage" 'procs :av "rest" procs)
)
(aclosure c :attribute "type spec" :type "program declaration" :stage nil
    :instance i 
    :ap "rest" rst
    :do (if rst 
            (progn 
                (update-push-aclosure c :av "rest" (cdr rst)))
                (clear-update-eval-aclosure c :av "instance" (car rst)))
)