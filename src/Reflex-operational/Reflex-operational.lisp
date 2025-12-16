(uiop:define-package Reflex-semantics
  (:use #:cl))
(in-package #:Reflex-semantics)


(mot "env"
    :at "agents" (listt "agent")
    :at "aclosures" (cot :amap "agent" (listt cot))
    :at "variable type" (cot :amap "variable name" "type")
    :at "port type" (cot :amap "port name" "port type")
    :at "input variables" (listt "variable name")
    :at "output variables" (listt "variable name")
    :at "variable init" (cot :amap "variable name" "reflex init")
    :at "process states names" (cot :amap "process name" (listt "state name"))
    :at "struct types" (cot :amap "structure name" "field name" "type")
    :at "enum value" (cot :amap "enum name" "constant name" "int")
    :atv "clock" nat 100
)

(mot "agent" 
    :at "variable value" (cot :amap "variable name" "reflex value")
    :at "process state" (cot :amap "process name" "state name")
    :at "process state offset" (cot :amap "process name" "int")
    :at "process time" (cot :amap "process name" "natural constant")
    :at "current process" "process name"
    :at "current state" "state name"
    :at "current offset" int
    :at "processes to start" (listt "process name")
    :at "value" "reflex value"
)
(mot "reflex value" (uniont "defined value" "lvalue" ))
(mot "defined value" (uniont "constant" "array value" "struct value"))
(mot "struct value") (uniont (cot :amap "field name" "reflex value"))
(mot "array value" (uniont (listt "reflex value")))
(mot "lvalue" :av "name" "string")

(aclosure c :attribute "opsem" :type "time constant" :stage nil
    :instance i 
  (let ((days (aget i "d"))
      (hours (aget i "h"))
      (minutes (aget i "m"))
      (seconds (aget i "s"))
      (milis (aget i "ms")))
    (+ (if milis milis 0)
      (* (+ (if seconds seconds 0)
        (* (+ (if minutes minutes 0)
          (* (+ (if hours hours 0)
            (* (if days days 0) 24)) 60)) 60)) 1000))))


(aclosure c :attribute "opsem" :type "non time constant" :stage nil
    :instance i
    i)

(aclosure c :attribute "opsem" :type "element access" :stage nil
    :instance i 
    :ap i "variable" name 
    :ap i "accesses" rst 
    :agent a 
    :do (if (and (not (nil rst)) (> (length rst) 0)) 
            (update-push-aclosure c :av "stage" 'access :av "current" (car rst) :av "rest" (cdr rst) :av "values" (aget a (aseq "variable value" "name")))
            (iobj "lvalue" :av name (aget i "name")))
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
    :do 
)



(mot "nondivision binary expressions" (uniont "+" "-" "*" "<<" ">>" "==" "!=" "<=" ">=" "<" ">" "|" "&" "^"))

(aclosure c :attribute "opsem" :type "nondivision binary expressions" :stage nil
    :instance i
    :ap i "left" left 
    :do (progn (update-push-aclosure c :av "stage" 'left)
            (clear-update-eval-aclosure c :av "instance" left))
)
(aclosure c :attribute "opsem" :type "nondivision binary expressions" :stage 'left
    :instance i
    :value left
    :ap i "right" right 
    :do (progn (update-push-aclosure c :av "stage" 'right :av "left" left)
            (clear-update-eval-aclosure c :av "instance" right))
)
(aclosure c :attribute "opsem" :type "nondivision binary expressions" :stage 'left
    :instance i
    :agent a
    :ap "left" left
    :value right  
    :do (def-bin-op i (act left a) (act right a))
)

(aclosure c :attribute "opsem" :type "/" :stage nil
    :instance i
    :ap i "left" left
    :do (progn (update-push-aclosure c :av "stage" 'left)
            (clear-update-eval-aclosure c :av "instance" left))
)
(aclosure c :attribute "opsem" :type "/" :stage 'right
    :instance i
    :value left
    :ap i "right" right
    :do (progn (update-push-aclosure c :av "stage" 'right :av "left" left)
            (clear-update-eval-aclosure c :av "instance" right))
)
(aclosure c :attribute "opsem" :type "/" :stage 'left
    :instance i
    :agent a 
    :env env 
    :value right 
    :ap c "left" left
    :do (let ((left (act left a))
                (right (act right a)))
            (if (= right 0)
                (make-error env a "Division by zero")
                (/ left right)))
)

(aclosure c :attribute "opsem" :type "%" :stage nil
    :instance i
    :ap i "left" left
    :do (progn (update-push-aclosure c :av "stage" 'left)
            (clear-update-eval-aclosure c :av "instance" left))
)
(aclosure c :attribute "opsem" :type "/" :stage 'right
    :instance i
    :value left
    :ap i "right" right
    :do (progn (update-push-aclosure c :av "stage" 'right :av "left" left)
            (clear-update-eval-aclosure c :av "instance" right))
)
(aclosure c :attribute "opsem" :type "/" :stage 'left
    :instance i
    :agent a 
    :env env 
    :value right 
    :ap c "left" left
    :do (let ((left (act left a))
                (right (act right a)))
            (if (= right 0)
                (make-error env a "Division by zero")
                (mod left right)))
)

(aclosure c :attribute "opsem" :type "&&" :stage nil
    :instance i
    :ap i "left" left 
    :do (progn (update-push-aclosure c :av "stage" 'left)
            (clear-update-eval-aclosure c :av "instance" left))
)
(aclosure c :attribute "opsem" :type "&&" :stage 'left
    :instance i
    :value val 
    :agent a
    :ap i "right" right
    :do (if (= (act val a) 'false)
            'false
            (clear-update-eval-aclosure c :av "instance" right))
)
(aclosure c :attribute "opsem" :type "||" :stage nil
    :instance i
    :ap i "left" left 
    :do (progn (update-push-aclosure c :av "stage" 'left)
            (clear-update-eval-aclosure c :av "instance" left))
)
(aclosure c :attribute "opsem" :type "||" :stage 'left
    :instance i
    :value val 
    :agent a
    :ap i "right" right
    :do (if (= (act val a) 'true)
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
                (update-push-aclosure c :av "stage" 'access :av "current" (car rest) :av "rest" (cdr rest) :av "values" var :av "collected" nil :av "collected values" nil :av "res" (act val a))
                (progn
                    (aset a (aseq "variable name" name) (act val a))
                    (iobj "lvalue" :av name))))
)
(aclosure c :attribute "opsem" :type "=" :stage 'access
    :ap "current" cur 
    :ap "rest" rst 
    :ap "values" vals 
    :ap "collected" coll 
    :ap "collected values" collval
    :do 
    (match :t cur "field name" :do 
        (let ((var (aget vals cur)))
            (if rst 
                (update-push-aclosure c :av "stage" 'access :av "current" (car rst) :av "rest" (cdr rst) :av "values" var :av "collected" (cons cur coll) :av "collected values" (cons var collval))
                (update-push-aclosure c :av "stage" 'unwind)))
    )               
    (match :t cur "expression" :do 
        (update-push-aclosure c :av "stage" 'access-act)
        (clear-update-eval-aclosure c :av "instance" cur))
)
(aclosure c :attribute "opsem" :type "=" :stage 'access-act
    :agent a
    :instance i 
    :value val
    :ap "current" cur 
    :ap "rest" rst 
    :ap "values" vals 
    :ap "collected" coll 
    :ap "collected values" collval
    :do (let *((act-val (act val a))
                (var (nth act-val vals)))
            (if (and (<= 0 act-val) (< act-val (get-array-size env name (reverse coll))))
                    (if rst 
                        (update-push-aclosure c :av "stage" 'access :av "current" (car rest) :av "rest" (cdr rest) :av "values" var :av "collected" (cons act-val coll) :av "collected values" (cons var collval))
                        (update-push-aclosure c :av "stage" 'unwind)
                (make-error env a "Array index out of bounds"))))
)
(aclosure c :attribute "opsem" :type "=" :stage 'unwind
    :agent a
    :instance i 
    :value val
    :ap "current" cur 
    :ap "rest" rst 
    :ap "values" vals 
    :ap "collected" coll 
    :ap "collected values" collval
    :ap "res" res 
    :ap i "left" access 
    :ap access "variable" name 
    :ap "fin" fin
    :do (if coll 
            (update-push-aclosure c :av "collected" (cdr coll) :av "collected values" (cdr collval) :av "res" (aset collval coll res))
            (progn (aset a (aseq "variable name" name) res)
                fin))
)

(mot "compaund assignment" (uniont "+=" "*=" "-=" "<<=" ">>=" "|=" "&=" "^="))

(aclosure c :attribute "opsem" :type "compaund assignment" :stage nil
    :instance i 
    :ap i "right" right
    :do (progn (update-push-aclosure c :av "stage" 'right)
            (clear-update-eval-aclosure c "instance" right))
)
(aclosure c :attribute "opsem" :type "compaund assignment" :stage 'right
    :instance i 
    :agent a 
    :value val
    :ap i "left" access 
    :ap access "variable" name 
    :ap access "accesses" rst 
    :do (let ((var (aget a (aseq "variable name" name))))
            (if (and (not (nil rest)) (> (length rest) 0)) 
                (update-push-aclosure c :av "stage" 'access :av "current" (car rest) :av "rest" (cdr rest) :av "values" var :av "collected" nil :av "collected values" nil :av "res" (act val a))
                (progn
                    (aset a (aseq "variable name" name) (act val a))
                    (iobj "lvalue" :av name))))
)
(aclosure c :attribute "opsem" :type "compaund assignment" :stage 'access
    :instance i 
    :agent a 
    :value val
    :ap "current" cur
    :ap "rest" rst 
    :ap "values" vals 
    :ap "collected" coll 
    :ap "collected values" collval
    :do 
    (match :t cur "field name" :do 
        (let ((var (aget vals cur)))
            (if rst 
                (update-push-aclosure c :av "stage" 'access :av "current" (car rst) :av "rest" (cdr rst) :av "values" var :av "collected" (cons cur coll) :av "collected values" (cons var collval))
                (update-push-aclosure c :av "stage" 'unwind :av "res" (def-comp-assign var res) :av "fin" (def-comp-assign var res))))
    )               
    (match :t cur "expression" :do 
        (update-push-aclosure c :av "stage" 'access-act)
        (clear-update-eval-aclosure c :av "instance" cur))
)
(aclosure c :attribute "opsem" :type "compaund assignment" :stage 'access-act
    :instance i 
    :agent a 
    :value val
    :ap "current" cur
    :ap "rest" rst 
    :ap "values" vals 
    :ap "collected" coll 
    :ap "collected values" collval
    :do (let ((act-val (act val a))
                (var (nth act-val vals)))
            (if (and (<= 0 act-val) (< act-val (get-array-size env name (reverse coll))))
                (if rest 
                    (update-push-aclosure c :av "stage" 'access :av "current" (car rst) :av "rest" (cdr rst) :av "values" var :av "collected" (cons act-val coll) :av "collected values" (cons var collval))
                    (update-push-aclosure c :av "stage" 'unwind :av "res" (def-comp-assign var res) :av "fin" (def-comp-assign var res)))
                (make-error env a "Array index out of bounds")))
)
(aclosure c :attribute "opsem" :type "compaund assignment" :stage 'unwind
    :instance i 
    :agent a 
    :value val
    :ap "rest" rst 
    :ap "values" vals 
    :ap "collected" coll 
    :ap "collected values" collval
    :ap "res" res
    :ap i "left" access 
    :ap access "variable" name 
    :ap "fin" fin
    :do (if coll 
            (update-push-aclosure c :av "collected" (cdr coll) :av "collected values" (cdr collval) :av "res" (aset collval coll res))
            (progn (aset a (aseq "variable name" name) res)
                fin))
)

#|
int x[3]={0,1,2};
int y=1;
x[--y]/=y;
при O0 - floating point exception
при O1 - 0
|#

(aclosure c :attribute "opsem" :type "/="
    :instance i 
    :do
    (match :av c "stage" nil :ap i "right" right :do 
        (progn (update-push-aclosure c :av "stage" 'right)
            (clear-update-eval-aclosure c "instance" right)))
    (match :av c "stage" 'right :ap c "agent" a :ap a "value" val :ap i "left" access :ap access "variable" name :ap access "accesses" rest :ap c "res" res :do 
        (let ((var (aget a (aseq "variable name" name)))
                (act-val ))
            (if (and (not (nil rest)) (> (length rest) 0)) 
                (update-push-aclosure c :av "stage" 'access :av "current" (car rest) :av "rest" (cdr rest) :av "values" var :av "collected" nil :av "collected values" nil :av "res" (act val a))
                (progn
                    (aset a (aseq "variable name" name) (act val a))
                    (iobj "lvalue" :av name)))))
    (match :av c "stage" 'access :ap c "current" cur :t cur "field name" :ap c "rest" rest :ap c "values" vals :ap c "collected" coll :ap c "collected values" collval :ap c "res" res :c "env" env :do 
        (let ((var (aget vals cur)))
            (if rest 
                (update-push-aclosure c :av "stage" 'access :av "current" (car rest) :av "rest" (cdr rest) :av "values" var :av "collected" (cons cur coll) :av "collected values" (cons var collval))
                (if (= res 0) 
                    (make-error env a)
                    (update-push-aclosure c :av "stage" 'unwind :av "res" (/ var res) :av "fin" (/ var res)))))
    )               
    (match :av c "stage" 'access :ap c "current" cur :t cur "expression" :do 
        (update-push-aclosure c :av "stage" 'access-act)
        (clear-update-eval-aclosure c :av "instance" cur))
    (match :av c "stage" 'access-act :ap c "rest" rest :ap c "values" vals :ap c "agent" a :ap a "value" val :ap c "collected" coll :ap c "collected values" collval :ap c "res" res :do
        (let ((act-val (act val a))
                (var (nth act-val vals)))
            (if (and (<= 0 act-val) (< act-val (get-array-size env name (reverse coll))))
                (if rest 
                    (update-push-aclosure c :av "stage" 'access :av "current" (car rest) :av "rest" (cdr rest) :av "values" var :av "collected" (cons act-val coll) :av "collected values" (cons var collval))
                    (if (= res 0) 
                        (make-error env a)
                        (update-push-aclosure c :av "stage" 'unwind :av "res" (/ var res) :av "fin" (/ var res))))
                (make-error env a "Array index out of bounds"))))
    (match :av c "stage" 'unwind :ap c "rest" rest :ap c "values" vals :ap c "agent" a :ap a "value" val :ap c "collected" coll :ap c "collected values" collval :ap c "res" res 
    :ap i "left" access :ap access "variable" name :ap c "fin" fin :do 
        (if coll 
            (update-push-aclosure c :av "collected" (cdr coll) :av "collected values" (cdr collval) :av "res" (aset collval coll res))
            (progn (aset a (aseq "variable name" name) res)
                fin)))
)

(aclosure c :attribute "opsem" :type "++."
    :instance i 
    :do
    (match :av c "stage" nil :ap c "agent" a :ap i "left" access :ap access "variable" name :ap access "accesses" rest :do 
        (if (and (not (nil rest)) (> (length rest) 0)) 
                (update-push-aclosure c :av "stage" 'access :av "collected" nil :av "collected values" nil)
                (progn
                    (aset a (aseq "variable name" name) (+ (aget a (aseq "variable name" name)) 1))
                    (iobj "lvalue" :av name)))
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
                    (iobj "lvalue" :av name)))
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
    :instance i 
    :agent a
    :do (and (not (equal (aget a (aseq "process state" process)) 'stop))
            (not (equal (aget a (aseq "process state" process)) 'error)))
)
(aclosure c :attribute "opsem" :type "inactive" :stage nil
    :instance i 
    :agent a
    :do (or (equal (aget a (aseq "process state" process)) 'stop)
            (equal (aget a (aseq "process state" process)) 'error))
)
(aclosure c :attribute "opsem" :type "rstop" :stage nil
    :instance i 
    :agent a
    :do (equal (aget a (aseq "process state" process)) 'stop)
)
(aclosure c :attribute "opsem" :type "rerror" :stage nil
    :instance i 
    :agent a
    :do (equal (aget a (aseq "process state" process)) 'error)
)

(aclosure c :attribute "opsem" :type "process state checking" :stage nil
    :instance i 
    :ap i "process" process 
    :ap i "activity" act 
    :agent a
    :do (clear-update-eval-aclosure c :av "instance" act)
)

;Transformations: statements


(aclosure c :attribute "opsem" :type "array init" 
    :instance i 
    :do 
    (match :av c "stage" nil :do
        (update-push-aclosure c :av "stage" 'idx :av "index" 1 :av "length" (length i))
        (clear-update-eval-aclosure c "instance" (car i)))
    (match :av c "stage" 'idx :ap c "index" index :ap c "length" len :ap c "agent" a :ap a "value" val :av "collected" collected :do 
        (if (< index len)
            (progn 
                (update-push-aclosure c :av "index" (+ index 1) :av "collected" (cons (act val a) collected))
                (clear-update-eval-aclosure c "instance" (nth index i)))
            (cons (act val a) collected))))

(aclosure c :attribute "opsem" :type "struct init" 
    :instance i 
    :do
    (match :av c "stage" nil :do 
        (update-push-aclosure c :av "stage" 'fields :av "fields" (attributes i) :av "new init" (ob))
        (clear-update-eval-aclosure c iob (aget i (car (attributes i)))))
    (match :av c "stage" nil :ap c "fields" fields  :ap "new init" ninit :ap c "agent" a :ap a "value" val :do 
        (if (> (length fields) 1)
            (progn 
                (update-push-aclosure c :av "fields" (cdr fields) :av "new init" (aset ninit (car fields) val))
                (clear-update-eval-aclosure c iob (aget i (car (cdr fields)))))
            (aset ninit (car fields) val))
    )        
)




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
    :do (if state
            (progn (aset a (aseq "process state" proc ) state)
                (aset a (aseq "process state offset" proc ) nil)
                (aset a (aseq "process time" proc ) 0))
            (let ((res (next-process-state a env)))
                (progn (aset a (aseq "process state" proc ) res)
                    (aset a (aseq "process state offset" proc ) nil)
                    (aset a (aseq "process time" proc ) 0))))
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
            (clear-update-eval-aclosure c :av "instance" (iobj "restart process"))
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
            (clear-update-eval-aclosure c :av "instance" (iobj "stop current process"))
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
            (clear-update-eval-aclosure c :av "instance" (iobj "error current process"))
            (aset a
                :av "processes state" proc 'error
                :av "process time" proc 0))
)

(aclosure c :attribute "opsem" :type "statement list"
    :instance i 
    :do 
    (match :av c "stage" nil :do 
        (update-push-aclosure c :av "stage" 'rest :av "rest" (cdr i))
        (clear-update-eval-aclosure c :av "instance" (car i)))
    (match :av c "stage" 'rest :av c "rest" rst :do 
        (if rst 
            (progn (update-push-aclosure c :av "rest" (cdr rst))
                (clear-update-eval-aclosure c :av "instance" (car rst))))))

(aclosure c :attribute "opsem" :type "if then else statement"
    :instance i 
    :do 
    (match :av c "stage" nil :ap i "condition" env :do
        (progn (update-push-aclosure c :av "stage" 'condition)
            (clear-update-eval-aclosure c :av "instance" con)))
    (match :av c "stage" 'condition :ap i "then" then :ap i "else" else :ap c "agent" a :ap a "value" val :do
        (if (= (act val a) 'true) 
            (clear-update-eval-aclosure c :av "instance" then)
            (clear-update-eval-aclosure c :av "instance" else))))

(aclosure c :attribute "opsem" :type "if then statement"
    :instance i 
    :do
    (match :av c "stage" nil :ap i "condition" env :do
        (progn (update-push-aclosure c :av "stage" 'condition)
            (clear-update-eval-aclosure c :av "instance" con)))
    (match :av c "stage" 'condition :ap i "then" then :ap c "agent" a :ap a "value" val :do
        (if (= (act val a) 'true)  
            (clear-update-eval-aclosure c :av "instance" then))))

(aclosure c :attribute "opsem" :type "switch statement"
    :instance i 
    :do 
    (match :av c "stage" nil :ap i "controlling expression" con :do 
        (progn (update-push-aclosure c :av "stage" 'condition)
            (clear-update-eval-aclosure c :av "instance" con)))
    (match :av c "stage" 'condition :ap i "cases" cs :ap c "agent" a :ap a "value" val :do
        (if cs 
            (update-push-aclosure c :av "stage" 'case-label :av "val" (act val a) :av "index" 0 :av "length" (length cs))
            (update-push-aclosure c :av "stage" 'default)))
    (match :av c "stage" 'case-label :ap c "index" index :ap c "length" len :ap i "cases" cs :do 
        (if (< index length)
            (progn (update-push-aclosure c :av "stage" 'case-iter)
                (clear-update-eval-aclosure c :av "instance" (aget (nth index cs) 'label)))
            (update-push-aclosure c :av "stage" 'default)))
    (match :av c "stage" 'case-iter :ap c "index" index :ap c "val" val :ap c "agent" a :ap a "value" label :ap i "cases" cs :do 
        (if (= val label)
            (progn 
                (if (not (aget (nth index cs) 'break))
                    (update-push-aclosure c :av "stage" 'cont-case-iter :av "index" (+ index 1))
                    (clear-update-eval-aclosure c :av "instance" (aget (nth index cs)))))
                (update-push-aclosure c :av "stage" 'case-label :av "index" (+ index 1))))
    (match :av c "stage" 'cont-case-iter :ap c "index" index :ap i "cases" cs :ap c "length" len :do 
        (if (< index len)
            (progn (if (not (aget (nth index cs) 'break))
                    (update-push-aclosure c index (+ index 1)))
                (clear-update-eval-aclosure c :av "instance" (nth index cs)))
            (update-push-aclosure c :av "stage" 'default)))
    (match :av c "stage" 'default :ap i "default" def :do 
        (if def 
            (clear-update-eval-aclosure c :av "instance" def)))
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

(aclosure c :attribute "opsem" :type "timeout statement" 
    :instance i 
    :do 
    (match :av c "stage" nil :av i "controlling expression" expr :do 
        (update-push-aclosure c :av "stage" 'cond)
        (clear-update-eval-aclosure c :av "instance" expr))
    (match :av c "stage" 'cond :ap c "agent" a :ap a "value" val 
        :ap a "current process" cur-proc :ap i "statements" sts :do 
        (if (<= (act val a) (aget a (aseq "process time" cur-proc))
            (clear-update-eval-aclosure c :av "instance" sts))))
)

(aclosure c :attribute "opsem" :type "wait" :stage nil
    :instance i 
    :do (clear-update-eval-aclosure c :av "instance" (aget i "condition")))
(aclosure c :attribute "opsem" :type "slice" :stage nil
    :instance i 
    :do nil)
(aclosure c :attribute "opsem" :type "transition" :stage nil
    :instance i 
    :do (clear-update-eval-aclosure c :av "instance" (aget i "condition")))

(aclosure c :attribute "opsem" :type "state declaration"
    :instance i 
    :do 
    (match :av c "stage" nil :ap i "statements" sts :ap c "agent" a :ap a "current" substate substate :do 
        (update-push-aclosure c :av "stage" 'statements :av "index" substate :av "length" (length sts)))
    (match :av c "stage" 'statements :ap c "index" index :ap c "length" len :ap i "statements" sts :do 
        (if (< index len)
            (progn (if (is-instance (nth index sts) 'barrier statement)
                        (update-push-aclosure c :av "stage" 'barrier :av "st" (nth index sts))
                        (update-push-aclosure c :av "stage" 'statements :av "index" (+ index 1)))
                (clear-update-eval-aclosure c :av "instance" (nth index sts)))))
    (match :av c "stage" 'barrier :ap index "index" :ap c "length" len :ap i "statements" sts 
        :ap c "st" st :t st wait :ap c "agent" a :ap a "value" val :do
        (if val
            (progn (update-push-aclosure c :av "stage" 'statements :av  index (+ index 1))
                (aset a "process state offset" (aget a "current process") (+ index 1)))
            (aset a "process state offset" (aget a "current process") index)))
    (match :av c "stage" 'barrier :ap index "index" :ap c "length" len :ap i "statements" sts 
        :ap c "st" st :t st slice :ap c "agent" a :ap a "value" val :do
        (aset a "process state offset" (aget a "current process") index))
    (match :av c "stage" 'barrier :ap index "index" :ap c "length" len :ap i "statements" sts 
        :ap c "st" st :t st transition :ap c "agent" a :ap a "value" val :do
        (if (equal (aget a "current offset") index)
            (if val
                (progn (update-push-aclosure c :av "stage" 'statements :av "index" (+ index 1))
                    (aset a "process state offset" (aget a "current process") (+ index 1)))
                (aset a "process state offset" (aget a "current process") index))
            (aset a "process state offset" (aget a "current process") index))))

(aclosure c :attribute "opsem" :type "process declaration"
    :instance i 
    :do
    (match :av c "stage" nil :ap c "agent" a :ap i "name" name :ap i "states" states :ap c "env" env :do 
        (let ((state (find-if (lambda state (equal (aget state "name") (aget a "current state"))) states)))
            (aset a "current process" name)
            (aset a "current state" (aget a (aseq "process state" name)))
            (aset a "current offset" (aget a (aseq "process state offset" name)))
            (if state 
                (progn (clear-update-eval-aclosure c :av "instance" state)
                    (aset a "process time" (+ (aget a (aseq "process time" name)) (aget env "clock"))))))))

(aclosure c :attribute "opsem" :type "program declaration"
    :instance i 
    :do 
    (match :av c "stage" nil :do 
        (update-push-aclosure c :av "stage" 'init-input)
    )
    (match :av c "stage" 'init-input :ap c "input" input :ap c "agent" a :do 
        (if input 
            (progn
                (update-push-aclosure c (cdr input))
                (aset a "variable value" (car input) (random 100)))
            (update-push-aclosure c :av "stage" 'work :av "index" 0 :av "length" (length (aget i "processes")))))
    (match :av c "stage" work :ap c "index" index :ap c "length" len :ap c "agent" a :do 
        (if (< index len)
            (progn (update-push-aclosure c :av "index" (+ index 1))
                (update-push-aclosure c :av "stage" 'init-started :av "index" 0 :av "length" (length (aget a "processes to start")))
                (clear-update-eval-aclosure c :av "instance" (nth index (aget i "processes"))))
            (update-push-aclosure c :av "stage" 'init-input :av "input" (aget env "input variables"))))
    (match :av c "stage" 'init-started :ap c "index" index :ap c "length" len :ap c "agent" a :do 
        (if (< index len)
            (progn (update-push-aclosure c :av "index" (+ index 1))
                (clear-update-eval-aclosure c
                    :av "attribute" "opsem init" 
                    :av "instance" (find-if 
                                (lambda process (equal (aget process "name") (nth index (aget a "processes to start")))) 
                                (aget i "processes"))))
            (aset a (aseq "processes to start") nil)))    
)

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

(aclosure c :attribute "opsem decl" :type "constant declaration"
    :instance i 
    :do 
    (match :av c "stage" nil :ap i "expression" expr :do 
        (update-push-aclosure c :av "stage" 'val)
        (clear-update-eval-aclosure c :av "instance" expr))
    (match :av c "stage" 'val :ap i "name" name :ap c "env" con
        :ap c "agent" a :ap a "value" val :do 
        (aset a (aseq "variable value" name) val)))
        
(aclosure c :attribute "opsem decl" :type "simple variable declaration" 
    :instance i 
    :do 
    (match :av c "stage" nil :ap i "init" init :ap i "type" rtype :ap c "env" env :do 
        (update-push-aclosure c :av "stage" 'first :av "init" (if init init (type-default-val env rtype))))
    (match :av c "stage" 'first :ap i "name" name :ap c "init" init :ap c "env" env :ap i "type" rtype :do 
        (aset env (aseq "variable init" name) init)
        (aset env (aseq "variable type" name) rtype))                    
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
            (aset env (aseq "variable init" name) (type-default-val env rtype)))
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

(aclosure c :attribute "opsem init" :type "simple variable declaration"
    :instance i 
    :do 
    (match :av c "stage" nil :ap i "name" name :ap c "env" env :do 
        (update-push-aclosure c :av "stage" 'inited)
        (clear-update-eval-aclosure c :av "attribute" "opsem" :av "instance" (aget env (aseq "variable init" name))))
    (match :av c "stage" 'inited :ap c "agent" a :ap a "value" val :do 
        (aset a (aseq "variable value" name) val))

)
(aclosure c :attribute "opsem init" :type "array variable declaration"
    :instance i 
    :do 
    (match :av c "stage" nil :ap i "name" name :ap c "env" env :do 
        (update-push-aclosure c :av "stage" 'to-init)
        (clear-update-eval-aclosure c :av "attribute" "opsem" :av "instance" (aget env (aseq "variable init" name))))
    (match :av c "stage" 'to-init :ap i "name" name :ap c "agent" a :ap a "value" val :do 
            (aset a (aseq "variable value" name) val))
)

(aclosure c :attribute "opsem init" :type "structure variable declaration"
    :instance i 
    :do 
    (match :av c "stage" nil :ap i "name" name :ap c "env" env :ap i "type" rtype :do 
        (let ((init (aget env (aseq "variable init" name))))
            (update-push-aclosure c :av "stage" 'inited)
            (clear-update-eval-aclosure c "instance" name)))
    (match :av c "stage" 'inited :ap i "name" name :ap c "agent" a :ap a "value" val :do 
        (aset a (aseq "variable value" name) val))
)

(aclosure c :attribute "opsem init" :type "enum variable declaration" :stage nil
    :instance i 
    :ap i "name" name 
    :env env 
    :do (aset a (aseq "variable value" name) (aget env (aseq "variable init" name)))
)

(aclosure c :attribute "opsem init" :type "process declaration"
    :instance i 
    :do 
    (match :av c "stage" nil :ap c "agent" a :ap c "env" env :ap i "name" name :ap i "variables" variables :do 
        (aset a (aseq "process time" name ) 0)
        (aset a (aseq "process state" name) (first-state env name))
        (aset a (aseq "process state offset" name ) 0)
        (update-push-aclosure c :av "stage" 'init vars :av "vars" variables))
    (match :av c "stage" 'init vars :ap c "vars" vars :do 
        (if vars
            (progn (update-push-aclosure c :av "vars" (cdr vars))
                (clear-update-eval-aclosure c :av "instance" (car vars)))))
)

(aclosure c :attribute "opsem init" :type "program declaration"
    :instance i 
    :do 
    (match :av c "stage" nil :ap i "declarations" decls :do 
        (update-push-aclosure c :av "stage" 'decls :av "decls" decls))
    (match :av c "stage" decls :ap c "decls" decls :do 
        (if decls 
            (progn (update-push-aclosure c :av "decls" (cdr decls))
                (clear-update-eval-aclosure c :av "instance" (car decls)))
            (clear-update-eval-aclosure c :av "instance" (aget i processes 1))))        
)