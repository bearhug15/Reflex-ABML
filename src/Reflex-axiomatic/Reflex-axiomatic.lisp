(uiop:define-package Reflex-semantics
  (:use #:cl))
(in-package #:Reflex-semantics)

(mot "env"
    :at "agents" (listt "agent")
    :at "aclosures" (cot :amap "agent" (listt cot))

    :at "program" "program declaration"
    :at "variable type" (cot :amap "variable name" "type")
    :at "port type" (cot :amap "port name" "port type")
    :at "input variables" (listt "varibale name")
    :at "output variables" (listt "varibale name")
    :at "variable init" (cot :amap "variable name" "reflex init")
    :at "processes states names" (cot :amap "process name" (listt "state name"))
    :at "struct fields" (cot :amap "structure name" "variable name" "type")
    :at "enum value" (cot :amap "enum name" "field name" "int")
    :atv "clock" int 100

    :at "conditions" (listt "vc lemma")

    ; List of compatability rules defined as a list of predicate functions returning nil if list of formulas is not compatable
    :at "crules" (listt (funt any "term" bool))
    :at "analysis params" (mot)
)


(mot "agent"
    :at "current process" "process name"
    :at "processes to start" (listt "process name")
    :at "value" "term"

    :at "cur cond" (listt "formula")
    :atv "cur attr" "attributes" (mo "attributes")

    ;expression attributes
    :at "precond" (listt "formula")
    :at "proc act" (cot :amap "process name" "activity")
    :at "state" "program state"
)

(aclosure c :attribute "actuate" :type "value getter"
    :instance i 
    :ap i "actuated" act 
    :ap i "type" rtype 
    :ap i "access" access
    :ap (aseq "agent" "state") state
    :do (if act 
            i 
            (mo "value getter" :av "type" rtype :av "state" state :av "access" access :av "actuated" t))
)

(aclosure c :attribute "actuate" :type "binary operation" :stage nil
    :instance i 
    :ap i "actuated" act  
    :ap i "left" left
    :do (if act 
            i 
            (progn (update-push-aclosure c :av "stage" 'left)
                (clear-update-eval-aclosure c "instance" left)))
)
(aclosure c :attribute "actuate" :type "binary operation" :stage 'left
    :instance i 
    :ap i "right" right
    :value val 
    :do (update-push-aclosure c :av "stage" 'right :av "left" val)
        (clear-update-eval-aclosure c :av "instance" right)
)
(aclosure c :attribute "actuate" :type "binary operation" :stage 'right
    :instance i 
    :value right 
    :ap "left" left 
    :ap i "type" rtype 
    :ap i "op" op
    :do (mo "binary operation" :av "type" rtype :av "op" op :av "left" left :av "right" right :av "actuated" t)
)


(aclosure c :attribute "actuate" :type "unary operation" :stage nil
    :instance i 
    :ap i "actuated" act  
    :ap i "right" right
    :do (if act 
            i 
            (progn (update-push-aclosure c :av "stage" 'right)
                (clear-update-eval-aclosure c "instance" right)))
)
(aclosure c :attribute "actuate" :type "unary operation" :stage 'right
    :instance i 
    :value right
    :ap i "type" rtype 
    :ap i "op" op
    :do (mo "unary operation" :av "type" rtype :av "op" op :av "right" right :av "actuated" t)
)

(aclosure c :attribute "actuate" :type "cast operation" :stage nil
    :instance i 
    :ap i "actuated" act  
    :ap i "right" right
    :do (if act 
            i 
            (progn (update-push-aclosure c :av "stage" 'right)
                (clear-update-eval-aclosure c "instance" right)))
)
(aclosure c :attribute "actuate" :type "cast operation" :stage 'right
    :instance i 
    :value right
    :ap i "type" rtype 
    :ap i "op" op 
    :do (mo "cast operation" :av "type" rtype :av "right" right :av "actuated" t)
)

(aclosure c :attribute "actuate" :type "nonactuatable term"
    :instance i
    :do i)

(aclosure c :attribute "axsem" :type "time constant"
    :instance i 
    :ap i (aseq "d" "value") days
    :ap i (aseq "h" "value") hours
    :ap i (aseq "m" "value") minutes
    :ap i (aseq "s" "value") seconds
    :ap i (aseq "ms" "value") milis
    :do (mo "typed constant" :av "type" 'uint64 :av "value" (+ (if (milis) milis 0)
            (* (+ (if (seconds) seconds 0)
                (* (+ (if (minutes) minutes 0)
                    (* (+ (if (hours) hours 0)
                        (* (if (days) days 0) 24)) 60)) 60)) 1000))))

(aclosure c :attribute "axsem" :type "non time constant"
    :instance i 
    :do i)

;expression возвращает term 
(aclosure c :attribute "axsem" :type "field name"
    :instance i
    :do i)

(aclosure c :attribute "axsem" :type "element access" :stage nil
    :instance i
    :ap i "accesses" rst 
    :do (update-push-aclosure c :av "stage" 'access :av "accesses" (cdr rst))
        (clear-update-eval-aclosure c :av "instance" (cdr rst))
)
(aclosure c :attribute "axsem" :type "element access" :stage nil
    :ap "accesses" rst
    :ap "collected" coll
    :value val
    :do (if (is-instance val "field name")
            (if rst 
                (progn
                    (update-push-aclosure c :av "collected" (cons val coll) :av "accesses" (cdr rst))
                    (clear-update-eval-aclosure c :av "instance" (car rst)))
                (update-push-aclosure c :av "stage" 'complete :av "collected" (cons val coll)))
            (progn (update-push-aclosure c :av "stage" 'access-act)
                (clear-update-eval-aclosure c :av "attribute" "actuate" :av "instance" val)))
)
(aclosure c :attribute "axsem" :type "element access" :stage 'access-act
    :instance i
    :ap i "variable" name
    :ap "accesses" rst 
    :ap "collected" coll
    :value val 
    :do (update-push-aclosure c :av "stage" 'domain :av "collected" (cons val coll) :av "accesses" (cdr rest) :av "index" val)
        (clear-update-eval-aclosure c :av "instance" (get-array-size env name (reverse coll)))
)
(aclosure c :attribute "axsem" :type "element access" :stage 'domain
    :instance i
    :ap i "variable" name
    :ap "accesses" rst 
    :ap "collected" coll
    :value val 
    :ap "index" index 
    :ap "bounds" bounds
    :p (mo "binary operation" :av "type" 'bool :av "op" "<=" :av "left" 0 :av "right" index :av "actuated" t) lbound
    :p (mo "binary operation" :av "type" 'bool :av "op" "<" :av "left" index :av "right" val :av "actuated" t) hbound
    :p (mo "binary operation" :av "type" 'bool :av "op" "&&" :av "left" lbound :av "right" hbound :av "actuated" t) bound 
    :do (if rst
            (progn (update-push-aclosure c :av "collected" (cons index coll) 
                                            :av "accesses" (cdr rst) 
                                            :av "bounds" (cons bound bounds))
                (clear-update-eval-aclosure c :av "instance" (car rst)))
            (update-push-aclosure c :av "stage" 'complete :av "collected" (cons index coll) :av "bounds" (cons bound bounds)))
)
(aclosure c :attribute "axsem" :type "element access" :stage 'complete
    :instance i
    :ap i "variable" name 
    :ap "collected" coll 
    :ap "env" env
    :ap "bounds" bounds
    :agent a
    :ap a "state" state 
    :do (if (not (null bounds))
                (let ((domain (mo "conjunction" :av "formulas" bounds))) 
                    (finalize-lemma a env domain)
                    (cons-to-inner-list a (aseq "precond") domain)))
        (mo "value getter" :av "type" (get-variable-type env name new-coll) 
                            :av "state" state 
                            :av "name" access 
                            :av "actuated" (not (null coll)))
)

(aclosure c :attribute "axsem" :type "enum element access"
    :instance i 
    :env env 
    :ap i "name" name 
    :ap i "field" field
    :do (aget env (aseq "enum value" name field))
)   

;Transformations: expressions

(mot "nondivision binary expression" :union ("+" "-" "*" "<<" ">>" "==" "!=" "<=" ">=" "<" ">" "|" "&" "^"))

(aclosure c :attribute "axsem" :type "nondivision binary expression" :stage nil
    :instance i 
    :ap i "left" left
    :do (update-push-aclosure c "stage" 'left)
        (clear-update-eval-aclosure c :av "instance" left)
)
(aclosure c :attribute "axsem" :type "nondivision binary expression" :stage 'left
    :instance i 
    :ap i "right" right
    :value left 
    :do (update-push-aclosure c :av "stage" 'right :av "left" left)
        (clear-update-eval-aclosure c :av "instance" right)
)
(aclosure c :attribute "axsem" :type "nondivision binary expression" :stage 'right
    :instance i 
    :value right 
    :ap i "restype" new-type
    :p (mo "binary operation" :av "type" new-type :av "op" (otype i) :av "left" left :av "right" right) new-expr 
    :do (update-push-aclosure c :av "stage" 'actuated)
        (clear-update-eval-aclosure c :av "attribute" "actuate" :av "instance" new-expr)
)
(aclosure c :attribute "axsem" :type "nondivision binary expression" :stage 'actuated
    :value val 
    :do val
)

(typedef "division" (uniont "/" "%"))

(aclosure c :attribute "axsem" :type "division" :stage nil
    :instance i 
    :ap i "left" left
    :do (update-push-aclosure c "stage" 'left)
        (clear-update-eval-aclosure c :av "instance" left)
)
(aclosure c :attribute "axsem" :type "division" :stage 'left
    :instance i 
    :ap i "right" right
    :value left 
    :do (update-push-aclosure c :av "stage" 'right :av "left" left)
        (clear-update-eval-aclosure c :av "instance" right)
)
(aclosure c :attribute "axsem" :type "division" :stage 'right
    :instance i 
    :value right 
    :ap "left" left 
    :do (update-push-aclosure c :av "stage" 'left-act :av "right" right)
        (clear-update-eval-aclosure c :av "attribute" "actuate" :av "instance" left)
)
(aclosure c :attribute "axsem" :type "division" :stage 'left-act
    :instance i   
    :value left
    :ap "right" right
    :do (update-push-aclosure c :av "stage" 'right-act :av "left" left)
        (clear-update-eval-aclosure c :av "attribute" "actuate" :av "instance" right)
)
(aclosure c :attribute "axsem" :type "division" :stage 'right-act
    :instance i
    :value right 
    :env env 
    :ap "left" left 
    :do (let* ((new-type (aget i "restype"))
            (new-expr (mo "binary operation" :av "type" new-type :av "op" (otype i) :av "left" left :av "right" right :av "actuated" t))
            (domain (mo "binary operation" :av "type" bool :av "op" "!=" :av "left" right :av "right" 0 :av "actuated" t)))
            (finalize-lemma a env domain)
            (cons-to-inner-list a (aseq "precond") domain)
            new-expr)
)

(aclosure c :attribute "axsem" :type "&&" :stage nil
    :instance i 
    :ap i "left" left
    :do (update-push-aclosure c :av "stage" 'left)
        (clear-update-eval-aclosure c :av "instance" left)
)
(aclosure c :attribute "axsem" :type "&&" :stage 'left
    :instance i 
    :value left 
    :do (update-push-aclosure c :av "stage" 'actuated)
        (clear-update-eval-aclosure c :av "instance" left :av "attribute" "actuate")
)
(aclosure c :attribute "axsem" :type "&&" :stage 'actuated
    :instance i 
    :env env 
    :value left
    :ap i "right" right
    :do (update-push-aclosure c :av "stage" 'short :av "agent" (iclone-agent env a) :av "left" (clone-obj left))
        (update-push-aclosure c :av "stage" 'long :av "left" left)
        (clear-update-eval-aclosure c :av "instance" right)
)
(aclosure c :attribute "axsem" :type "&&" :stage 'short
    :instance i
    :agent a
    :ap "left" left 
    :p (mo "unary operation" :av "type" bool :av "op" "!" :av "right" left :av "actuated" t) cnd
    :do (cons-to-inner-list a (aseq "precond")  cnd)
        'false
)
(aclosure c :attribute "axsem" :type "&&" :stage 'long
    :instance i
    :value right 
    :ap "left" left
    :do (update-push-aclosure c :av "stage" 'long-act :av "left" left)
        (clear-update-eval-aclosure c :av "instance" right :av "attribute" "actuate")
)
(aclosure c :attribute "axsem" :type "&&" :stage 'long
    :instance i
    :value right 
    :ap "left" left 
    :do (cons-to-inner-list a (aseq "precond")  left)
        right
)

(aclosure c :attribute "axsem" :type "\|\|" :stage nil
    :instance i 
    :ap i "left" left
    :do (update-push-aclosure c :av "stage" 'left)
        (clear-update-eval-aclosure c :av "instance" left)
)
(aclosure c :attribute "axsem" :type "\|\|" :stage 'left
    :instance i 
    :value left 
    :do (update-push-aclosure c :av "stage" 'actuated)
        (clear-update-eval-aclosure c :av "instance" left :av "attribute" "actuate")
)
(aclosure c :attribute "axsem" :type "\|\|" :stage 'actuated
    :instance i 
    :env env 
    :value left
    :ap i "right" right
    :do (update-push-aclosure c :av "stage" 'short :av "agent" (iclone-agent env a) :av "left" (clone-obj left))
        (update-push-aclosure c :av "stage" 'long :av "left" left)
        (clear-update-eval-aclosure c :av "instance" right)
)
(aclosure c :attribute "axsem" :type "\|\|" :stage 'short
    :instance i
    :agent a
    :ap "left" left 
    :do (cons-to-inner-list a (aseq "precond") left)
        'true
)
(aclosure c :attribute "axsem" :type "\|\|" :stage 'long
    :instance i
    :value right 
    :ap "left" left
    :do (update-push-aclosure c :av "stage" 'long-act :av "left" left)
        (clear-update-eval-aclosure c :av "instance" right :av "attribute" "actuate")
)
(aclosure c :attribute "axsem" :type "\|\|" :stage 'long
    :instance i
    :value right 
    :ap "left" left 
    :p (mo "unary operation" :av "type" bool :av "op" "!" :av "right" left :av "actuated" t) cnd
    :do (cons-to-inner-list a (aseq "precond")  cnd)
        right
)


(aclosure c :attribute "axsem" :type "cast" :stage nil 
    :instance i 
    :ap i "right" right
    :do (update-push-aclosure c stage right)
        (clear-update-eval-aclosure c :av "instance" right)
)
(aclosure c :attribute "axsem" :type "cast" :stage 'right 
    :instance i 
    :value right 
    :do (update-push-aclosure c :av "stage" 'actuated)
        (clear-update-eval-aclosure c :av "attribute" "actuate" :av "instance" new-expr)
)
(aclosure c :attribute "axsem" :type "cast" :stage 'actuated 
    :instance i
    :value val
    :ap i "type" rtype
    :ap i (aseq "right" "restype") pretype
    :do (mo "cast operation" :av "type" rtype :av "pretype" pretype :av "right" val :av "actuated" t)
)

(aclosure c :attribute "axsem" :type "!." :stage nil
    :instance i 
    :ap i "right" right
    :do (update-push-aclosure c stage right)
        (clear-update-eval-aclosure c :av "instance" right)
)
(aclosure c :attribute "axsem" :type "!." :stage 'right
    :instance i 
    :value right
    :do (update-push-aclosure c :av "stage" 'actuated)
        (clear-update-eval-aclosure c :av "attribute" "actuate" :av "instance" new-expr)
)
(aclosure c :attribute "axsem" :type "!." :stage 'right
    :instance i 
    :value val 
    :do (mo "unary operation" :av "type" 'bool :av "op" "!" :av "right" right :av "actuated" t)
)

(aclosure c :attribute "axsem" :type "-." :stage nil
    :instance i 
    :ap i "right" right
    :do (update-push-aclosure c stage right)
        (clear-update-eval-aclosure c :av "instance" right)
)
(aclosure c :attribute "axsem" :type "-." :stage 'right
    :instance i
    :value right
    :do (update-push-aclosure c :av "stage" 'actuated)
        (clear-update-eval-aclosure c :av "attribute" "actuate" :av "instance" new-expr)
)
(aclosure c :attribute "axsem" :type "-." :stage 'actuated
    :instance i
    :value val
    :do (mo "unary operation" :av "type" (aget val "type") :av "op" "-" :av "right" right :av "actuated" t)
)

(aclosure c :attribute "axsem" :type "~." :stage nil
    :instance i 
    :ap i "right" right
    :do (update-push-aclosure c stage right)
        (clear-update-eval-aclosure c :av "instance" right)
)
(aclosure c :attribute "axsem" :type "~." :stage 'right
    :instance i
    :value right
    :do (update-push-aclosure c :av "stage" 'actuated)
        (clear-update-eval-aclosure c :av "attribute" "actuate" :av "instance" new-expr)
)
(aclosure c :attribute "axsem" :type "~." :stage 'actuated
    :instance i
    :value val
    :do (mo "unary operation" :av "type" (aget val "type") :av "op" "~" :av "right" right :av "actuated" t)
)


;x={0,0,0}
; clang
; x[++x[0]] = x[0]; -> {1,0,0}
; x[x[0]++] = x[0]; -> {0,0,0}
; gcc
; x[++x[0]] = x[0]; -> {1,1,0}
; x[x[0]++] = x[0]; -> {1,0,0}
#|Сначала вычисляем правую часть, потом левую (слева направо), потом актуализируем значения |#



(mot "nondivision complex assignment" :union ("+=" "-=" "*=" "<<=" ">>=" "|=" "&=" "^="))
(mot "division complex assignment" :union ("/=" "%="))

(aclosure c :attribute "axsem" :type "=" :stage nil
    :instance i
    :ap i "right" right
    :do (update-push-aclosure c :av "stage" 'right)
        (clear-update-eval-aclosure c :av "instance" right)
)
(aclosure c :attribute "axsem" :type "=" :stage 'right
    :instance i
    :value val 
    :ap i "left" left 
    :ap left "accesses" rst
    :do (update-push-aclosure c :av "stage" 'access :av "accesses" (cdr rst) :av "right" val)
        (clear-update-eval-aclosure c :av "instance" (cdr rst))
)
(aclosure c :attribute "axsem" :type "=" :stage 'access
    :instance i
    :ap "accesses" rst 
    :ap "collected" coll 
    :ap "right" right
    :value val 
    :do (if rst 
            (progn
                (update-push-aclosure c :av "collected" (cons val coll) :av "accesses" (cdr rst))
                (clear-update-eval-aclosure c :av "instance" (car rst)))
            (progn (update-push-aclosure c :av "stage" 'right-act :av "collected" (cons val coll))
                (clear-update-eval-aclosure c :av "instance" right :av "attribute" "actuate")))
)
(aclosure c :attribute "axsem" :type "=" :stage 'right-act
    :instance i
    :value val
    :ap "collected" coll
    :do (update-push-aclosure c :av "right" val :av "stage" 'access-act :av "collected" (cdr coll))
        (clear-update-eval-aclosure c :av "instance" (car coll) :av "attribute" "actuate")
)
(aclosure c :attribute "axsem" :type "=" :stage 'access-act
    :instance i
    :value val 
    :ap "collected" coll 
    :ap "new collected" new-coll
    :ap "left" left 
    :ap left "name" name
    :ap "accesses" rst 
    :do (if rst 
            (progn (update-push-aclosure c :av "collected" (cdr coll) :av "new collected" (cons val new-coll))
                (clear-update-eval-aclosure c :av "instance" (car coll) :av "attribute" "actuate"))
            (progn (update-push-aclosure c :av "stage" 'domain :av "collected" (cons val new-coll) :av "path" (cons val new-coll))
                (clear-update-eval-aclosure c :av "instance" (get-array-size env name nil))))
)
(aclosure c :attribute "axsem" :type "=" :stage 'domain
    :instance i
    :ap c "path" path 
    :ap c "passed path" ppath 
    :value val 
    :ap c "bounds" domain 
    :do (if path 
            (if (is-instance (car path) "field name")
                (progn (update-push-aclosure c :av "path" (cdr path) :av "passed path" (cons (car path) ppath))
                    (clear-update-eval-aclosure c :av "instance" (get-array-size env name (reverse (cons (car path) ppath)))))
                (let* ((idx (car path))
                        (lbound (mo "binary operation" :av "type" 'bool :av "op" "<=" :av "left" 0 :av "right" index :av "actuated" t))
                        (hbound (mo "binary operation" :av "type" 'bool :av "op" "<" :av "left" index :av "right" val :av "actuated" t))
                        (bound (mo "binary operation" :av "type" 'bool :av "op" "&&" :av "left" lbound :av "right" hbound :av "actuated" t)))
                    (update-push-aclosure c :av "path" (cdr path) :av "passed path" (cons 0 ppath) :av "bounds" (cons bound domain))
                    (clear-update-eval-aclosure c :av "instance" (get-array-size env name (reverse (cons 0 ppath))))))
            (update-push-aclosure c :av "stage" 'complete))
)
(aclosure c :attribute "axsem" :type "=" :stage 'complete
    :instance i
    :agent a 
    :env env
    :ap i "variable" name 
    :ap "collected" coll
    :ap a "state" state 
    :ap "right" right 
    :ap "bounds" domain
    :p (mo "variable access" :av "name" name :av "path" coll) access 
    :p (mo "value setter" :av "type" (get-variable-type env name coll) :av "state" state :av "name" access :av "value" right) new-state 
    :do (aset a "state" new-state)
        (if (not (null domain))
            (let ((domain (mo "conjunction" :av "formulas" bounds)))
                (finalize-lemma a env domain)
                (cons-to-inner-list a (aseq "precond") domain)))
        (if (null coll) 
            (mo "value getter" :av "type" (get-variable-type env name new-coll) :av "state" state :av "name" access :av "actuated" nil)
            right)
)

(aclosure c :attribute "axsem" :type "nondivision complex assignment" :stage nil
    :instance i
    :ap i "right" right 
    :do (update-push-aclosure c :av "stage" 'right)
        (clear-update-eval-aclosure c :av "instance" right)
)
(aclosure c :attribute "axsem" :type "nondivision complex assignment" :stage 'right
    :instance i
    :ap i "left" left 
    :ap left "accesses" rst
    :value val
    :do (update-push-aclosure c :av "stage" 'access :av "accesses" (cdr rst) :av "right" val)
        (clear-update-eval-aclosure c :av "instance" (cdr rst))
)
(aclosure c :attribute "axsem" :type "nondivision complex assignment" :stage 'access
    :instance i
    :ap "accesses" rst 
    :ap "collected" coll 
    :value val 
    :ap "right" right
    :do (if rst 
            (progn
                (update-push-aclosure c :av "collected" (cons val coll) :av "accesses" (cdr rst))
                (clear-update-eval-aclosure c :av "instance" (car rst)))
            (progn (update-push-aclosure c :av "stage" 'right-act :av "collected" (cons val coll))
                (clear-update-eval-aclosure c :av "instance" right :av "attribute" "actuate")))
)
(aclosure c :attribute "axsem" :type "nondivision complex assignment" :stage 'right-act
    :instance i
    :value val 
    :ap c "collected" coll
    :do (update-push-aclosure c :av "right" val :av "stage" 'access-act :av "collected" (cdr coll))
        (clear-update-eval-aclosure c :av "instance" (car coll) :av "attribute" "actuate")
)
(aclosure c :attribute "axsem" :type "nondivision complex assignment" :stage 'access-act
    :instance i
    :ap "accesses" rst
    :ap "collected" coll 
    :ap "new collected" new-coll 
    :value val 
    :ap "left" left 
    :ap left "name" name
    :do (if rst 
            (progn (update-push-aclosure c :av "collected" (cdr coll) :av "new collected" (cons val new-coll))
                (clear-update-eval-aclosure c :av "instance" (car coll) :av "attribute" "actuate"))
            (progn (update-push-aclosure c :av "stage" 'domain :av "collected" (cons val new-coll) :av "path" (cons val new-coll))
                (clear-update-eval-aclosure c :av "instance" (get-array-size env name nil))))
)
(aclosure c :attribute "axsem" :type "nondivision complex assignment" :stage 'domain
    :instance i
    :ap c "path" path 
    :ap c "passed path" ppath 
    :value val 
    :ap c "bounds" domain 
    :do (if path 
            (if (stringp (car path))
                (progn (update-push-aclosure c :av "path" (cdr path) :av "passed path" (cons (car path) ppath))
                    (clear-update-eval-aclosure c :av "instance" (get-array-size env name (reverse (cons (car path) ppath)))))
                (let* ((idx (car path))
                        (lbound (mo "binary operation" :av "type" 'bool :av "op" "<=" :av "left" 0 :av "right" index :av "actuated" t))
                        (hbound (mo "binary operation" :av "type" 'bool :av "op" "<" :av "left" index :av "right" val :av "actuated" t))
                        (bound (mo "binary operation" :av "type" 'bool :av "op" "&&" :av "left" lbound :av "right" hbound :av "actuated" t)))
                    (update-push-aclosure c :av "path" (cdr path) :av "passed path" (cons 0 ppath) :av "bounds" (cons bound domain))
                    (clear-update-eval-aclosure c :av "instance" (get-array-size env name (reverse (cons 0 ppath))))))
            (update-push-aclosure c :av "stage" 'complete))
)
(aclosure c :attribute "axsem" :type "nondivision complex assignment" :stage 'complete
    :instance i
    :ap i "variable" name 
    :ap "collected" coll 
    :ap "env" env 
    :agent a
    :ap a "state" state 
    :ap "right" right 
    :ap "bounds" domain
    :do (let* ((access (mo "variable access" :av "name" name :av "path" coll))
                (old-val (mo "value getter" :av "type" (get-variable-type env name coll) :av "state" state :av "name" access))
                (new-val (mo "binary operation" :av "type"(get-variable-type env name coll) :av "op" (assignment-to-expression (otype i)) :av "left" old-val :av "right" right :av "actuated" t))
                (new-state (mo "value setter" :av "type" (get-variable-type env name coll) :av "state" state :av "name" access :av "value" new-val)))
            (aset a "state" new-state)
            (if (not (null domain))
                (let ((domain (mo "conjunction" :av "formulas" bounds)))
                    (finalize-lemma a env domain)
                    (cons-to-inner-list a (aseq "precond") domain)))
            (if (null coll) 
                (mo "value getter" :av "type" (get-variable-type env name new-coll) :av "state" state :av "name" access :av "actuated" nil)
                right))
)


(aclosure c :attribute "axsem" :type "division complex assignment" :stage nil
    :instance i
    :ap i "right" right 
    :do (update-push-aclosure c :av "stage" 'right)
        (clear-update-eval-aclosure c :av "instance" right)
)
(aclosure c :attribute "axsem" :type "division complex assignment" :stage 'right
    :instance i
    :ap i "left" left 
    :ap left "accesses" rst
    :value val
    :do (update-push-aclosure c :av "stage" 'access :av "accesses" (cdr rst) :av "right" val)
        (clear-update-eval-aclosure c :av "instance" (cdr rst))
)
(aclosure c :attribute "axsem" :type "division complex assignment" :stage 'access
    :instance i
    :ap "accesses" rst 
    :ap "collected" coll 
    :value val 
    :ap "right" right
    :do (if rst 
            (progn (update-push-aclosure c :av "collected" (cons val coll) :av "accesses" (cdr rst))
                (clear-update-eval-aclosure c :av "instance" (car rst)))
            (progn (update-push-aclosure c :av "stage" 'right-act :av "collected" (cons val coll))
                (clear-update-eval-aclosure c :av "instance" right :av "attribute" "actuate")))
)
(aclosure c :attribute "axsem" :type "division complex assignment" :stage 'right-act
    :instance i
    :value val 
    :ap c "collected" coll
    :do (update-push-aclosure c :av "right" val :av "stage" 'access-act :av "collected" (cdr coll))
        (clear-update-eval-aclosure c :av "instance" (car coll) :av "attribute" "actuate")
)
(aclosure c :attribute "axsem" :type "division complex assignment" :stage 'access-act
    :instance i
    :ap "accesses" rst
    :ap "collected" coll 
    :ap "new collected" new-coll 
    :value val 
    :ap "left" left 
    :ap left "name" name
    :do (if rst 
            (progn (update-push-aclosure c :av "collected" (cdr coll) :av "new collected" (cons val new-coll))
                (clear-update-eval-aclosure c :av "instance" (car coll) :av "attribute" "actuate"))
            (progn (update-push-aclosure c :av "stage" 'domain :av "collected" (cons val new-coll) :av "path" (cons val new-coll))
                (clear-update-eval-aclosure c :av "instance" (get-array-size env name nil))))
)
(aclosure c :attribute "axsem" :type "division complex assignment" :stage 'domain
    :instance i
    :ap c "path" path 
    :ap c "passed path" ppath 
    :value val 
    :ap c "bounds" domain 
    :do (if path 
            (if (stringp (car path))
                (progn (update-push-aclosure c :av "path" (cdr path) :av "passed path" (cons (car path) ppath))
                    (clear-update-eval-aclosure c :av "instance" (get-array-size env name (reverse (cons (car path) ppath)))))
                (let* ((idx (car path))
                        (lbound (mo "binary operation" :av "type" 'bool :av "op" "<=" :av "left" 0 :av "right" index :av "actuated" t))
                        (hbound (mo "binary operation" :av "type" 'bool :av "op" "<" :av "left" index :av "right" val :av "actuated" t))
                        (bound (mo "binary operation" :av "type" 'bool :av "op" "&&" :av "left" lbound :av "right" hbound :av "actuated" t)))
                    (update-push-aclosure c :av "path" (cdr path) :av "passed path" (cons 0 ppath) :av "bounds" (cons bound domain))
                    (clear-update-eval-aclosure c :av "instance" (get-array-size env name (reverse (cons 0 ppath))))))
            (update-push-aclosure c :av "stage" 'complete))
)
(aclosure c :attribute "axsem" :type "division complex assignment" :stage 'complete
    :instance i
    :ap i "variable" name 
    :ap "collected" coll 
    :ap "env" env 
    :agent a
    :ap a "state" state 
    :ap "right" right 
    :ap "bounds" domain
    :do (let* ((access (mo "variable access" :av "name" name :av "path" coll))
                (old-val (mo "value getter" :av "type" (get-variable-type env name coll) :av "state" state :av "name" access))
                (new-val (mo "binary operation" :av "type"(get-variable-type env name coll) :av "op" (assignment-to-expression (otype i)) :av "left" old-val :av "right" right :av "actuated" t))
                (new-state (mo "value setter" :av "type" (get-variable-type env name coll) :av "state" state :av "name" access :av "value" new-val))
                (div-domain (mo "binary operation" :av "type" 'bool :av "op" "=" :av "left" right :av "right" 0 :av "actuated" t)))
            (aset a "state" new-state)
            (let ((domain (mo "conjunction" :av "formulas" (cons div-domain bounds))))
                (finalize-lemma a env domain)
                (cons-to-inner-list a (aseq "precond") domain))
            (if (null coll) 
                (mo "value getter" :av "type" (get-variable-type env name new-coll) :av "state" state :av "name" access :av "actuated" nil)
                right))
)

(aclosure c :attribute "axsem" :type "++." :stage nil
    :instance i 
    :ap i "access" access 
    :ap access "accesses" rst
    :do (update-push-aclosure c :av "stage" 'access :av "accesses" (cdr rst))
        (clear-update-eval-aclosure c :av "instance" (cdr rst))
)
(aclosure c :attribute "axsem" :type "++." :stage 'access
    :instance i     
    :ap "accesses" rst 
    :ap "collected" coll
    :value val 
    :do (if (stringp val)
            (if rest 
                (progn
                    (update-push-aclosure c :av "collected" (cons val coll) :av "accesses" (cdr rest))
                    (clear-update-eval-aclosure c :av "instance" (car rest)))
                (update-push-aclosure c :av "stage" 'complete :av "collected" (cons val coll)))
            (progn (update-push-aclosure c :av "stage" 'access-act)
                (clear-update-eval-aclosure c :av "attribute" "actuate" :av "instance" val)))
)
(aclosure c :attribute "axsem" :type "++." :stage 'access-act
    :instance i  
    :ap "accesses" rst 
    :ap "collected" coll 
    :value val 
    :ap i "variable" name
    :do (update-push-aclosure c :av "stage" 'domain :av "collected" (cons val coll) :av "accesses" (cdr rst) :av "index" val)
        (clear-update-eval-aclosure c :av "instance" (get-array-size env name (reverse coll)))
)
(aclosure c :attribute "axsem" :type "++." :stage 'domain
    :instance i  
    :ap "accesses" rst 
    :ap "collected" coll
    :value val
    :ap "index" index 
    :ap "bounds" bounds
    :do (let* ((lbound (mo "binary operation" :av "type" 'bool :av "op" "<=" :av "left" 0 :av "right" index :av "actuated" t))
                (hbound (mo "binary operation" :av "type" 'bool :av "op" "<" :av "left" index :av "right" val :av "actuated" t))
                (bound (mo "binary operation" :av "type" 'bool :av "op" "&&" :av "left" lbound :av "right" hbound :av "actuated" t))) 
            (if rest
                (progn (update-push-aclosure c :av "collected" (cons index coll) :av "accesses" (cdr rest) :av "bounds" (cons bound bounds))
                    (clear-update-eval-aclosure c :av "instance" (car rest)))
                (update-push-aclosure c :av "stage" 'complete :av "collected" (cons index coll) :av "bounds" (cons bound bounds))))
)
(aclosure c :attribute "axsem" :type "++." :stage 'complete
    :instance i 
    :ap i (aseq "access" "variable") name 
    :ap "collected" coll 
    :env env 
    :agent a
    :ap a "state" state 
    :ap "bounds" bounds
    :do (let* ((new-coll (reverse coll))
                (access (mo "variable access" :av "name" name :av "path" new-coll))
                (var-type (get-variable-type env name new-coll))
                (getter (mo "value getter" :av "type" var-type :av "state" state :av "name" access :av "actuated" t))
                (new-val (mo "binary operation" :av "type" var-type :av "op" "+" :av "left" getter :av "right" 1 :av "actuated" t))
                (setter (mo "value setter" :av "type" var-type :av "state" state :av "name" access :av "value" new-val)))
            (if (not (null bounds))
                (let ((domain (mo "conjunction" :av "formulas" bounds))) 
                    (finalize-lemma a env domain)
                    (cons-to-inner-list a (aseq "precond") domain)))
            (aset a "state" setter)
            (if (null coll)
                (mo "value getter" :av "type" var-type :av "state" (aget a "state") :av "name" access :av "actuated" nil)
                new-val)
        )
)


(aclosure c :attribute "axsem" :type ".++" :stage nil
    :instance i 
    :ap i "access" access 
    :ap access "accesses" rst
    :do (update-push-aclosure c :av "stage" 'access :av "accesses" (cdr rst))
        (clear-update-eval-aclosure c :av "instance" (cdr rst))
)
(aclosure c :attribute "axsem" :type ".++" :stage 'access
    :instance i     
    :ap "accesses" rst 
    :ap "collected" coll
    :value val 
    :do (if (stringp val)
            (if rest 
                (progn
                    (update-push-aclosure c :av "collected" (cons val coll) :av "accesses" (cdr rest))
                    (clear-update-eval-aclosure c :av "instance" (car rest)))
                (update-push-aclosure c :av "stage" 'complete :av "collected" (cons val coll)))
            (progn (update-push-aclosure c :av "stage" 'access-act)
                (clear-update-eval-aclosure c :av "attribute" "actuate" :av "instance" val)))
)
(aclosure c :attribute "axsem" :type ".++" :stage 'access-act
    :instance i  
    :ap "accesses" rst 
    :ap "collected" coll 
    :value val 
    :ap i "variable" name
    :do (update-push-aclosure c :av "stage" 'domain :av "collected" (cons val coll) :av "accesses" (cdr rst) :av "index" val)
        (clear-update-eval-aclosure c :av "instance" (get-array-size env name (reverse coll)))
)
(aclosure c :attribute "axsem" :type ".++" :stage 'domain
    :instance i  
    :ap "accesses" rst 
    :ap "collected" coll
    :value val
    :ap "index" index 
    :ap "bounds" bounds
    :do (let* ((lbound (mo "binary operation" :av "type" 'bool :av "op" "<=" :av "left" 0 :av "right" index :av "actuated" t))
                (hbound (mo "binary operation" :av "type" 'bool :av "op" "<" :av "left" index :av "right" val :av "actuated" t))
                (bound (mo "binary operation" :av "type" 'bool :av "op" "&&" :av "left" lbound :av "right" hbound :av "actuated" t))) 
            (if rest
                (progn (update-push-aclosure c :av "collected" (cons index coll) :av "accesses" (cdr rest) :av "bounds" (cons bound bounds))
                    (clear-update-eval-aclosure c :av "instance" (car rest)))
                (update-push-aclosure c :av "stage" 'complete :av "collected" (cons index coll) :av "bounds" (cons bound bounds))))
)
(aclosure c :attribute "axsem" :type ".++" :stage 'complete
    :instance i 
    :ap i (aseq "access" "variable") name 
    :ap "collected" coll 
    :env env 
    :agent a
    :ap a "state" state 
    :ap "bounds" bounds
    :do (let* ((new-coll (reverse coll))
                (access (mo "variable access" :av "name" name :av "path" new-coll))
                (var-type (get-variable-type env name new-coll))
                (getter (mo "value getter" :av "type" var-type :av "state" state :av "name" access :av "actuated" t))
                (new-val (mo "binary operation" :av "type" var-type :av "op" "+" :av "left" getter :av "right" 1 :av "actuated" t))
                (setter (mo "value setter" :av "type" var-type :av "state" state :av "name" access :av "value" new-val)))
            (if (not (null bounds))
                (let ((domain (mo "conjunction" :av "formulas" bounds))) 
                    (finalize-lemma a env domain)
                    (cons-to-inner-list a (aseq "precond") domain)))
            (aset a "state" setter)
            getter)
)

(aclosure c :attribute "axsem" :type "--." :stage nil
    :instance i 
    :ap i "access" access 
    :ap access "accesses" rst
    :do (update-push-aclosure c :av "stage" 'access :av "accesses" (cdr rst))
        (clear-update-eval-aclosure c :av "instance" (cdr rst))
)
(aclosure c :attribute "axsem" :type "--." :stage 'access
    :instance i     
    :ap "accesses" rst 
    :ap "collected" coll
    :value val 
    :do (if (stringp val)
            (if rest 
                (progn
                    (update-push-aclosure c :av "collected" (cons val coll) :av "accesses" (cdr rest))
                    (clear-update-eval-aclosure c :av "instance" (car rest)))
                (update-push-aclosure c :av "stage" 'complete :av "collected" (cons val coll)))
            (progn (update-push-aclosure c :av "stage" 'access-act)
                (clear-update-eval-aclosure c :av "attribute" "actuate" :av "instance" val)))
)
(aclosure c :attribute "axsem" :type "--." :stage 'access-act
    :instance i  
    :ap "accesses" rst 
    :ap "collected" coll 
    :value val 
    :ap i "variable" name
    :do (update-push-aclosure c :av "stage" 'domain :av "collected" (cons val coll) :av "accesses" (cdr rst) :av "index" val)
        (clear-update-eval-aclosure c :av "instance" (get-array-size env name (reverse coll)))
)
(aclosure c :attribute "axsem" :type "--." :stage 'domain
    :instance i  
    :ap "accesses" rst 
    :ap "collected" coll
    :value val
    :ap "index" index 
    :ap "bounds" bounds
    :do (let* ((lbound (mo "binary operation" :av "type" 'bool :av "op" "<=" :av "left" 0 :av "right" index :av "actuated" t))
                (hbound (mo "binary operation" :av "type" 'bool :av "op" "<" :av "left" index :av "right" val :av "actuated" t))
                (bound (mo "binary operation" :av "type" 'bool :av "op" "&&" :av "left" lbound :av "right" hbound :av "actuated" t))) 
            (if rest
                (progn (update-push-aclosure c :av "collected" (cons index coll) :av "accesses" (cdr rest) :av "bounds" (cons bound bounds))
                    (clear-update-eval-aclosure c :av "instance" (car rest)))
                (update-push-aclosure c :av "stage" 'complete :av "collected" (cons index coll) :av "bounds" (cons bound bounds))))
)
(aclosure c :attribute "axsem" :type "--." :stage 'complete
    :instance i 
    :ap i (aseq "access" "variable") name 
    :ap "collected" coll 
    :env env 
    :agent a
    :ap a "state" state 
    :ap "bounds" bounds
    :do (let* ((new-coll (reverse coll))
                (access (mo "variable access" :av "name" name :av "path" new-coll))
                (var-type (get-variable-type env name new-coll))
                (getter (mo "value getter" :av "type" var-type :av "state" state :av "name" access :av "actuated" t))
                (new-val (mo "binary operation" :av "type" var-type :av "op" "-" :av "left" getter :av "right" 1 :av "actuated" t))
                (setter (mo "value setter" :av "type" var-type :av "state" state :av "name" access :av "value" new-val)))
            (if (not (null bounds))
                (let ((domain (mo "conjunction" :av "formulas" bounds))) 
                    (finalize-lemma a env domain)
                    (cons-to-inner-list a (aseq "precond") domain)))
            (aset a "state" setter)
            (if (null coll)
                (mo "value getter" :av "type" var-type :av "state" (aget a "state") :av "name" access :av "actuated" nil)
                new-val)
        )
)


(aclosure c :attribute "axsem" :type ".--" :stage nil
    :instance i 
    :ap i "access" access 
    :ap access "accesses" rst
    :do (update-push-aclosure c :av "stage" 'access :av "accesses" (cdr rst))
        (clear-update-eval-aclosure c :av "instance" (cdr rst))
)
(aclosure c :attribute "axsem" :type ".--" :stage 'access
    :instance i     
    :ap "accesses" rst 
    :ap "collected" coll
    :value val 
    :do (if (stringp val)
            (if rest 
                (progn
                    (update-push-aclosure c :av "collected" (cons val coll) :av "accesses" (cdr rest))
                    (clear-update-eval-aclosure c :av "instance" (car rest)))
                (update-push-aclosure c :av "stage" 'complete :av "collected" (cons val coll)))
            (progn (update-push-aclosure c :av "stage" 'access-act)
                (clear-update-eval-aclosure c :av "attribute" "actuate" :av "instance" val)))
)
(aclosure c :attribute "axsem" :type ".--" :stage 'access-act
    :instance i  
    :ap "accesses" rst 
    :ap "collected" coll 
    :value val 
    :ap i "variable" name
    :do (update-push-aclosure c :av "stage" 'domain :av "collected" (cons val coll) :av "accesses" (cdr rst) :av "index" val)
        (clear-update-eval-aclosure c :av "instance" (get-array-size env name (reverse coll)))
)
(aclosure c :attribute "axsem" :type ".--" :stage 'domain
    :instance i  
    :ap "accesses" rst 
    :ap "collected" coll
    :value val
    :ap "index" index 
    :ap "bounds" bounds
    :do (let* ((lbound (mo "binary operation" :av "type" 'bool :av "op" "<=" :av "left" 0 :av "right" index :av "actuated" t))
                (hbound (mo "binary operation" :av "type" 'bool :av "op" "<" :av "left" index :av "right" val :av "actuated" t))
                (bound (mo "binary operation" :av "type" 'bool :av "op" "&&" :av "left" lbound :av "right" hbound :av "actuated" t))) 
            (if rest
                (progn (update-push-aclosure c :av "collected" (cons index coll) :av "accesses" (cdr rest) :av "bounds" (cons bound bounds))
                    (clear-update-eval-aclosure c :av "instance" (car rest)))
                (update-push-aclosure c :av "stage" 'complete :av "collected" (cons index coll) :av "bounds" (cons bound bounds))))
)
(aclosure c :attribute "axsem" :type ".--" :stage 'complete
    :instance i 
    :ap i (aseq "access" "variable") name 
    :ap "collected" coll 
    :env env 
    :agent a
    :ap a "state" state 
    :ap "bounds" bounds
    :do (let* ((new-coll (reverse coll))
                (access (mo "variable access" :av "name" name :av "path" new-coll))
                (var-type (get-variable-type env name new-coll))
                (getter (mo "value getter" :av "type" var-type :av "state" state :av "name" access :av "actuated" t))
                (new-val (mo "binary operation" :av "type" var-type :av "op" "-" :av "left" getter :av "right" 1 :av "actuated" t))
                (setter (mo "value setter" :av "type" var-type :av "state" state :av "name" access :av "value" new-val)))
            (if (not (null bounds))
                (let ((domain (mo "conjunction" :av "formulas" bounds))) 
                    (finalize-lemma a env domain)
                    (cons-to-inner-list a (aseq "precond") domain)))
            (aset a "state" setter)
            getter)
)

(aclosure c :attribute "axsem" :type "process state checking" :stage nil
    :instance i 
    :env env 
    :agent a
    :do (update-push-aclosure c :av "stage" 'true :av "agent" (iclone-agent env a))
        (update-push-aclosure c :av "stage" 'false)
)
(aclosure c :attribute "axsem" :type "process state checking" :stage 'true
    :instance i 
    :ap i "process" process 
    :ap i "activity" activity
    :env env 
    :agent a
    :do (if (insert-proc-act a process activity)
            t
            (delete-agent-aclosures env a))
)
(aclosure c :attribute "axsem" :type "process state checking" :stage 'false
    :instance i 
    :ap i "process" process 
    :ap i "activity" activity
    :env env 
    :agent a
    :do (if (insert-proc-act a process (invert-activity activity))
            nil
            (delete-agent-aclosures env a))
)

;Transformations: statements

;add-cons-attributes

(defun update-attributes (agent new-attributes)
    (aset agent "cur attr" (add-cons-attributes (aget agent "cur attr") new-attributes)))

(aclosure c :attribute "axsem" :type "reset time"
    :instance i 
    :agent a
    :do (aset a (aseq "cur attr" "reset") t)
        (cons-to-inner-list a (list "cur cond") (mo "reset"))
)
(aclosure c :attribute "axsem" :type "set state"
    :instance i 
    :ap i "state" state
    :env env 
    :agent a 
    :ap a "current process" current-process 
    :do (update-attributes a (aget i "analysis attributes"))
        (if state 
            (progn 
                (cons-to-inner-list a (list "cur cond") (mo "pstate setter" :av "process" current-process :av "state" state)))
            (let ((next-state (next-process-state a env)))
                (cons-to-inner-list a (list "cur cond") (mo "pstate setter" :av "process" current-process :av "state" next-state))))
)
(aclosure c :attribute "axsem" :type "restart process"
    :instance i 
    :env env
    :agent a 
    :ap a "current process" current-process 
    :do (update-attributes a (aget i "analysis attributes")) 
        (cons-to-inner-list a (list "cur cond") (mo "pstate setter" :av "process" current-process :av "state" (current-first-state a env)))
        (cons-to-inner-list a (list "processes to start") current-process)
)
(aclosure c :attribute "axsem" :type "start process"
    :instance i 
    :ap i "process" process
    :env env
    :agent a 
    :ap a "current process" current-process 
    :do (update-attributes a (aget i "analysis attributes"))
        (if (= current-process process)
            (clear-update-eval-aclosure c :av "instance" (mo "restart process"))
            (progn (cons-to-inner-list a (list "cur cond") (mo "pstate setter" :av "process" process :av "state" (first-state env process)))
                (cons-to-inner-list a (list "processes to start") process)))
)
(aclosure c :attribute "axsem" :type "stop current process"
    :instance i 
    :agent a 
    :ap a "current process" current-process 
    :do (update-attributes a (aget i "analysis attributes"))
        (cons-to-inner-list a (aseq "cur cond") (mo "pstate setter" :av "process" current-process :av "state" "stop"))
)
(aclosure c :attribute "axsem" :type "stop process"
    :instance i 
    :ap i "process" process
    :agent a 
    :ap a "current process" current-process
    :do (update-attributes a (aget i "analysis attributes"))
        (if (= current-process process)
            (clear-update-eval-aclosure c :av "instance" (mo "stop current process"))
            (progn (cons-to-inner-list a (aseq "cur cond") (mo "pstate setter" :av "process" process :av "state" "stop"))))
)
(aclosure c :attribute "axsem" :type "error current process"
    :instance i 
    :agent a 
    :ap a "current process" current-process
    :do (update-attributes a (aget i "analysis attributes"))
        (cons-to-inner-list a (aseq "cur cond") (mo "pstate setter" :av "process" current-process :av "state" "error"))
)
(aclosure c :attribute "axsem" :type "error process"
    :instance i 
    :ap i "process" process
    :agent a 
    :ap a "current process" current-process
    :do (update-attributes a (aget i "analysis attributes"))
        (if (= current-process process)
            (clear-update-eval-aclosure c :av "instance" (mo "error current process"))
            (progn (cons-to-inner-list a (aseq "cur cond") (mo "pstate setter" :av "process" process :av "state" "error"))))
)
(aclosure c "axsem" "if then else statement" :stage nil 
    :instance i
    :p (aget i "condition") cnd 
    :do (update-push-aclosure c :av "stage" 'cond)
        (clear-update-eval-aclosure c :av "instance" cnd)
)
(aclosure c "axsem" "if then else statement" :stage 'cond 
    :value cnd
    :do (update-push-aclosure c :av "stage" 'cond-act)
        (clear-update-eval-aclosure c :av "instance" cnd)
)
(aclosure c "axsem" "if then else statement" :stage 'cond-act
    :env env
    :agent a 
    :value cnd
    :do (if (finalize-expression c)
            (progn (clear-agent-expr a)
                (update-push-aclosure c :av "stage" 'false :av "agent" (iclone-agent env a) :av "cnd" cnd)
                (update-push-aclosure c :av "stage" 'true :av "cnd" cnd))
            (delete-agent-aclosures env a))
)
(aclosure c "axsem" "if then else statement" :stage 'true
    :env env
    :agent a 
    :value cnd
    :instance i 
    :p (aget i "then") then
    :do (case cnd 
            ('true (clear-update-eval-aclosure c :av "instance" then))
            ('false (delete-agent-aclosures env a))
            (otherwise (if  (check-compatability c cnd)
                            (progn (cons-to-inner-list a (list "cur cond") cnd)
                                (clear-update-eval-aclosure c :av "instance" then))
                            (delete-agent-aclosures env a))))
)
(aclosure c "axsem" "if then else statement" :stage 'false
    :env env
    :agent a 
    :value cnd
    :instance i 
    :p (aget i "else") else
    :do (case cnd 
            ('false (clear-update-eval-aclosure c :av "instance" else))
            ('true (delete-agent-aclosures env a))
            (otherwise (let ((new-cnd (mo "unary operator" 
                                :av "type" bool-constant 
                                :av "op" "!" 
                                :av "value" cnd 
                                :av "actuated" t)))
                        (if (check-compatability c new-cnd))
                            (progn (cons-to-inner-list a (list "cur cond") new-cnd)
                                (clear-update-eval-aclosure c :av "instance" else))
                            (delete-agent-aclosures env a))))
)       

(aclosure c :attribute "axsem" :type "if then statement" :stage nil
    :instance i 
    :ap i "condition" cnd
    :do (update-push-aclosure c :av "stage" 'cond)
        (clear-update-eval-aclosure c :av "instance" cnd)
)
(aclosure c :attribute "axsem" :type "if then statement" :stage 'cond
    :instance i 
    :value cnd
    :do (update-push-aclosure c :av "stage" 'cond-act)
        (clear-update-eval-aclosure c :av "instance" cnd :av "attribute" "actuate")
)
(aclosure c :attribute "axsem" :type "if then statement" :stage 'cond-act
    :instance i 
    :env env 
    :agent a 
    :value cnd
    :do (if (finalize-expression c)
            (progn (clear-agent-expr a)
                (update-push-aclosure c :av "stage" 'false :av "agent" (iclone-agent env a) :av "cnd" cnd)
                (update-push-aclosure c :av "stage" 'true :av "cnd" cnd))
            (delete-agent-aclosures env a))
)
(aclosure c :attribute "axsem" :type "if then statement" :stage 'true
    :instance i 
    :agent a 
    :env env
    :ap "cnd" cnd 
    :ap i "then" then 
    :do (case cnd 
            ('true (clear-update-eval-aclosure c :av "instance" then))
            ('false (delete-agent-aclosures env a))
            (otherwise (if  (check-compatability c cnd)
                            (progn (cons-to-inner-list a (aseq "cur cond") cnd)
                                (clear-update-eval-aclosure c :av "instance" then))
                            (delete-agent-aclosures env a))))
)
(aclosure c :attribute "axsem" :type "if then statement" :stage 'false
    :instance i 
    :agent a 
    :env env
    :ap "cnd" cnd 
    :do (case cnd 
            ('false nil)
            ('true (delete-agent-aclosures env a))
            (otherwise (let ((new-cnd (mo "unary operator" :av "type" bool-constant :av "op" "!" :av "value" cnd :av "actuated" t)))
                        (if (check-compatability c new-cnd))
                            (cons-to-inner-list a (aseq "cur cond") new-cnd)
                            (delete-agent-aclosures env a))))   
)

(aclosure c :attribute "axsem" :type "switch statement" :stage nil
    :instance i 
    :ap i "controlling expression" cnd
    :do (update-push-aclosure c :av "stage" 'cond)
        (clear-update-eval-aclosure c :av "instance" cnd)
)
(aclosure c :attribute "axsem" :type "switch statement" :stage 'cond
    :instance i 
    :value cnd
    :do (update-push-aclosure c :av "stage" 'cond-act)
        (clear-update-eval-aclosure c :av "instance" cnd)
)
(aclosure c :attribute "axsem" :type "switch statement" :stage 'cond-act
    :instance i 
    :value cnd 
    :env env 
    :ap i "cases" css
    :do (if css
            ()
            (if (finalize-expression a)
                (progn (clear-agent-expr a)
                    (update-push-aclosure c :av "stage" 'cases-label :av "cnd" cnd :av "cases" css))
                (delete-agent-aclosures env a)) 
        )
)
(aclosure c :attribute "axsem" :type "switch statement" :stage 'cases-label
    :instance i 
    :env env 
    :agent a 
    :ap "cases" css
    :ap "cnd" cnd 
    :do (if css
            (let ((clone (iclone-agent env a)))
                (update-push-aclosure c :av "stage" 'case-iter-false :av "agent" clone)
                (update-push-aclosure c :av "stage" 'case-iter-true))
            (update-push-aclosure c :av "stage" 'default))
)
(aclosure c :attribute "axsem" :type "switch statement" :stage 'case-iter-true
    :instance i 
    :env env 
    :agent a 
    :ap "cases" css
    :p (car css) cs
    :ap "cnd" cnd 
    :do (let* ((label (aget cs "label"))
                (expr (mo "binary operation" :av "op" "==" :av "type" bool :av "left" cnd :av "right" label :av "actuated" t)))
            (cons-to-inner-list a (aseq "cur cond") expr)
            (if (not (aget cs "break"))
                (update-push-aclosure c :av "stage" 'cont-case-iter :av "cases" (cdr css)))
            (clear-update-eval-aclosure c :av "instance" cs))
)
(aclosure c :attribute "axsem" :type "switch statement" :stage 'case-iter-false
    :instance i 
    :env env 
    :agent a 
    :ap "cases" css
    :p (car css) cs
    :ap "cnd" cnd 
    :do (let* ((label (aget cs "label"))
                (expr (mo "binary operation" :av "op" "!=" :av "type" bool :av "left" cnd :av "right" label :av "actuated" t)))
            (cons-to-inner-list a (aseq "cur cond") expr)
            (update-push-aclosure c :av "stage" 'case-label :av "cases" (cdr css)))
)
(aclosure c :attribute "axsem" :type "switch statement" :stage 'cont-case-iter
    :instance i 
    :env env 
    :agent a 
    :ap "cases" css
    :p (car css) cs
    :ap "cnd" cnd    
    :do (if css
            (progn (if (not (aget cs "break"))
                    (update-push-aclosure c :av "cases" (cdr css)))
                (clear-update-eval-aclosure c :av "instance" (car css)))
            (update-push-aclosure c :av "stage" 'default))
)
(aclosure c :attribute "axsem" :type "switch statement" :stage 'default
    :instance i 
    :ap i "default" default
    :do (if default 
            (clear-update-eval-aclosure c :av "instance" default))
)

(aclosure c :attribute "axsem" :type "statement list" :stage nil 
    :instance i 
    :do (update-push-aclosure c :av "stage" 'statements :av "sts" i))
(aclosure c :attribute "axsem" :type "statement list" :stage 'statements 
    :ap "sts" sts 
    :do (if sts 
            (progn (update-push-aclosure c :av "sts" (cdr sts))
                (clear-update-eval-aclosure c :av "instance" (car sts)))))

(aclosure c :attribute "axsem" :type "default statement"
    :instance i 
    :ap i "statements" sts
    (clear-update-eval-aclosure c :av "instance" sts)     
)

(aclosure c :attribute "axsem" :type "case statement"
    :instance i 
    :ap i "statements" sts
    (clear-update-eval-aclosure c :av "instance" sts)   
)

(aclosure c :attribute "axsem" :type "statement block"
    :instance i 
    :ap i "statements" sts
    (clear-update-eval-aclosure c :av "instance" sts) 
)

(aclosure c :attribute "axsem" :type "expression statement" :stage nil 
    :instance i
    :ap i "expression" expr
    :do (update-push-aclosure c :av "stage" 'next)
        (clear-update-eval-aclosure c :av "instance" expr)
)
(aclosure c :attribute "axsem" :type "expression statement" :stage 'next 
    :instance i
    :agent a
    :do (if (finalize-expression a)
            (clear-agent-expr a)
            (delete-agent-aclosures env a))
)

(aclosure c :attribute "axsem" :type "timeout statement" :stage nil
    :instance i 
    :ap i "controlling expression" cnd
    :do (update-push-aclosure c :av "stage" 'cond)
        (clear-update-eval-aclosure c :av "instance" cnd)
)
(aclosure c :attribute "axsem" :type "timeout statement" :stage 'cond
    :instance i 
    :value cnd
    :do (update-push-aclosure c :av "stage" 'cond-act)
        (clear-update-eval-aclosure c :av "instance" cnd)
)
(aclosure c :attribute "axsem" :type "timeout statement" :stage 'cond-act
    :instance i 
    :value cnd
    :do (update-push-aclosure c :av "stage" 'not-exceed :av "cnd" cnd)
        (update-push-aclosure c :av "stage" 'exceed :av "cnd" cnd)
)
(aclosure c :attribute "axsem" :type "timeout statement" :stage 'exceed
    :instance i 
    :agent a 
    :ap a "current process" process
    :ap "cnd" cnd 
    :ap i "statements" sts
    :p (mo "ltime check" :av "state" "blank" :av "process" process  :av "comapre val" cnd :av "exceed" t) new-cnd
    :do (if (check-compatability c new-cnd)
            (progn (cons-to-inner-list a (aseq "cur cond") new-cnd)
                (clear-update-eval-aclosure c :av "instance" sts))
            (delete-agent-aclosures c))
)
(aclosure c :attribute "axsem" :type "timeout statement" :stage 'not-exceed
    :instance i 
    :agent a 
    :ap a "current process" process
    :ap "cnd" cnd 
    :p (mo "ltime check" :av "state" "blank" :av "process" process  :av "comapre val" cnd :av "exceed" nil) new-cnd 
    :do (if (check-compatability c new-cnd)
            (cons-to-inner-list a (aseq "cur cond") new-cnd)
            (delete-agent-aclosures c))
)

(aclosure c :attribute "axsem" :type "wait" :stage nil 
    :instance i 
    :ap i "condition" cnd
    :do (update-push-aclosure c :av "stage" 'cnd)
        (clear-update-eval-aclosure c :av "instance" cnd)
)
(aclosure c :attribute "axsem" :type "wait" :stage 'cnd 
    :instance i 
    :value cnd 
    :do (clear-update-eval-aclosure c :av "instance" cnd :av "attribute" "actuate")
)
(aclosure c :attribute "axsem" :type "slice"
    :instance i nil)

(aclosure c :attribute "axsem" :type "transition"
    :instance i 
    :do (match :av c "stage" nil :ap i "condition" cnd :do 
        (update-push-aclosure c :av "stage" 'cnd)
        (clear-update-eval-aclosure c :av "instance" cnd))
    (match :av c "stage" 'cnd :av c "stage" 'actuated :ap c "agent" a :av a "value" cnd :do
        (clear-update-eval-aclosure c :av "instance" cnd :av "attribute" "actuate"))
)

(aclosure c :attribute "axsem" :type "state declaration" :stage nil 
    :instance i 
    :env env 
    :agent a 
    :ap i "name" name 
    :ap i "statements" sts
    :do (aset a (aseq "cur attr" "reach from") (aget i (aseq "analysis attributes" "reach from"))) 
        (aset a "current state" name)
        (update-push-aclosure c :av "stage" 'conclude)
        (clear-update-eval-aclosure c :av "instance" sts)
)   
(aclosure c :attribute "axsem" :type "state declaration" :stage 'conclude 
    :instance i
    :agent a 
    :do (aset a (aseq "cur attr" "reset") nil)
        (aset a (aseq "cur attr" "changes to") nil)
        (aset a (aseq "cur attr" "pot process change") nil)
        (aset a (aseq "cur attr" "state changed") nil)
)
#|(aclosure c :attribute "axsem" :type "state declaration"
    :instance i 
    (match :av c "stage" nil :ap c "env" env :ap c "agent" a :ap i "name" name :ap i "statements" sts :do
        (aset a (aseq "cur attr" "reach from") (aget i (aseq "analysis attributes" "reach from")))
        (aset a "current state" name)
        (update-push-aclosure c :av "stage" 'conclude)
        (update-push-aclosure c :av "stage" 'statements :av "sts" sts :av "clear agent" (iclone-agent env a)))
    (match :av c "stage" 'statements :ap i "statements" sts :ap c "agent" a :ap c "clear agent" cagent :do 
        (if (< index length)
            (progn (if (is-instance (car sts) barrier-statement)
                    (update-push-aclosure c :av "stage" 'barrier)
                    (update-push-aclosure c :av "stage" 'statements :av "sts" (cdr sts)))
                (clear-update-eval-aclosure c :av "instance" (car sts)))))
    (match :av c "stage" 'barrier :ap c "sts" sts :ap c "env" env :ap c "clear agent" cagent :ap c "agent" a :ap a "value" cnd :do 
        ;
        (cond
            ((is-instance (car sts) wait) 
                (let ((init-clone1 (iclone-agent env cagent))
                        (init-clone2 (iclone-agent env cagent))
                        (clone (iclone-agent env a)))
                    (cons-to-inner-list init-clone1 (list "cur cond") (mo "unary operation" :av "type" bool :av "op" "!." :av "right" cnd :av "actuated" t))
                    (update-push-aclosure c :av "stage" 'nothing :av "agent" init-clone1)
                    
                    (cons-to-inner-list clone (aseq "cur cond") (mo "unary operation" :av "type" bool :av "op" "!." :av "right" cnd :av "actuated" t))
                    (update-push-aclosure c :av "stage" 'nothing :av "agent" clone)
                    
                    (cons-to-inner-list init-clone2 (list "cur cond") cnd)
                    (update-push-aclosure c :av "stage" 'statements :av "agent" init-clone2 :av "sts" (cdr sts))
                    
                    (cons-to-inner-list a (aseq "cur cond") cnd)
                    (update-push-aclosure c :av "stage" 'statements :av "agent" clone :av "sts" (cdr sts))))
            ((is-instance (car sts) slice)
                (let ((clone (iclone-agent env cagent)))
                    (update-push-aclosure c :av "stage" 'nothing)
                    (update-push-aclosure c :av "stage" 'statements :av "agent" clone :av "sts" (cdr sts))))
            ((is-instance (car sts) slice) 
                (let ((init-clone1 (iclone-agent env cagent))
                        (init-clone2 (iclone-agent env cagent)))
                    (update-push-aclosure c :av "stage" 'nothing)
                    
                    (cons-to-inner-list init-clone1 (list "cur cond") (mo "unary operation" :av "type" bool :av "op" "!." :av "right" cnd :av "actuated" t))
                    (update-push-aclosure c :av "stage" 'nothing :av "agent" init-clone1)
                    
                    (cons-to-inner-list init-clone2 (list "cur cond") cnd)
                    (update-push-aclosure c :av "stage" 'statements :av "agent" init-clone2 :av "sts" (cdr sts))))))
    (match :av c "stage" 'conclude :ap c "agent" a 
    :do (aset a (aseq "cur attr" "reset") nil)
        (aset a (aseq "cur attr" "changes to") nil)
        (aset a (aseq "cur attr" "pot process change") nil)
        (aset a (aseq "cur attr" "state changed") nil))  

)|#

(aclosure c :attribute "axsem" :type "process declaration" :stage nil 
    :instance i 
    :agent a 
    :env env
    :ap i "name" name 
    :ap i "states" states
    :do (aset a (aseq "cur attr" "reachS") (aget i (aseq "analysis attributes" "reachS")))
        (aset a (aseq "cur attr" "reachE") (aget i (aseq "analysis attributes" "reachE")))
        (aset a (aseq "cur attr" "startS") (aget i (aseq "analysis attributes" "startS")))
        (aset a "current process" name)
        (update-push-aclosure c :av "stage" 'states :av "rest" states :av "clear agent" a)
)
(aclosure c :attribute "axsem" :type "process declaration" :stage 'states 
    :instance i 
    :ap i "name" name 
    :env env
    :ap "clear agent" a
    :ap "rest" rst
    :do (if rst 
            (let* ((cur-state (car rst))
                    (pstate-name (aget cur-state "name"))
                    (new-pstate (mo "pstate compare" :av "stage" "blank" :av "process" name :av "pstate" pstate-name)))
                (update-push-aclosure c :av "rest" (cdr rst))
                (if (check-compatability c new-pstate)
                    (let ((new-agent (iclone-agent env a)))
                        (cons-to-inner-list new-agent (list "cur-cond") new-pstate)
                        (clear-update-eval-aclosure c :av "agent" new-agent :av "instance" cur-state))))
            (update-push-aclosure c :av "stage" 'stop))
)
(aclosure c :attribute "axsem" :type "process declaration" :stage 'stop 
    :instance i 
    :ap i "name" name
    :env env 
    :ap "clear agent" a 
    :p (mo "pstate compare" :av "stage" "blank" :av "process" name :av "pstate" "stop") new-pstate 
    :do (if (check-compatability c new-pstate)
            (let ((new-agent (iclone-agent env a)))
                (cons-to-inner-list new-agent (list "cur-cond") new-pstate)))
        (update-push-aclosure c :av "stage" 'error)
)
(aclosure c :attribute "axsem" :type "process declaration" :stage 'error 
    :instance i 
    :ap i "name" name
    :env env 
    :ap "clear agent" a 
    :p (mo "pstate compare" :av "stage" "blank" :av "process" name :av "pstate" "error") new-pstate
    :do (if (check-compatability c new-pstate)
            (cons-to-inner-list a (list "cur-cond") new-pstate)
            (delete-agent-aclosures a))
)

(aclosure c :attribute "axsem" :type "program declaration" :stage nil
    :instance i 
    :do (aset c (aseq "env" "program" i))
        (update-push-aclosure c :av "stage" 'init-input)
)
(aclosure c :attribute "axsem" :type "program declaration" :stage 'init-input
    :instance i 
    :agent a 
    :ap "input" input
    :do (if input 
            (let* ((name (aget (car input) "name"))
                    (var-type (aget env (aseq "variable type" "name"))))
                (update-push-aclosure c (cdr input))
                (cons-to-inner-list a "cur cond" (mo "value setter" :av "type" var-type :av "state" "blank" :av "name" name :av "value" name))
            )
            (update-push-aclosure c :av "stage" 'work :av "procs" (aget i "processes")))
)
(aclosure c :attribute "axsem" :type "program declaration" :stage 'work
    :instance i 
    :agent a
    :ap "procs" procs 
    :do (if procs
            (progn
                (update-push-aclosure c :av "stage" 'init-started)
                (clear-update-eval-aclosure c :av "instance" (car procs)))
            (update-push-aclosure c :av "stage" 'conclude)
        )
)
(aclosure c :attribute "axsem" :type "program declaration" :stage 'init-started
    :instance i
    :agent a
    :ap a "processes to start" procs-to-start
    :do (if procs-to-start 
            (let ((proc-name (car procs-to-start))) 
                (push-aclosure c)
                (eval-aclosure (aset (clear-aclosure c) 
                    :av "attribute" "axsem init" 
                    :av "instance" (car (member (lambda (process) (member (lambda (proc) (equal proc-name proc)) (procs-to-start))) (aget i "processes"))))))
            (update-push-aclosure c :av "stage" 'work))
)
(aclosure c :attribute "axsem" :type "program declaration" :stage 'conclude
    :instance i
    :agent a 
    :env env
    :do (finalize-base-lemma a env)
        (update-push-aclosure c :av "stage" 'print-lemma)
)
(aclosure c :attribute "axsem" :type "program declaration" :stage 'print-lemma
    :instance i
    :agent a 
    :env env 
    :do
)

(aclosure c :attribute "axsem prepare" :type "program declaration" :stage nil 
    :do (update-push-aclosure c :av "stage" 'prepare :av "steps" (list "map name" "type spec" "normalize program" "axsem decl" "axsem init" "attribute prepare"))
)
(aclosure c :attribute "axsem prepare" :type "program declaration" :stage 'prepare 
    :instance i
    :ap "steps" sts
    :do (if sts 
            (progn (update-push-aclosure c :av "staps" (cdr sts))
                (clear-update-eval-aclosure c :av "attribute" (car sts) :av "instance" i))
            (progn (set-mode-prepare c)
                (check-compatability c nil)))
)



;axsem decl
(aclosure c :attribute "axsem decl" :type "constant declaration" :stage nil 
    :instance i 
    :ap i "expression" expr
    :do (update-push-aclosure c :av "stage" 'val)
        (clear-update-eval-aclosure c :av "instance" expr)
)
(aclosure c :attribute "axsem decl" :type "constant declaration" :stage val 
    :instance i 
    :ap i "name" name
    :value val 
    :do (aset a (aseq "variable value" name) val))
        
(aclosure c :attribute "axsem decl" :type "simple variable declaration" :stage nil
    :instance i 
    :ap i "init" init 
    :ap i "type" rtype
    :ap i "name" name
    :env env 
    :do (aset env (aseq "variable init" name) (if init init (type-default-val env rtype)))
        (aset env (aseq "variable type" name) rtype)
)

(aclosure c :attribute "axsem decl" :type "array variable declaration" :stage nil
    :instance i
    :ap i "init" init 
    :ap i "type" rtype 
    :ap i "size" size
    :ap i "name" name
    :env env
    :do (aset env (aseq "variable init" name) (if init init (type-default-val env rtype)))
        (aset env (aseq "variable type" name) rtype)
)

(aclosure c :attribute "axsem decl" :type "imported variable declaration"
    :instance i 
    nil)

(aclosure c :attribute "axsem decl" :type "physical variable declaration"
    :instance i 
    :ap i "name" name 
    :ap i "type" rtype 
    :ap i "port" pname
    :env env 
    :do (if (equal (aget env (aseq "port type" pname)) 'input)
            (progn (aset env "input variables" (adjoin (aget env "input variables") name))
                (aset env (aseq "variable type" name ) rtype ))
            (progn (aset env "output variables" (adjoin (aget env "input variables") name))
                (aset env (aseq "variable type" name ) rtype)))
)

(aclosure c :attribute "axsem decl" :type "structure declaration" :stage nil
    :instance i 
    :ap i "fields" fields 
    :ap i "name" name
    :do (update-push-aclosure c :av "stage" 'fields :av "fields" fields)
)
(aclosure c :attribute "axsem decl" :type "structure declaration" :stage 'fields
    :instance i
    :ap "fields" fields 
    :ap i "name" name
    :env env
    :do (if fields
            (let ((field (car fields)))
                (progn (update-push-aclosure c :av "fields" (cdr fields))
                (aset env (aseq "struct types" name (aget field "name")) (aget field "type")))))
)

(aclosure c :attribute "axsem decl" :type "structure variable declaration"
    :instance i 
    :ap i "name" name
    :ap i "type" rtype 
    :ap i "init" init
    :env env
    :do (aset env (aseq "variable type" name) rtype)
        (if init 
            (aset env (aseq "variable init" name) init)
            (aset env (aseq "variable init" name) (type-default-val env rtype)))
)

(aclosure c :attribute "axsem decl" :type "enum declaration" :stage nil
    :instance i 
    :ap i "fileds" fields
    :do (update-push-aclosure c :av "stage" 'fields :av "fields" fields :av "last value" -1)
)
(aclosure c :attribute "axsem decl" :type "enum declaration" :stage 'fields
    :instance i 
    :ap "fileds" fields
    :ap c "last value" lv
    :env env
    :ap i "name" name
    :p (car fields) field
    :do (if fields
            (if (aget field "value")
                (progn (update-push-aclosure c :av "fields" (cdr fields) :av "last value" (aget field "value"))
                    (aset env (aseq "enum value" name (aget field "name")) (aget field "value")))
                (progn (update-push-aclosure c :av "fields" (cdr fields) :av "last value" (+ lv 1))
                    (aset env (aseq "enum value" name (aget field "name")) (+ lv 1)))))
)

(aclosure c :attribute "axsem decl" :type "enum variable declaration"
    :instance i 
    :ap i "init" init 
    :ap i "type" rtype
    :env env 
    :do (if init 
            (aset env (aseq "variable init" name) init)
            (aset env (aseq "variable init" name) (type-default-val env rtype)))
)

(aclosure c :attribute "axsem decl" :type "port declaration"
    :instance i 
    :env env 
    :ap i "name" name 
    :ap i "port type" pt
    :do (aset env (aseq "port type" name ) pt)
)

(aclosure c :attribute "axsem decl" :type "process declaration" :stage nil
    :instance i 
    :ap i "variables" variables
    :do (update-push-aclosure c :av "stage" 'decls :av "vars" variables )
)
(aclosure c :attribute "axsem decl" :type "process declaration" :stage 'decls
    :instance i 
    :ap i "name" name
    :ap "vars" vars 
    :env env
    :do (if vars
            (progn (update-push-aclosure c "vars" (cdr vars))
                (clear-update-eval-aclosure c :av "instance" (car vars)))
            (aset c (aseq "process states names" name) (reduce (lambda (col el) (append (aget el "name") col)) (aget i states))))
)

(aclosure c :attribute "axsem decl" :type "program decl" :stage nil
    :instance i 
    :ap i "clock" clock
    :do (update-push-aclosure c :av "stage" 'clock)
        (clear-update-eval-aclosure c :av "attribute" "opsem" :av "instance" clock)
)
(aclosure c :attribute "axsem decl" :type "program decl" :stage 'clock
    :instance i 
    :ap i "declarations" decls
    :value val
    :env env
    :do (aset env (aseq clock ) val)
        (update-push-aclosure c :av "stage" 'decls :av "decls" decls)
)
(aclosure c :attribute "axsem decl" :type "program decl" :stage 'decls
    :instance i 
    :ap "decls" decls
    :do (if decls 
            (progn (update-push-aclosure c "decls" (cdr decls))
                (clear-update-eval-aclosure c :av "instance" (car decls)))
            (update-push-aclosure c :av "stage" 'procs :av "procs" (aget i "processes")))
)
(aclosure c :attribute "axsem decl" :type "program decl" :stage 'procs
    :instance i 
    :ap "procs" procs
    :do (if procs 
            (progn (update-push-aclosure c "procs" (cdr procs))
                (clear-update-eval-aclosure c :av "instance" (car procs))))
)


;TODO axsem-init

(aclosure c :attribute "axsem init" :type "simple variable declaration"
    :instance i :do 
    (match :av c "stage" nil :ap i "name" name :ap c "env" env :do 
        (update-push-aclosure c :av "stage" 'val)
        (clear-update-eval-aclosure c :av "instance" (aget env (aseq "variable init" name)) :av "attribute" "axsem"))
    (match :av c "stage" 'val :ap c "agent" a :ap a "value" val :do 
        (update-push-aclosure c :av "stage" 'val-act)
        (clear-update-eval-aclosure c :av "instance" val :av "attribute" "actuate"))
    (match :av c "stage" 'val-act :ap c "agent" a :ap a "value" val  :ap c "env" env :ap i "name" name :do 
        (clear-agent-expr a)
        (cons-to-inner-list c (aseq "cur cond") (mo "value setter" :av "type" (aget env (aseq "variable type" name)) :av "state" "blank" :av "name" name :av "value" val )))
)

(aclosure c :attribute "opsem init" :type "array variable declaration"
    :instance i 
    (match :av c "stage" nil :ap i "name" name :ap c "env" env :do 
        (update-push-aclosure c :av "stage" 'to-init)
        (clear-update-eval-aclosure c :av "attribute" "opsem" :av "instance" (aget env (aseq "variable init" name))))
    (match :av c "stage" 'to-init :ap i "name" name :ap c "agent" a :ap a "value" val :do 
            (aset a (aseq "variable value" name) val))
)

(aclosure c :attribute "axsem init" :type "array variable declaration"
    :instance i 
    (match :av c "stage" nil :ap i "name" name :ap c "env" env :do 
        (update-push-aclosure c :av "stage" 'inits :av "inits" (aget env (aseq "variable init" name)) :av "index" 0))
    (match :av c "stage" 'inits :ap c "inits" inits :do 
        (if inits 
            (let ((init (car inits)))
                (update-push-aclosure c :av "stage" 'init :av "inits" (cdr inits))
                (clear-update-eval-aclosure c :av "instance" init :av "attribute" "axsem"))
            (update-push-aclosure c :av "stage" 'update)))
    (match :av c "stage" 'init :ap c "agent" a :ap a "value" val :do 
        (update-push-aclosure c :av "stage" 'init-act)
        (clear-update-eval-aclosure c :av "instance" val :av "attribute" "actuate"))
    (match :av c "stage" 'init-act :ap c "agent" a :ap a "value" val :ap i "name" name :ap c "env" env :ap c "vals" vals :do 
        (update-push-aclosure c :av "stage" 'inits :av "vals" (cons val vals))
        (clear-agent-expr a))
    (match :av c "stage" 'update :ap i "name" name :ap c "vals" vals :do
        (cons-to-inner-list a (aseq "cur cond")
            (mo "value setter" :av "type" (aget env (aseq "variable type" name)) :av "state" "blank" :av "name" name :av "value" (reverse vals))))
)

;TODO
(aclosure c :attribute "axsem init" :type "structure variable declaration"
    :instance i 
    (match :av c "stage" nil :ap i "name" name :ap c "env" env :do 
        (let ((init (aget env (aseq "variable init" name))))
            (update-push-aclosure c :av "stage" 'inits :av "inits" (attributes init) :av "init" init :av "index" 0)))
    (match :av c "stage" 'inits :ap c "inits" inits :ap c "init" init :do 
        (if inits 
            (let* ((init-name (car inits))
                    (init (aget init init-name)))
                (update-push-aclosure c :av "stage" 'init)
                (clear-update-eval-aclosure c :av "instance" init :av "attribute" "axsem"))
            (update-push-aclosure c :av "stage" 'update)))
    (match :av c "stage" 'init :ap c "agent" a :ap a "value" val :do 
        (update-push-aclosure c :av "stage" 'init-act)
        (clear-update-eval-aclosure c :av "instance" val :av "attribute" "actuate"))
    (match :av c "stage" 'init-act :ap c "agent" a :ap a "value" val :ap i "name" name :ap c "env" env :ap c "vals" vals :ap c "inits" inits :do 
        (update-push-aclosure c :av "stage" 'inits :av "inits" (cdr inits) :av "vals" (cons val vals))
        (clear-agent-expr a))
    (match :av c "stage" 'update :ap i "name" name :ap c "vals" vals :do
        (cons-to-inner-list a (aseq "cur cond")
            (mo "value setter" :av "type" (aget env (aseq "variable type" name)) :av "state" "blank" :av "name" name :av "value" (reverse vals))))
)



(aclosure c :attribute "axsem init" :type "enum variable declaration"
    :instance i 
    (match :ap i "name" name :ap c "env" env :ap c "env" env :do 
        (cons-to-inner-list c (aseq "cur cond") (mo "simple value setter" :av "type" (aget env (aseq "variable type" name)) :av "state" "blank" :av "name" name :av "value" (aget env (aseq "variable init" name)) )))
)

(aclosure c :attribute "axsem init" :type "process declaration"
    :instance i 
    (match :av c "stage" nil :ap c "agent" a :ap c "env" env :ap i "name" name :ap i "variables" variables :do 
        (aset a "process time" name 0)
        (update-push-aclosure c :av "stage" 'init-vars :av "vars" variables))
    (match :av c "stage" 'init-vars :ap c "vars" vars :do 
        (if vars
            (progn (update-push-aclosure c vars (cdr vars))
                (clear-update-eval-aclosure c :av "instance" (car vars)))))
)

(mot "program declaration" 
    :at "name" "program name" 
    :atv "clock" "clock" 100
    :at "declarations" (listt "program item declaration")
    :at "processes" (listt "process declaration")
)

(aclosure c :attribute "axsem init" :type "program declaration" :stage nil 
    :instance i 
    :ap i "declarations" decls 
    :do (update-push-aclosure c :av "stage" 'decls :av "decls" decls)
)
(aclosure c :attribute "axsem init" :type "program declaration" :stage nil 
    :ap "decls" decls 
    :instance i 
    :ap i "processes" procs
    :do (if decls 
            (progn (update-push-aclosure c :av "decls" (cdr decls))
                (clear-update-eval-aclosure c :av "instance" (car decls)))
            (update-push-aclosure c :av "stage" 'procs :av "procs" procs))
)
(aclosure c :attribute "axsem init" :type "program declaration" :stage nil 
    :ap "procs" procs 
    :do (if decls 
            (progn (update-push-aclosure c :av "decls" (cdr procs))
                (clear-update-eval-aclosure c :av "instance" (car procs))))
)