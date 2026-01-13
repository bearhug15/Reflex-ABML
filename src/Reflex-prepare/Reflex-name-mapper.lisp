(uiop:define-package Reflex-semantics
  (:use #:cl))
(in-package #:Reflex-semantics)


(defun cons-to-inner-list (a l val)
    (aset a (aseql l) (cons val (aget a (aseql l)))))

(defun mashup-name (&rest objects) 
    (if (listp (car objects))
        (format nil "~{~a~^#~}" (car objects))
        (format nil "~{~a~^#~}" objects)))

(defun new-name (path name)
    (format nil "~a::~a"(format nil "~{~a~^.~}" (reverse path)) name))

(defun new-phys-name (name pos)
    (format nil "~a_~a" name pos))

(defun form-direct (name num)
    (format nil "~a.~a" name num))

(defun block-name (num) (format nil "~a~a" "b" num))

(mot "env" 
;There used raw variable names
;variable exists whether in is-process-variable or is-global-variable
;if variable is in shared-in-process then it should be in is-process-variable
;is-input/is-output is exclusive categories
    :at "agents" (listt "agent")
    :at "aclosures" (cot :amap "agent" (listt (cot)))

    :av "is global variable" (cot :amap "variable name" bool)
    :av "is process variable" (cot :amap "process name" (cot :amap "variable name" bool))
    :av "is global constant" (cot :amap "variable name" bool)
    :av "is process constant" (cot :amap "process name" (cot :amap "variable name" bool))
    :av "shared in process" (cot :amap "process name" (cot :amap "variable name" bool))
    ;На практике в списке в лежит имя процесса и имя переменной
    :av "shared variable" (cot :amap "process name" (cot :amap "variable name" (listt "name")))

    :av "input variable port" (cot :amap "process name" (cot :amap "variable name" "port name"))
    :av "output variable port" (cot :amap "process name"(cot :amap "variable name" "port name"))
    :av "port variable" (cot :amap "process name" (cot :amap "variable name" (cot :amap "port name" int) ))

    :av "input ports" (listt "port name")
    :av "output ports" (listt "port name")

)

(mot "agent" 
    :av "path" (listt string)
    :av "block count" int 
    :av "variable map" (cot :amap "variable name" "variable name")
    :av "is direct" (cot :amap "variable name" bool)
    :av "direct count" (cot :amap "variable name" int)
    :av "node variables" (cot :amap "node name" (cot :amap "variable name" "variable name"))
    :av "nodes processes" (cot :amap "node name" "process name")
)

(defun is-in-node (agent node process)
    (member process (aget a (aseq "nodes processes" node)) :test #'string=))

(defun mobject-union (obj1 obj2)
    (let ((uobj (mot (otype obj1))))
        (mapc (lambda (att-name) (aset uobj att-name (aget obj1 att-name))) (attributes obj1))
        (mapc (lambda (att-name) (aset uobj att-name (aget obj2 att-name))) (attributes obj2))
        uobj))

(aclosure с :attribute "map name" :type "element access" :stage nil
    :instance i
    :agent a
    :env env
    :ap i "name" name 
    :ap i "accesses" accesses
    :ap a "variable map" mp
    :p (aget mp name) new-name
    :ap a (aseq "direct count" new-name) num
    :do (if (aget a (aseq "is direct" new-name))
            (progn (aset i "name" (form-direct new-name num))
                (aset a (aseq "direct count" new-name) (+ num 1)))
            (aset i "name" new-name))
        (update-push-aclosure c :av "stage" 'accesses :av "accesses" accesses)
)
(aclosure с :attribute "map name" :type "element access" :stage 'acceesses
    :ap "accesses" accesses 
    :do (if accesses 
            (progn (update-push-aclosure с :av "accesses" (cdr accesses))
                (clear-update-eval-aclosure c :av "instance" (car accesses)))))


(mot "enum element access" :at "name" "enum name" :at "field" "field name")

(mot "binary expression" :union ("+" "-" "*" "/" ">>" "<<" "==" "!=" ">=" "<=" ">" "<" "&&" "||" "&" "|" "^" "=" "+=" "-=" "*=" "/=" "<<=" ">>=" "&=" "|=" "^="))

(aclosure c :attribute "map name" :type "binary operation"
    :instance i
    :ap i "left" left 
    :ap i "right" right
    :do (clear-update-eval-aclosure c "instance" left)
        (clear-update-eval-aclosure c "instance" right)
)
(aclosure c :attribute "map name" :type "cast"
    :instance i
    :ap i "expression" expr
    :do (clear-update-eval-aclosure c "instance" expr)
)
(aclosure c :attribute "map name" :type "!."
    :instance i
    :ap i "expression" expr 
    :do (clear-update-eval-aclosure c "instance" expr)
)
(aclosure c :attribute "map name" :type "-."
    :instance i
    :ap i "expression" expr 
    :do (clear-update-eval-aclosure c "instance" expr)
)
(aclosure c :attribute "map name" :type "~."
    :instance i 
    :ap i "expression" expr 
    :do (clear-update-eval-aclosure c "instance" expr)
)

(aclosure c :attribute "map name" :type "++."
    :instance i 
    :ap i "access" access 
    :do (clear-update-eval-aclosure c "instance" access)
)
(aclosure c :attribute "map name" :type ".++"
    :instance i 
    :ap i "access" access 
    :do (clear-update-eval-aclosure c "instance" access)
)
(aclosure c :attribute "map name" :type "--."
    :instance i 
    :ap i "access" access 
    :do (clear-update-eval-aclosure c "instance" access)
)
(aclosure c :attribute "map name" :type ".--"
    :instance i 
    :ap i "access" access 
    :do (clear-update-eval-aclosure c "instance" access)
)

(aclsoure c :attribute "map name" :type "expression list" :stage nil
    :instance i 
    :do (update-push-aclosure c :av "stage" 'sts :av "sts" i)
)
(aclsoure c :attribute "map name" :type "expression list" :stage 'sts
    :instance i
    :ap "sts" sts
    :do (if sts 
            (progn (update-push-aclosure c :av "sts" (cdr sts))
                (clear-update-eval-aclosure c :av "instance" (car sts))))
)

;Statements

(aclosure c :attribute "map name" :type "timeout statement" :stage nil
    :instance i
    :ap i "controlling expression" expr 
    :ap i "statements" sts
    :agent a
    :ap a "variable map" mp
    :do (update-push-aclosure c :av "stage" 'sts :av "sts" sts :av "variable map" mp)
        (update-eval-aclosure c "instance" expr)
)
(aclosure c :attribute "map name" :type "timeout statement" :stage 'sts
    :ap "sts" sts 
    :do (if sts 
            (progn (update-push-aclosure c :av "sts" (cdr sts))
                (clear-update-eval-aclosure c :av "instance" (car sts)))
            (update-push-aclosure c :av "stage" 'end))
)
(aclosure c :attribute "map name" :type "timeout statement" :stage 'end
    :ap "variable map" mp
    :agent a
    :do (aset a "variable map" mp)
)

(aclsoure c :attribute "map name" :type "statement list" :stage nil
    :instance i 
    :do (update-push-aclosure c :av "stage" 'sts :av "sts" i)
)
(aclsoure c :attribute "map name" :type "statement list" :stage 'sts
    :instance i
    :ap "sts" sts
    :do (if sts 
            (progn (update-push-aclosure c :av "sts" (cdr sts))
                (clear-update-eval-aclosure c :av "instance" (car sts))))
)


(aclosure c :attribute "map name" :type "statement block" :stage nil
    :instance i 
    :ap i "statements" sts
    :agent a
    :ap a "variable map" mp
    :ap a "block count" bc
    :ap a "path" path
    :do (aset a "path" (cons (block-name bc) path))
        (aset a "block count" (+ bc 1))
        (update-push-aclosure c :av "stage" 'end :av "variable map" mp)
        (clear-update-eval-aclosure c :av "instance" sts)
)
(aclosure c :attribute "map name" :type "statement block" :stage 'end
    :ap "variable map" mp
    :agent a
    :ap a "path" path
    :do (aset a "path" (cdr path))
        (aset a "variable map" mp)
)

(aclosure c :attribute "map name" :type "wait"
    :instance i 
    :ap i "condition" expr 
    :do (clear-update-eval-aclosure c "instance" expr)
)

(aclosure c :attribute "map name" :type "wait on timeout" :stage nil
    :instance i 
    :ap i "condition" expr
    :ap i "controlling expression" cexpr
    :ap i "statements" sts
    :do (clear-update-eval-aclosure c "instance" expr)
        (clear-update-eval-aclosure c "instance" cexpr)
        (clear-update-eval-aclosure c "instance" sts)
)

(aclosure c :attribute "map name" :type "if then statement"
    :instance i 
    :ap i "condition" expr 
    :ap c "then" then 
    :do (update-eval-aclosure c "instance" expr)
        (update-eval-aclosure c "instance" then)
)

(aclosure c :attribute "map name" :type "if then else statement"
    :instance i 
    :ap i "condition" cexpr 
    :ap c "then" then 
    :ap c "else" else 
    :do (update-eval-aclosure c "instance" cexpr)
        (update-eval-aclosure c "instance" then)
        (update-eval-aclosure c "instance" else)
)

(aclosure c :attribute "map name" :type "switch statement" :stage nil
    :instance i
    :ap i "controlling expression" cexpr 
    :ap i "cases" cs 
    :ap i "default" default 
    :agent a
    :ap a "variable map" mp
    :ap a "block count" bc
    :ap a "path" path
    :do (aset a "path" (cons (block-name bc) path))
        (aset a "block count" (+ bc 1))
        (update-push-aclosure c :av "stage" 'end :av "variable map" mp)
        (update-push-aclosure c :av "stage" 'sts :av "sts" cs)
        (clear-update-eval-aclosure c "instance" cexpr)
        (clear-update-eval-aclosure c "instance" default)
)
(aclosure c :attribute "map name" :type "switch statement" :stage 'sts
    :ap c "sts" sts 
    :do (if sts 
            (progn (update-push-aclosure c :av "sts" (cdr sts))
                (clear-update-eval-aclosure c :av "instance" (car sts))))
)
(aclosure c :attribute "map name" :type "switch statement" :stage 'end
    :ap "variable map" mp
    :agent a
    :ap a "path" path
    :do (aset a "path" (cdr path))
        (aset a "variable map" mp)
)

(aclosure c :attribute "map name" :type "default statement"
    :instance i 
    :ap i "statements" sts 
    :do (clear-update-eval-aclosure c :av "instance" sts)
)

(aclosure c :attribute "map name" :type "case statement"
    :instance i 
    :ap i "statements" sts 
    :do (clear-update-eval-aclosure c :av "instance" sts)
)

(aclosure c :attribute "map name" :type "expression statement"
    :instance i 
    :ap i "expression" expr 
    :do (update-eval-aclosure c "instance" expr)
)

(mot "for statement" :at "init" "expression" :at "condition" "expression" :at "update" "expression" :at "statement" "statement")

;Можно ли несолько eval подряд?
(aclosure c :attribute "map name" :type "for statement" :stage nil 
    :instance i 
    :ap i "init" init
    :ap i "condition" cnd
    :ap i "update" upd
    :at i "statement" st
    :agent a 
    :ap a "variable map" mp 
    :do (update-push-aclosure c :av "stage" 'end :av "variable map" mp)
        (clear-update-eval-aclosure c :av "instance" init)
        (clear-update-eval-aclosure c :av "instance" cnd)
        (clear-update-eval-aclosure c :av "instance" upd)
        (clear-update-eval-aclosure c :av "instance" st))
(aclosure c :attribute "map name" :type "for statement" :stage nil 
    :ap "variable map" mp 
    :do (aset a "variable map" mp))

(mot "for decl statement" :at "init" "statement variable declaration" :at "condition" "expression" :at "update" "expression" :at "statement" "statement")
(aclosure c :attribute "map name" :type "for decl statement" :stage nil 
    :instance i 
    :ap i "init" init
    :ap i "condition" cnd
    :ap i "update" upd
    :at i "statement" st
    :agent a 
    :ap a "variable map" mp 
    :do (update-push-aclosure c :av "stage" 'end :av "variable map" mp)
        (clear-update-eval-aclosure c :av "instance" init)
        (clear-update-eval-aclosure c :av "instance" cnd)
        (clear-update-eval-aclosure c :av "instance" upd)
        (clear-update-eval-aclosure c :av "instance" st))
(aclosure c :attribute "map name" :type "for decl statement" :stage nil 
    :ap "variable map" mp 
    :do (aset a "variable map" mp))


(aclosure c :attribute "map name" :type "state declaration" :stage nil
    :instance i 
    :env env
    :ap i "name" name 
    :ap i "statements" sts 
    :agent a
    :ap a "variable map" mp
    :do (aset a "path" (cons name (aget a "path")))
        (update-push-aclosure c :av "stage" 'end :av "variable map" mp)
        (aset env "current state" name)
        (clear-update-eval-aclosure c :av "instance" sts)
)
(aclosure c :attribute "map name" :type "state declaration" :stage 'end 
    :ap "variable map" mp
    :agent a
    :do (aset a "path" (cdr (aget a "path")))
        (aset a "variable map" mp))

(aclosure c :attribute "map name" :type "process declaration" :stage nil
    :instance i 
    :ap i "states" states 
    :ap i "name" name 
    :ap i "node" node
    :env env 
    :agent a
    :ap a "variable map" mp
    :ap a (aseq "node variables" node) nmp
    :do (aset a (aseq "variable map") (mobject-union mp nmp))
        (aset a "path" (cons name (cons node (aget a "path"))))
        (update-push-aclosure c :av "stage" 'end :av "variable map" mp)
        (aset env "current process" name)
        (update-push-aclosure c :av "stage" 'states :av "rest" (cdr states))
        (clear-update-eval-aclosure c :av "instance" (car states))
)
(aclosure c :attribute "map name" :type "process declaration" :stage 'states
    :ap "rest" rst 
    :env env 
    :do (if rst 
            (progn (update-push-aclosure c :av "rest" (cdr rst))
                (clear-update-eval-aclosure c :av "instance" (car rst)))
            (aset env "current process" nil))
)
(aclosure c :attribute "map name" :type "process declaration" :stage 'end 
    :ap "variable map" mp
    :agent a
    :do (aset a "path" (cdr (aget a "path")))
        (aset a "variable map" mp))

(aclosure c :attribute "map name" :type "constant declaration"
    :instance i 
    :ap i "name" name 
    :agent a
    :ap a "path" path 
    :ap (new-name path name) nname
    :do (aset i "name" nname)
        (aset a (aseq "variable map" name) nname)
)

(aclosure c :attribute "map name" :type "simple variable declaration" :stage nil 
    :instance i
    :env env 
    :ap i "name" name 
    :ap i "init" init
    :do (update-push-aclosure c :av "stage" 'end)
        (clear-update-eval-aclosure c :av "instance" init)
)
(aclosure c :attribute "map name" :type "simple variable declaration" :stage 'end 
    :instance i
    :ap i "name" name 
    :agent a
    :ap a "path" path 
    :ap (new-name path name) nname
    :do (aset i "name" nname)
        (aset a (aseq "variable map" name) nname)
)

(aclosure c :attribute "map name" :type "array variable declaration" :stage nil 
    :instance i
    :env env 
    :ap i "name" name 
    :ap i "init" init
    :do (update-push-aclosure c :av "stage" 'end)
        (clear-update-eval-aclosure c :av "instance" init)
)
(aclosure c :attribute "map name" :type "array variable declaration" :stage 'end 
    :instance i
    :ap i "name" name 
    :agent a
    :ap a "path" path 
    :ap (new-name path name) nname
    :do (aset i "name" nname)
        (aset a (aseq "variable map" name) nname)
)

(aclosure c :attribute "map name" :type "physical variable declaration"
    :instance i 
    :env env 
    :ap i "name" name 
    :ap i "port" port 
    :ap i "index" index
    :ap i "direct" direct
    :ap (new-phys-name port index) nname
    :do (aset i "name" nname)
        (aset a (aseq "variable map" name) nname)
        (aset a (aseq "is direct" nname) direct)
        (if direct 
            (aset a (aseq "direct count" nname) 0))
)

(aclosure c :attribute "map name" :type "enum variable declaration"
    :instance i
    :env env 
    :ap i "name" name 
    :agent a
    :ap a "path" path 
    :ap (new-name path name) nname
    :do (aset i "name" nname)
        (aset a (aseq "variable map" name) nname)
)

(aclosure c :attribute "map name" :type "structure variable declaration"
    :instance i 
    :env env
    :ap i "name" name 
    :agent a
    :ap a "path" path 
    :ap (new-name path name) nname
    :do (aset i "name" nname)
        (aset a (aseq "variable map" name) nname)
)

(aclosure c :attribute "map name" :type "node declaration" :stage nil 
    :instance i 
    :ap i "variables" rst 
    :agent a 
    :ap a "variable map" mp 
    :do (update-push-aclosure c :av "stage" 'end :av "variable map" mp)
        (update-push-aclosure c :av "stage" 'vars :av "rest" rst))
(aclosure c :attribute "map name" :type "node declaration" :stage 'vars 
    :ap "rest" rst 
    :do (if rst 
            (progn (update-push-aclosure c :av "rest" (cdr rst))
                (clear-update-eval-aclosure c :av "instance" (car rst)))))
(aclosure c :attribute "map name" :type "node declaration" :stage 'end  
    :instance i :ap i "name" name
    :ap "variable map" omp
    :agent a 
    :ap a "variable map" mp
    :ap a "node variables" nvars
    :do (aset nvars name mp)
        (aset a "variable map" omp)
)

(aclosure c :attribute "map name" :type "program declaration" :stage nil 
    :instance i 
    :ap i "variables" vars
    :do (update-push-aclosure c :av "stage" 'prepared :av "rest" vars)
        ;(clear-update-eval-aclosure c :av "attribute" "map name decl" :av "instance" i)
)
(aclosure c :attribute "map name" :type "program declaration" :stage 'vars
    :ap "rest" rst
    :instance i
    :ap i "nodes" nodes
    :do (if rst 
            (progn (update-push-aclosure c :av "rest" (cdr rst))
                (clear-update-eval-aclosure c :av "instance" (car rst)))
            (update-push-aclosure c :av "stage" 'nodes :av "rest" nodes))
)
(aclosure c :attribute "map name" :type "program declaration" :stage 'nodes
    :ap "rest" rst
    :instance i
    :ap i "processes" procs
    :do (if rst 
            (progn (update-push-aclosure c :av "rest" (cdr rst))
                (clear-update-eval-aclosure c :av "instance" (car rst)))
            (update-push-aclosure c :av "stage" 'procs :av "rest" procs))
)
(aclosure c :attribute "map name" :type "program declaration" :stage 'nodes
    :ap "rest" rst
    :env env 
    :agent a
    :do (if rst 
            (progn (clear-update-eval-aclosure c :av "agent" (iclone-agent env a) :av "instance" (car rst))
                (update-push-aclosure c :av "rest" (cdr rst))))
)


#|
(aclosure c :attribute "map name decl" :type "process declaration" :stage nil
    :instance i 
    :env env
    :ap i "variables" vars 
    :ap i "name" name
    :do (aset env "current process" name)
        (update-push-aclosure c :av "stage" 'states :av "rest" (cdr vars))
        (clear-update-eval-aclosure c :av "instance" (car states))
)
(aclosure c :attribute "map name decl" :type "process declaration" :stage 'states
    :env env
    :ap "rest" rst
    :do (if rst 
            (progn (update-push-aclosure c :av "rest" (cdr rst))
                (clear-update-eval-aclosure c :av "instance" (car rst)))
            (aset env "current process" nil))
)

(aclosure c :attribute "map name decl" :type "program declaration" :stage nil
    :instance i 
    :ap "declarations" decls
    :do (update-push-aclosure c :av "stage" 'prepare-gvars :av "rest" decls)
)    
(aclosure c :attribute "map name decl" :type "program declaration" :stage 'prepare-gvars
    :instance i 
    :ap "rest" rst 
    :ap i "processes" procs 
    :do (if rst 
            (progn (update-push-aclosure c "rest" (cdr rst))
                (clear-update-eval-aclosure c "instance" (car rst)))
            (update-push-aclosure c :av "stage" 'prepare-procs :av "rest" procs))
)
(aclosure c :attribute "map name decl" :type "program declaration" :stage 'prepare-procs
    :ap "rest" rst
    :do (if rst 
            (progn (update-push-aclosure c "rest" (cdr rst))
                (clear-update-eval-aclosure c "instance" (car rst))))
)

(aclosure c :attribute "map name" :type "program declaration" :stage nil 
    :instance i 
    :ap i "processes" procs 
    :do (update-push-aclosure c :av "stage" 'prepared :av "rest" procs)
        (clear-update-eval-aclosure c :av "attribute" "map name decl" :av "instance" i)
)
(aclosure c :attribute "map name" :type "program declaration" :stage 'prepared
    :ap "rest" rst
    :do (if rst 
            (progn (update-push-aclosure c :av "rest" (cdr rst))
                (clear-update-eval-aclosure c "instance" (car rst))))
)
|#