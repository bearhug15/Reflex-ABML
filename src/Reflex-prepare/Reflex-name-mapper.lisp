(uiop:define-package Reflex-semantics
  (:use #:cl))
(in-package #:Reflex-semantics)


(defun cons-to-inner-list (a aseq val)
    (aset a (aseql aseq) (cons val (aget a (aseql aseq)))))

(defun mashup-name (&rest objects) 
    (if (listp (car objects))
        (format nil "~{~a~^#~}" (car objects))
        (format nil "~{~a~^#~}" objects)))

(defun map-name (env name is-var)
    (if is-var
        (if (aget env "current process")
            (let ((cur-proc (aget env "current process")))
                (if (aget env (aseq "is process variable" cur-proc name))
                    (if (aget env (aseq "shared in process" cur-proc name))
                        (mashup-name "pv_" (aget env (aseq "shared in process" cur-proc)) "_" (aget env (aseq "shared" cur-proc name (aget env (aseq "shared in process" cur-proc)))))
                        (if (aget env (aseq "input variable port" cur-proc name))
                            (let* ((port-name (aget env (aseq "input variable port" cur-proc name)))
                                    (port-pos (aget env (aseq "port variable" cur-proc name port-name)))) 
                                (mashup-name port-name "_" port-pos))
                            (if (aget env (aseq "output variable port" cur-proc name))
                                (let* ((port-name (aget env (aseq "output variable port" cur-proc name)))
                                    (port-pos (aget env (aseq "port variable" cur-proc name port-name)))) 
                                    (mashup-name port-name "_" port-pos))
                                (mashup-name "pv_" (aget env "current process") "_" name)
                                )
                        )
                    )
                    (if (aget env (aseq "is global variable" name))
                        (if (aget env "input variable port" "_" name)
                            (let* ((port-name (aget env (aseq "input variable port" "_" name)))
                                    (port-pos (aget env (aseq "port variable" "_" name port-name)))) 
                                (mashup-name port-name "_" port-pos))
                            (if (aget env "output variable port" "_" name)
                                (let* ((port-name (aget env (aseq "output variable port" "_" name)))
                                    (port-pos (aget env (aseq "port variable" "_" name port-name)))) 
                                    (mashup-name port-name "_" port-pos))
                                (mashup-name "gv_" name)
                            )
                        )
                        nil
                    )
                )
            )
            (if (aget env (aseq "is global variable" name))
                (if (aget env "input variable port" "_" name)
                    (let* ((port-name (aget env (aseq "input variable port" "_" name)))
                                    (port-pos (aget env (aseq "port variable" "_" name port-name)))) 
                                (mashup-name port-name "_" port-pos))
                    (if (aget env "output variable port" "_" name)
                        (let* ((port-name (aget env (aseq "output variable port" "_" name)))
                                    (port-pos (aget env (aseq "port variable" "_" name port-name)))) 
                                    (mashup-name port-name "_" port-pos))
                        (mashup-name "gv_" name)
                    )
                )
                nil
            )
        )
        (if (aget env "current process")
            (let ((cur-proc (aget env "current process")))
                (if (aget "is process constant" name)
                    (mashup-name "pc_" name)
                    (if (aget env (aseq "is global constant" name))
                        (mashup-name "gc_" name)
                        nil
                    )
                )
            )
            (if (aget env (aseq "is global constant" name))
                (mashup-name "gc_" name)
                nil
            )
        )  
    )
)



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
    :av "shared variable" (cot :amap "process name" (cot :amap "variable name" (cot :amap "process name" "variable name")))

    :av "input variable port" (cot :amap "process name" (cot :amap "variable name" "port name"))
    :av "output variable port" (cot :amap "process name"(cot :amap "variable name" "port name"))
    :av "port variable" (cot :amap "process name" (cot :amap "variable name"(cot :amap "port name" int) ))

    :av "input ports" (listt "port name")
    :av "output ports" (listt "port name")

    :av "current process" "process name"
)

(mot "agent")


(mot "access" (uniont "expression" "field name"))
(mot "element access" :at "name" "variable name" :at "accesses" (listt "access"))

(aclosure с :attribute "map name" :type "element access" :stage nil
    :instance i
    :env env
    :ap i "name" name 
    :ap i "accesses" accesses
    :do (aset i "name" (map-name env name 
            (or (aget env (aseq "is global constant" name))
                (aget env (aseq "is process constant" (aget env "current process") name)))
            ))
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

;Statements

(aclosure c :attribute "map name" :type "timeout statement" :stage nil
    :instance i
    :ap i "controlling expression" expr 
    :ap i "statements" sts
    :do (update-push-aclosure c :av "stage" 'sts :av "sts" sts)
        (update-eval-aclosure c "instance" expr)
)
(aclosure c :attribute "map name" :type "timeout statement" :stage 'sts
    :instance i
    :ap "sts" sts 
    :do (if sts 
            (progn (update-push-aclosure c :av "sts" (cdr sts)))
                (clear-update-eval-aclosure c :av "instance" (car sts)))
)


(aclosure c :attribute "map name" :type "statement block" :stage nil
    :instance i 
    :ap i "statements" sts
    :do (update-push-aclosure c :av "stage" 'sts :av "sts" sts)
)
(aclosure c :attribute "map name" :type "statement block" :stage 'sts
    :instance i 
    :ap "sts" sts
    :do (if sts 
            (progn (update-push-aclosure c :av "sts" (cdr sts)))
                (clear-update-eval-aclosure c :av "instance" (car sts)))
)

(aclosure c :attribute "map name" :type "wait"
    :instance i 
    :ap i "condition" expr 
    :do (clear-update-eval-aclosure c "instance" expr)
)

(aclosure c :attribute "map name" :type "wait"
    :instance i 
    :ap i "condition" expr
    :ap i "controlling expression" cexpr
    :ap i "statements" sts
    :do (clear-update-eval-aclosure c "instance" expr)
        (clear-update-eval-aclosure c "instance" cexpr)
        (clear-update-eval-aclosure c "instance" sts)
)
#|(aclosure c :attribute "map name" :type "transition"
    :instance i 
    :ap i "condition" cexpr 
    :do (clear-update-eval-aclosure c "instance" cexpr)
)|#

(aclosure c :attribute "map name" :type "statement list" :stage nil
    :instance i
    :do (update-push-aclosure c :av "stage" 'rest :av "rest" (cdr i))
        (clear-update-eval-aclosure c :av "instance" (car i))
)
(aclosure c :attribute "map name" :type "statement list" :stage 'rest
    :ap c "rest" rst 
    :do (if rst 
            (progn (update-push-aclosure c :av "rest" (cdr rst)))
                (clear-update-eval-aclosure c :av "instance" (car rst)))
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
    :do (update-push-aclosure c :av "stage" 'sts :av "sts" cs)
        (clear-update-eval-aclosure c "instance" cexpr)
        (clear-update-eval-aclosure c "instance" default)
)
(aclosure c :attribute "map name" :type "switch statement" :stage 'sts
    :ap c "sts" sts 
    :do (if sts 
            (progn (update-push-aclosure c :av "sts" (cdr sts))
                (clear-update-eval-aclosure c :av "instance" (car sts))))
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

(aclosure c :attribute "map name" :type "block statement"
    :instance i 
    :ap i "statements" sts 
    :do (clear-update-eval-aclosure c :av "instance" sts)
)

(aclosure c :attribute "map name" :type "expression statement"
    :instance i 
    :ap i "expression" expr 
    :do (update-eval-aclosure c "instance" expr)
)

(aclosure c :attribute "map name" :type "state declaration"
    :instance i 
    :env env
    :ap i "name" name 
    :ap i "statements" sts 
    :do (aset env "current state" name)
        (clear-update-eval-aclosure c :av "instance" sts)
)

(aclosure c :attribute "map name" :type "process declaration" :stage nil
    :instance i 
    :ap i "states" states 
    :ap i "name" name 
    :env env 
    :do (aset env "current process" name)
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

(aclosure c :attribute "map name decl" :type "constant declaration"
    :instance i 
    :env env 
    :ap i "name" name 
    :ap env "current process" cur-proc
    :do (if cur-proc 
            (aset env (aseq "is process constant" cur-proc name) t)
            (aset env (aseq "is global constant" name) t))
)

(aclosure c :attribute "map name decl" :type "simple variable declaration"
    :instance i
    :env env 
    :ap i "name" name 
    :ap i "shared" shared 
    :ap env "current process" cur-proc
    :do (if cur-proc
            (progn (aset env (aseq "is process variable" cur-proc name) t)
                (if shared 
                    (aset env (aseq "shared in process" cur-proc name) t)))
            (aset env (aseq "is global variable" cur-proc name) t))
)

(aclosure c :attribute "map name decl" :type "array variable declaration"
    :instance i 
    :env env
    :ap i "name" name 
    :ap i "shared" shared 
    :ap env "current process" cur-proc
    :do (if cur-proc
            (progn (aset env (aseq "is process variable" cur-proc name) t)
                (if shared 
                    (aset env (aseq "shared in process" cur-proc name) t)))
            (aset env (aseq "is global variable" cur-proc name) t))
)

(aclosure c :attribute "map name decl" :type "imported variable declaration"
    :instance i
    :env env 
    :ap i "name" name 
    :ap i "source proc" sproc 
    :ap i "source var" svar 
    :ap env "current process" cur-proc
    :do (aset env (aseq "shared variable" cur-proc name sproc) svar)
)

(aclosure c :attribute "map name decl" :type "physical variable declaration"
    :instance i 
    :env env 
    :ap i "name" name 
    :ap i "port" port 
    :ap i "index" index 
    (aset env (aseq "port variable" name port) index)
)

(aclosure c :attribute "map name decl" :type "enum variable declaration"
    :instance i
    :env env 
    :ap i "name" name 
    :ap i "shared" shared 
    :ap env "current process" cur-proc
    :do (if cur-proc
            (progn (aset env (aseq "is process variable" cur-proc name) t)
                (if shared 
                    (aset env (aseq "shared in process" cur-proc name) t)))
            (aset env (aseq "is global variable" cur-proc name) t))
)

(aclosure c :attribute "map name decl" :type "structure variable declaration"
    :instance i 
    :env env
    :ap i "name" name 
    :ap i "shared" shared 
    :ap env "current process" cur-proc
    :do (if cur-proc
            (progn (aset env (aseq "is process variable" cur-proc name) t)
                (if shared 
                    (aset env (aseq "shared in process" cur-proc name) t)))
            (aset env (aseq "is global variable" cur-proc name) t))
)

(aclosure c :attribute "map name decl" :type "port declaration"
    :instance i 
    :env env 
    :ap i "port type" ty 
    :ap i "name" name 
    :do (if (= ty 'input)
            (cons-to-inner-list env (list "input ports") name)
            (cons-to-inner-list env (list "ouput ports") name))
)

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
