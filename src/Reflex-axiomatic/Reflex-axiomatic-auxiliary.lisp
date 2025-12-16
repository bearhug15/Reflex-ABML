(uiop:define-package Reflex-semantics
  (:use #:cl))
(in-package #:Reflex-semantics)


(defun clear-agent-expr (a) 
    (progn (aset a "precond" nil)
        (aset a "proc act" nil)
        (aset a "state" nil)))

(defun cons-to-inner-list (a aseq val)
    (aset a (aseql aseq) (cons val (aget a (aseql aseq)))))

;добавляет ограничения на состояния процессов к предусловию и обнуляет их
(defun finalize-proc-act (c a)
    (let ((res (mapcar 
                (lambda (proc-name)
                    (mo "process activity" :av "state" "blank" :av "process" proc-name :av "activity" (aget a (aseq "proc act" proc-name)))
                ) 
                (attributes (aget a "proc act")))))
        (if (check-compatability c res)
            (if (> (length res) 1)
                (cons-to-inner-list a (aseq "cur cond") res)
                (if (= (length res) 1)
                    (cons-to-inner-list a (aseq "cur cond") (car res))))
            nil)))

;добавляет обновление на состояния программы к предусловию и обнуляет его
(defun finalize-state (a)
    (if (not (is-instance (aget a "state") "program state name"))
        (cons-to-inner-list a (aseq "cur cond") (aget a "state")))
)
;добавляет локальное предусловие к предусловию и обнуляет его
(defun finalize-precond (c a)
    (let ((precond (aget a "precond"))) 
        (if (> (length precond) 1)
            (if (check-compatability c (mo "conjunction" :av "formulas" precond))
                (cons-to-inner-list a (aseq "cur cond") (mo "conjunction" :av "formulas" precond))
                nil)
            (if (= (len res) 1)
                (if (check-compatability c (mo "conjunction" :av "formulas" precond))
                    (cons-to-inner-list a (aseq "cur cond") precond)
                    nil)))))

(defun finalize-expression (c)
    (let ((a (aget c "agent")))
        (and 
            (finalize-proc-act c a)
            (finalize-precond c a)
            (finalize-state a))))

(defun create-lemma (a postcondition)
    (mo "vc lemma" :av "precondition" (mo "inv plug") :av "postcondition" postcondition :av "steps" (reverse 
        (progn (finalize-expression a)
                (aget a "cur cond")))))

(defun finalize-lemma (a env postcondition)
    (cons-to-inner-list env (aseq "conditions") (create-lemma a postcondition)))

(defun finalize-base-lemma (a con)
    (cons-to-inner-list env (aseq "conditions") (mo "vc lemma" :av "precondition" 'true :av "postcondition" (mo "inv plug") :av "steps" (reverse (aget a "cur cond")))))

(defun finalize-general-lemma (a con)
    (cons-to-inner-list env (aseq "conditions") (mo "vc lemma" :av "precondition" (mo "inv plug") :av "postcondition" (mo "inv plug") :av "steps" (reverse (aget a "cur cond")))))

(defun type-default-val (env ty)
    (cond 
        ((is-instance ty "simple type")
            (cond  
            ((is-instance ty "natural type") 0)
            ((is-instance ty "integer type") 0)
            ((is-instance ty "float type") 0.0)
            ((is-instance ty "boolean type") 'false)
            ((is-instance ty "time type") (mo "rtime"))
            (ty 0)))
        ((is-instance ty "array type")
            (make-list len :initial-element (type-default-val env (aget ty "element type"))))
        ((is-instance ty "structure type")
            (let* ((struct-name (aget ty "name"))
                    (field-names (aget env (attributes (aseq "struct fields" struct-name)))))
                (reduce (lambda (coll element) (aset coll element (type-default-val env (aget env (aseq "struct fields" struct-name element)))))
                    field-names 
                    :initial-element (ob))))
        ((is-instance ty "enum type") (mo "enum element access" :av "name" (aget ty "name") :av "field" (find-min-enum-field env (aget ty "name"))))
    )
)

(defun get-variable-type-sup (env type fields)
    (cond 
        ((is-instance type "simple type") (if (null fields) type (mo "undefined type")))
        ((is-instance type "array type")
            (if (stringp (car fields))
                (mo "undefined type")
                (get-variable-type-sup env (aget type "element type") (cdr fields))))
        ((is-instance type "structure type")
            (let* ((struct-name (aget type "name"))
                    (field-type (aget (aget env (aseq "struct fields" struct-name (car fields))) )))
                (get-variable-type-sup env field-type (cdr fields))))
        ((is-instance t "enum type") (if (null fields) 'int32 (mo "undefined type")))
    ))
(defun get-variable-type (env name fields)
    (get-variable-type-sup env (aget env (aseq "variable type" name)) fields))

(defun get-array-size-sup (env type fields)
    (cond 
        ((is-instance type "simple type") nil)
        ((is-instance type "array type")
            (if (null fields)
                (aget type "size")
                (get-array-size-sup env  (aget type "element type") (cdr fields))))
        ((is-instance type "structure type")
            (let* ((struct-name (aget type "name"))
                    (field-type (aget (aget env (aseq "struct fields" struct-name (car fields))))))
                (get-array-size-sup env field-type (cdr fields))))
        ((is-instance t "enum type") nil)
    ))

(defun get-array-size (env name fields)
    (get-array-size-sup env (aget env (aseq "variable type" name)) fields))


(defun assignment-to-expression (op)
    (cond 
        ((= op "+=") "+")
        ((= op "-=") "-")
        ((= op "*=") "*")
        ((= op "<<=") "<<")
        ((= op ">>=") ">>")
        ((= op "|=") "|")
        ((= op "&=") "&")
        ((= op "^=") "^")
        ((= op "/=" "/"))
        ((= op "%=" "%")))
)


(defun activity-to-int (activity)
    (cond 
        ((= activity 'active) 1)
        ((= activity 'inactive) 3)
        ((= activity 'stop) 5)
        ((= activity 'nonstop) 7)
        ((= activity 'error) 11)
        ((= activity 'nonerror) 13)
    )
)

(defun insert-proc-act (a process act)
    (let ((prev-act (aget a (aseq "proc act" process))))
        (if prev-act
            (case (* (activity-to-int prev-act) (activity-to-int act))
                ((3 5 11 35 55 143) nil)
                ((1 7 13 91) (progn (aset a "proc act" process 'active) t))
                (9 (progn (aset a "proc act" process 'inactive) t))
                ((15 39 25 65) (progn (aset a "proc act" process 'stop) t))
                (49 (progn (aset a "proc act" process 'nonstop) t))
                ((21 33 121 77) (progn (aset a "proc act" process 'error) t))
                (169 (progn (aset a "proc act" process 'nonerror) t)))
            (progn (aset a (aseq "proc act" process) act)
                t))))

(defun invert-activity (act)
    (cond  
        ((= act 'active) 'inactive)
        ((= act 'inactive) 'active)
        ((= act 'stop) 'nonstop)
        ((= act 'error) 'nonerror)
        ((= act 'nonstop) 'stop)
        ((= act 'nonerror) 'error))
)

;Так ли мы удаляем агента из стека
(defun delete-agent-aclosures (env agent)
    (progn 
        (aset env "agents" (remove-if (lambda (val) (= (aget val "uid") (aget agent "uid"))) (aget env "agents")))
        (aset env (aseq "aclosures" agent) nil)))

(defun next-process-state (a c)
	(let* ((current-process (aget a "current process"))
            (current-state (aget a "current state"))
            (lst (member (aget c (aseq "process states names" current-process)) current-state)))
        (if (or (not lst) (= (length lst) 1))
            nil
            (car (cdr lst))))
)

(defun first-state (env process)
    (car (aget env (aseq "processes states names" process))))
(defun current-first-state (a env)
    (car (aget env "processes states names" (aget a "current process"))))

(defun mashup-symbol (&rest objects) 
    (intern (format nil "~{~a~}" objects)))
