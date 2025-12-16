(uiop:define-package Reflex-semantics
  (:use #:cl))
(in-package #:Reflex-semantics)


(defun next-process-state (a env)
	(let* ((current-process (aget a "current process"))
            (current-state (aget a "current state"))
            (lst (member (aget env (aseq "process states names" current-process)) current-state)))
        (if (or (not lst) (= (length lst) 1))
            nil
            (car (cdr lst))))
)

(defun first-state (env process)
    (car (aget env (aseq "processes states names" process))))


(defun defined-proc-change (coll)
    (attributes coll))
(defun defined-pot-proc-change (coll)
    (reduce (lambda (elem col) (adjoin (aget elem "process") col)) coll :initial-value '()))

(defun add-cons-attributes (old new)
    (let* 
        ((procChange (aget old "process change"))
            (potProcChange (aget old "pot process change"))
            (newProcChange (aget new "process change"))
            (newPotProcChange (aget new "pot process change"))
            (procs (set-difference (intersection (defined-proc-change procChange) (defined-pot-proc-change (aget new "pot process change")))(defined-proc-change (aget new "pot process change"))))
            (newChangesTo (aget new "changes to"))) 
        (if (aget new "reset")
            (aset old "reset" t))
        (if (aget new "state changed")
            (aset old "state changed" t))
        (if newChangesTo
            (if (member nil newChangesTo)
                (aset old "changes to" (union newChangesTo (aget old "changes to")))
                (aset old "changes to" newChangesTo)))
        (mapc 
            (lambda (proc)
                (let ((potStart (member-if (lambda (el) (and (= proc (aget el "process")) (= 'start (aget el "change")))) potProcChange))
                        (potStop (member-if (lambda (el) (and (= proc (aget el "process")) (= 'stop (aget el "change")))) potProcChange))
                        (potError (member-if (lambda (el) (and (= proc (aget el "process")) (= 'error (aget el "change")))) potProcChange)))
                    (if (and (= (aget procChange proc) 'start) (or potStop potError))
                        (aset procChange proc nil))
                    (if (and (= (aget procChange proc) 'stop) (or potStart potError))
                        (aset procChange proc nil))
                    (if (and (= (aget procChange proc) 'error) (or potStart potStop))
                        (aset procChange proc nil))))
            procs)
        (mapc
            (lambda (proc)
                (aset procChange proc (aget newProcChange proc)))
            (attributes newProcChange))
        (let* ((ppc1 (remove-if (lambda (change) (member (aget change "process") (defined-proc-change newProcChange))) potProcChange))
                (ppc2 (union ppc1 newPotProcChange)))
            (aset old "process change" procChange)
            (aset old "pot process change" potProcChange))
            old
    ))
(defun cons-attributes (attr-list)
    (if (null attr-list)
        (mo "attributes")
        (reduce 
            (lambda (old new) (add-par-attributes old new)) 
            (cdr attr-list) 
            :initial-value (iclone (car attr-list)))))

(defun add-par-attributes (old new)
    (let* ((procChange (aget old "process change"))
            (potProcChange (aget old "pot process change"))
            (newProcChange (aget new "process change"))
            (newPotProcChange (aget new "pot process change"))
            (newChangesTo (aget new "changes to")))
        (if (null (aget new "reset"))
            (aset new "reset" nil))
        (if (null (aget new "state changed"))
            (aset new "state changed" nil))
        (if newChangesTo
            (aset old "changes to" (adjoin newChangesTo (aget old "changes to")))
            (aset old "changes to" (adjoin nil (aget old "changes to"))))
        (mapc 
            (lambda (proc) 
                (if (or (null (member proc (defined-proc-change newProcChange))) 
                        (not (= (aget newProcChange proc) (aget procChange proc))))
                    (aset procChange proc nil)))
            (defined-proc-change procChange))
        (let ((ppc1 (union potProcChange newPotProcChange)))
            (aset old "process change" procChange)
            (aset old "pot process change" ppc1))
        old
    ))
(defun add-par-attributes-conc (old)
    (let* ((procChange (aget old "process change"))
            (potProcChange (aget old "pot process change"))
            (definedProcChange (defined-proc-change procChange))
            (ppc (reduce 
                    (lambda (elem coll)
                        (let ((proc-name (aget elem "process")))
                            (if (member proc-name definedProcChange)
                                (adjoin (mo :av "process" proc-name :av "change" (aget procChange proc-name) ) coll
                                    :test (lambda (left right) 
                                            (and (= (aget left "process") (aget right "process"))
                                                (= (aget left "change") (aget right "change")))))
                                (cons elem coll)))) 
                    potProcChange 
                    :initial-value '())))
        (aset old "pot process change" ppc)
        old))

(defun par-attributes (attr-list)
    (add-par-attributes-conc
        (reduce 
            (lambda (old new) (add-par-attributes old new)) 
            (cdr attr-list) 
            :initial-value (iclone (car attr-list)))))




(defun check-p1-p2 (check-list p1 p2)
    "Проверяет, что:
   - для каждого i-го элемента el списка check-list истинен предикат P1,
   - и для каждого элемента от el (включительно) до конца списка истинен предикат P2.
   Возвращает T, если условие выполняется для всех i, иначе NIL."
    (loop for sublist on check-list
        for el = (first sublist)
        do (when (or (not (funcall p1 el))          ; P1 должен быть истинен для el_i
                     (some (lambda (x) (not (funcall p2 x))) sublist)) ; P2 для всех от el_i до конца
             (return-from check-p1-p2 nil)))
t)

(defun exists-p1-with-p2-tail (check-list p1 p2)
  "Возвращает T, если существует элемент el в check-list такой что:
   - (funcall p1 el) → истинно
   - и для всех элементов от el до конца списка (включительно) истинно (funcall p2 x)
   Иначе возвращает NIL."
    (loop for sublist on check-list
        for el = (first sublist)
        when (and (funcall p1 el)
                  (every p2 sublist))        ; P2 должен быть истинен на всём хвосте
        do (return-from exists-p1-with-p2-tail t))
nil)