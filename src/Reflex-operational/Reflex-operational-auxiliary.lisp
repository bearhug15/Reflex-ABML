(uiop:define-package Reflex-semantics
  (:use #:cl))
(in-package #:Reflex-semantics)

(defun cons-to-inner-list (a aseq val)
    (aset a (aseql aseq) (cons val (aget a (aseql aseq)))))

(defun mashup-name (&rest objects) 
    (if (listp (car objects))
        (format nil "~{~a~^#~}" (car objects))
        (format nil "~{~a~^#~}" objects)))

(defun act (value agent)
    (cond 
        ((is-instance value "lvalue") (aget agent (aseq "variable value" (aget value "name"))))
        (t value)))

(defun find-min-enum-field (env name)
    (let* ((field-map (aget env (aseq "enum value" name)))
            (names (attributes field-map)))
        (reduce (lambda (col el) (if (< (aget field-map el) (second col)) (el . (aget field-map el)))) 
            (cdr names) 
            :initial-value ((car names) . (aget field-map (car names))))))

(defun type-default-val (env ty)
    (cond 
        ((is-instance ty "simple type")
            (cond  
            ((is-instance ty "natural type") 0)
            ((is-instance ty "integer type") 0)
            ((is-instance ty "float type") 0.0)
            ((is-instance ty "boolean type") 'false)
            ((is-instance ty "time type") (iobj "rtime"))
            (ty 0)))
        ((is-instance ty "array type")
            (make-list len :initial-element (type-default-val env (aget ty "element type"))))
        ((is-instance ty "structure type")
            (let* ((struct-name (aget ty "name"))
                    (field-names (attributes (aget env (aseq "struct types" struct-name)))))
                (reduce (lambda (coll element) (aset coll element (type-default-val env (aget env (aseq "struct types" struct-name element)))))
                    field-names 
                    :initial-element (ob))))
        ((is-instance ty "enum type") (iobj "enum element access" :av "name" (aget ty "name") :av "field" (find-min-enum-field env (aget ty "name"))))
    )
)

(defun get-array-size-sup (env ty fields)
    (cond 
        ((is-instance ty "simple type") nil)
        ((is-instance ty "array type")
            (if (null fields)
                (aget ty "size")
                (get-array-size-sup env  (aget ty "element type") (cdr fields))))
        ((is-instance ty "structure type")
            (let* ((struct-name (aget ty "name"))
                    (field-type (aget env (aseq "struct fields" struct-name (car fields)))))
                (get-array-size-sup env field-type (cdr fields))))
        ((is-instance ty "enum type") nil)
    ))

(defun get-array-size (env name fields)
    (get-array-size-sup env (aget env (aseq "variable type" name)) fields))

(defun delete-agent-aclosures (env agent)
    (progn 
        (aset env "agents" (remove-if (lambda (val) (= (aget val "uid") (aget agent "uid"))) (aget env "agents")))
        (aset env (aseq "aclosures" agent) nil)))

(defun make-error (env agent message)
    (progn 
        (print message)
        (delete-agent-aclosures env agent)))

(defun def-bin-op (op left right)
    (let ((ty (otype op)))
        (cond 
            ((= "+" ty) (+ left right))
            ((= "-" ty) (- left right))
            ((= "*" ty) (* left right))
            ((= "<<" ty) (lsh left right))
            ((= ">>" ty) (lsh left (* -1 right)))
            ((= "==" ty) (= left right))
            ((= "!=" ty) (/= left right))
            ((= "<=" ty) (<= left right))
            ((= ">=" ty) (>= left right))
            ((= "<" ty) (< left right))
            ((= ">" ty) (> left right))
            ((= "|" ty) (logior left right))
            ((= "&" ty) (logand left right))
            ((= "^" ty) (logxor left right)))))


(defun def-comp-assign (op left right)
    (let ((ty (otype op)))
        (cond 
            ((= "+=" ty) (+ left right))
            ((= "-=" ty) (- left right))
            ((= "*=" ty) (* left right))
            ((= "<<=" ty) (lsh left right))
            ((= ">>=" ty) (lsh left (* -1 right)))
            ((= "|=" ty) (logior left right))
            ((= "&=" ty) (logand left right))
            ((= "^=" ty) (logxor left right)))))

(defun next-process-state (a c)
	(let* ((current-process (aget a "current process"))
            (current-state (aget a "current state"))
            (lst (member (aget c (aseq "process states names" current-process)) current-state)))
        (if (or (not lst) (= (length lst) 1))
            nil
            (car (cdr lst))))
)

(defun first-state (env process)
    (car (aget env (aseq "process states names" process))))