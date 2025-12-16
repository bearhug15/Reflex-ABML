(uiop:define-package Reflex-semantics
  (:use #:cl))
(in-package #:Reflex-semantics)

(in-readtable :cl-smt-lib)
(defparameter smt (make-smt "z3" "-in" "-smt2"))

(defun SMT-analysis (сlosure term)
    (cond 
		((= (get-mode closure) 'prepare) (SMT-analysis-prepare closure))
        ((= (get-mode closure) 'work) (SMT-analysis-work closure term))))
