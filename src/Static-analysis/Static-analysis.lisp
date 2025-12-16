(uiop:define-package Reflex-semantics
  (:use #:cl))
(in-package #:Reflex-semantics)

(defun prepare-static-analysis (program)
	(progn 
		(eval-aclosure (co 
		:av "env" (mo "analysis env")
		:av "agent" (mo "analysis agent")
		:av "attribute" "attribute prepare" 
		:av "instance" program))
		))

(defun check-compatability (closure instance)
    (let ((rules (aget closure (aseq "env" "crules"))))
        (dolist (func rules)
            (let ((result (funcall func closure instance)))
            (when (null result)
                (return result))))))

(defun set-mode-prepare (closure)
    (aset closure (aseq "env" "analysis params" "mode") 'prepare))

(defun set-mode-work (closure)
    (aset closure (aseq "env" "analysis params" "mode") 'work))

(defun get-mode (closure)
    (aget closure (aseq "env" "analysis params" "mode")))