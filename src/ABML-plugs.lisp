(uiop:define-package Reflex-semantics
  (:use #:cl))
(in-package #:Reflex-semantics)

(deftype lispt () t)
;(deftype symbol () t)
;(deftype atom () t)
;(deftype string () t)
;(deftype int () t)
(deftype nat () t)
;(deftype real () t)
(deftype listt () t)
(deftype uniont () t)
(deftype enumt () t)
(deftype funt () t)
(deftype any () t)
(deftype bool () t)

(defun mot (&rest var) ()) 
(defun cot (&rest var) ())
(defun typedef (var1 var2) ())
(defun mo (&rest var) ())
(defun co (&rest var) ())

(defun uid (&rest var) ())
(defun imax (&rest var) ())
(defun otype (&rest var) ())
(defun is-instance (instance type) ())
(defun attributes (&rest var) ())
(defun att (&rest var) ())
(defun iclone (var) ())
(defun iclone-agent (env a) ())

(defun aget (&rest var) ())
(defun aset (&rest var) ())
(defun acall (&rest var) ())
(defun aseq (&rest var) ())
(defun aseql (&rest var) ())

(defun match (&rest var) ())
(defun nmatch (&rest var) ())
(defun aclosure (&rest var) ())
(defun eval-aclosure (&rest var) ())
(defun clear-aclosure (ac) ())

(defun push-aclosure (ac)
  (match :ap ac "agent" a :ap ac "env" :ap e "agents" al
    :ap e (aseq "aclosures" a) cl
    :do
      (aset e "aclosures" a (cons ac cl))
      (match :v (not (member a al)) T :do
        (aset e "agents" (cons a al)))))

(defun pop-aclosure (ac)
  (match :ap ac "env" e :ap e "agents" al :do
    (match :v (null al) T :do nil)
    (match :p (car al) a :ap e (aseq "aclosures" a) cl :do
      (match :v (null cl) T :do nil
        :exit (aset e "aclosures" a (cdr cl)) (car cl)))))

(defun next-aclosure (ac)
  (match :ap ac "env" e :ap e "agents" al :do
    (match :v (null al) T :do)
    (match :p (car al) a :ap e (aseq "aclosures" a) cl 
      :do(match :v (null cl) T
      :do (aset e "agents" (cdr al)) (next-aclosure ac))
      :exit (aset e "aclosures" a (cdr cl))
        (eval-aclosure (car cl)))))

(defun update-push-aclosure (&rest var) ())
(defun clear-update-push-aclosure (&rest var) ())
(defun update-eval-aclosure (&rest var) ())
(defun clear-update-eval-aclosure (&rest var) ())