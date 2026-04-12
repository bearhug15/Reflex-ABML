(uiop:define-package Reflex-semantics
  (:use #:cl))
(in-package #:Reflex-semantics)

(mot "blank program state")
(typedef "outer var" (enumt "name"))
(typedef "term" (uniont "actualizable term" "nonactualizable term"))
(typedef "actualizable term" (uniont "binary operation" "unary operation" "value getter"  "cast operation"))
(typedef "nonactualizable term" (uniont "constant" "pstate compare" "outer var" "value list" "value map"))
(typedef "value list" (listt "term"))
(typedef "value map" (cot :amap "field name" "term"))

(mot "access" (uniont "term" "field name"))
(mot "variable access" :at "name" "variable name" :at "path" (listt "access"))

(mot "value getter"
    :at "type" "simple type"
    :at "state" "program state"
    :at "access" "variable access"
    :at "actualized" bool)
(mot "value setter"
    :at "type" "simple type"
    :at "state" "program state"
    :at "access" "variable access"
    :at "value" "term")


(mot "binary operation" 
    :at "type" "simple type"
    :at "op" "bop" 
    :at "left" "term"
    :at "right" "term" 
    :at "actualized" bool)
(mot "unary operation" 
    :at "type" "simple type"
    :at "op" "uop"
    :at "right" "term" 
    :at "actualized" bool)
(mot "cast operation" 
    :at "type" "simple type"
    :at "pretype" "simple type" 
    :at "right" "term" 
    :at "actualized" bool)

(mot "logic binop" :enum ("&&" "||" "==" "!=" "<" "<=" ">" ">="))
(mot "num binop" :enum ("+" "-" "*" "/" "%" "&" "|" "^" "<<" ">>"))
(mot "bop" (uniont "logic bop" "num bop"))
(mot "uop" (uniont "-." "!." "~."))

(mot "pstate compare"
    :at "state" "program state" 
    :at "process" "process name"
    :at "pstate" "state name")

(mot "implication" 
    :at "left" "term" 
    :at "right" "term")
(mot "conjunction" :at "formulas" (listt "formula"))
(mot "disjunction" :at "formulas" (listt "formula"))
(mot "process activity" :at "state" "program state" :at "process" "process name" :at "activity" (uniont 'active 'stop 'error 'inactive 'nonstop 'nonerror))
(mot "process activity block" (uniont (listt "process activity")))
(mot "arg name" (enumt string))
(mot "forall" 
    :at "args" (listt "arg name")
    :at "formula" "formula")
(mot "exists" 
    :at "args" (listt "arg name")
    :at "formula" "formula")
(mot "ltime check"
    :at "state" "program state"
    :at "process" "process name"
    :at "compare val" "term" 
    :at "exceed" bool)
(mot "inv plug" :at "num" int)
(mot "state notupdating formula" (uniont "forall" "exists" "ltime check" "term" "implication" "inv plug" "conjunction" "disjunction" "process activity" "process activity block"))

(mot "program state" (uniont "blank program state" "value setter"))
(mot "reset" :at "state" "program state")
(mot "to env" :at "state" "program state")
(mot "pstate setter" :at "state" "program state" :at "process" "process name" :at "pstate" "state name")
(mot "state updating formula" (uniont "program state" "pstate setter" "reset" "to env"))

(mot "formula" (uniont "state notupdating formula" "state updating formula"))
(mot "vc lemma" 
    :at "precondition" "formula" 
    :at "postcondition" "formula" 
    :at "steps" (listt "formula"))




;В работе
(mot "constructor field" :at "name" "name" :at "type" "name")
(mot "datatype constructor" :at "name" "name" :at "fields" (listt "constructor field"))
(mot "datatype" :at "name" "name" :at (listt "datatype constructor"))

(mot "signature element" (uniont "name" "signature"))
(mot "signature" :at "input" (listt "signature element") :at "output" "signature element" )
(mot "list unfold" :at "args" (listt "name") :at "rest" "name")
(mot "function argument" (uniont "name" "list unfold"))
(mot "function branch" :at "args" (listt "function argument") :at "formula" "formula")
(mot "function" :at "name" "name" :at "signature" "signature" :at "branches" (listt "function branch"))