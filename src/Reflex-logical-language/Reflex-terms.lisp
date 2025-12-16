(uiop:define-package Reflex-semantics
  (:use #:cl))
(in-package #:Reflex-semantics)

(mot "program state name" (enumt symbol))
(mot "outer var" (enumt "name"))
(mot "term" (uniont "actuatable term" "nonactuatable term"))
(mot "actuatable term" (uniont "binary operation" "unary operation" "value getter"  "cast operation"))
(mot "nonactuatable term" (uniont "constant" "pstate compare" "outer var" "value list" "value map"))
(mot "value list" (uniont listt "term"))
(mot "value map" (uniont cot))

(mot "access" (uniont "term" "field name"))
(mot "variable access" :at "name" "variable" :at "path" (listt "access"))

(mot "value getter"
    :at "type" "simple type"
    :at "state" "program state"
    :at "access" "variable access"
    :at "actuated" bool)
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
    :at "actuated" bool)
(mot "unary operation" 
    :at "type" "simple type"
    :at "op" "uop"
    :at "right" "term" 
    :at "actuated" bool)
(mot "cast operation" 
    :at "type" "simple type"
    :at "pretype" "simple type" 
    :at "right" "term" 
    :at "actuated" bool)


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
(mot "process activity" :at "state" "program state" :av "process" "process name" :av "activity" (uniont 'active 'stop 'error 'inactive 'nonstop 'nonerror))
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
(mot "state notupdating formula" (uniont "forall" "exists" "ltime check" "term" "implication" "inv plug" "conjunction" "disjunction" "process activity" "process activity block"))

(mot "program state" (uniont "program state name" "value setter"))
(mot "reset" :at "state" "program state")
(mot "to env" :at "state" "program state")
(mot "pstate setter" :at "state" "program state" :av "process" "process name" :av "pstate" "state name")
(mot "state updating formula" (uniont "program state" "pstate setter" "reset" "to env"))

(mot "formula" (uniont "state notupdating formula" "state updating formula"))
(mot "vc lemma" 
    :at "precondition" "formula" 
    :at "postcondition" "formula" 
    :at "steps" (listt "formula"))




;В работе
(mot "constructor field" :av "name" "name" :av "type" "name")
(mot "datatype constructor" :av "name" "name" :av "fields" (listt "constructor field"))
(mot "datatype" :av "name" "name" :av (listt "datatype constructor"))

(mot "signature element" (uniont "name" "signature"))
(mot "signature" :av "input" (listt "signature element") :av "output" "signature element" )
(mot "list unfold" :av "args" (listt "name") :av "rest" "name")
(mot "function argument" (uniont "name" "list unfold"))
(mot "function branch" :av "args" (listt "function argument") :av "formula" "formula")
(mot "function" :av "name" "name" :av "signature" "signature" :av "branches" (listt "function branch"))