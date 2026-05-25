(uiop:define-package Reflex-semantics
  (:use #:cl))
(in-package #:Reflex-semantics)

(typedef "type" (uniont (enumt 'int 'nat 'real 'bool 'string 'char) string))

(typedef "unary operator" (enumt"+" "-" "!"))

(typedef "binary operator"
  (enumt "+" "-" "*" "/" "%" "<" "<=" ">" ">=" "=""!=" "&&" "||" "^" "==>" "<=>" "&" "|" "<<" ">>"))


(typedef "scope specifier"
  (uniont
    (enumt "pre" "prev")
    "past scope specifier"))

(mot "past scope specifier" :at "condition" "specification expression")


(typedef "quantifier kind" (enumt "forall" "exists"))

(typedef "domain expression" (uniont "collection domain" "range domain"))

(mot "collection domain" :at "expression" "specification expression")

(mot "range domain" :at "from" "specification expression" :at "to" "specification expression")

(mot "quantified variable" :at "name" string :atv "domain" "domain expression"nil)


(mot "identifier expression" :at "name" string)

(mot "unary expression" :at "operator" "unary operator" :at "operand" "specification expression")

(mot "binary expression" :at "operator" "binary operator" :at "left" "specification expression" :at "right" "specification expression")

(mot "function call" :at "name" "identifier expression" :at "arguments" (listt "specification expression"))

(mot "struct access" :at "object" "specification expression" :at "member" string)

(mot "array access" :at "array" "specification expression" :at "index" "specification expression")

(mot "scoped expression" :at "expression" "specification expression" :at "scope" "scope specifier")

(mot "quantified expression"  
  :at "quantifier" "quantifier kind" 
  :at "variables" (listt "quantified variable") 
  :at "body" "specification expression")


(mot "previously" :at "arguments" (listt "specification expression"))
(mot "next" :at "arguments" (listt "specification expression"))
(mot "once" :at "arguments" (listt "specification expression"))
;(mot "eventually" :at "arguments" (listt "specification expression"))
(mot "during" :at "arguments" (listt "specification expression"))

(typedef "temporal expression"
  (uniont "previously" "next" "once" "during"))


(mot "variable definition" :at "type" "type" :at "name" string :at "expression" "specification expression")
(mot "parameter" :at "type" "type" :at "name" string)
(mot "function definition" :at "type" "type" :at "name" string :at "parameters" (listt "parameter") :at :at "expression" "specification expression")
(typedef "definition list" (listt "definition"))

(typedef "bool constant" (enumt 'true 'false))
(typedef "integer constant" int)
(typedef "natural constant" nat)
(typedef "float constant" real)
(typedef "string constant" string)
(mot "char constant" :at "value" string)

(mot "time constant" :at "d" nat :at "h" nat :at "m" nat :at "s" nat :at "ms" nat)

(typedef "number constant" (uniont "integer constant" "natural constant" 
  "float constant"))
(typedef "constant" (uniont "bool constant" "number constant" "time constant" "string constant" "char constant"))


(typedef "specification expression"
  (uniont
    "identifier expression"
    "unary expression"
    "binary expression"
    "function call"
    "struct access"
    "array access"
    "scoped expression"
    "quantified expression"
    "temporal expression"
    "constant"))

(typedef "annotation kind"
  (enumt
    "assume"
    "assert"
    "invariant"
    "define"))

(mot "annotation"
    :at "kind" "annotation kind"
    :atv "language" string nil
    :at "body" (uniont "specification expression" "definition list"))

(mot "annotation block" :at "annotations" (listt "annotation"))
