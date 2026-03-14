(uiop:define-package Reflex-semantics
  (:use #:cl))
(in-package #:Reflex-semantics)

;(is-instance i bool) всегда истинно?



(typedef "bool constant" (enumt 'true 'false))
(typedef "integer constant" (enumt int))
(typedef "natural constant" (enumt nat))
(typedef "float constant" (enumt real))

(mot "days" :at "value" nat)
(mot "hours" :at "value" nat)
(mot "minutes" :at "value" nat)
(mot "seconds" :at "value" nat)
(mot "milliseconds" :at "value" nat)
(mot "time constant" :at "d" "days" :at "h" "hours" :at "m" "minutes" :at "s" "seconds" :at "ms" "milliseconds")

(typedef "non time constant" (uniont "bool constant" "integer constant" "natural constant" 
  "float constant" "boolean constant"))
(typedef "constant" (uniont "non time constant" "time constant"))


(typedef "name" (enumt string))
(typedef "variable name" (uniont "name"))
(typedef "process name" (uniont "name"))
(typedef "state name" (uniont "name"))
(typedef "program name" (uniont "name"))
(typedef "structure name" (uniont "name"))
(typedef "field name" (uniont "name"))
(typedef "enum name" (uniont "name"))
(typedef "port name" (uniont "name"))
(typedef "node name" (uniont "name"))


(typedef "integer type" (enumt 'int8 'int16 'int32 'int64))
(typedef "natural type" (enumt 'uint8 'uint16 'uint32 'uint64))
(typedef "float type" (enumt 'float 'double))
(typedef "boolean type" (enumt 'bool))
(typedef "time type" (enumt 'time))
(typedef "simple type" (uniont "integer type" "natural type" "float type" "boolean type" "time type"))
(mot "array type" :at "element type" "type" :at "size" "expression")
(mot "structure type" :at "name" "structure name")
(mot "enum type" :at "name" "enum name")
(typedef "type" (uniont "simple type" "array type" "structure type" "enum type"))

(typedef "undefined type" (enumt 'undefined-int-type 'undefined-float-type))
(typedef "extended type" (uniont "type" "undefined type"))

;Expressions
(typedef "access" (uniont "expression" "field name"))
(mot "element access" :at "name" "variable name" :at "accesses" (listt "access"))
(mot "enum element access" :at "name" "enum name" :at "field" "field name")

(mot "+" :at "left" "expression" :at "right" "expression")
(mot "-" :at "left" "expression" :at "right" "expression")
(mot "*" :at "left" "expression" :at "right" "expression")
(mot "/" :at "left" "expression" :at "right" "expression")
(mot "%" :at "left" "expression" :at "right" "expression")
(mot ">>" :at "left" "expression" :at "right" "expression")
(mot "<<" :at "left" "expression" :at "right" "expression")

(mot "==" :at "left" "expression" :at "right" "expression")
(mot "!=" :at "left" "expression" :at "right" "expression")
(mot ">=" :at "left" "expression" :at "right" "expression")
(mot "<=" :at "left" "expression" :at "right" "expression")
(mot ">" :at "left" "expression" :at "right" "expression")
(mot "<" :at "left" "expression" :at "right" "expression")

(mot "&&" :at "left" "expression" :at "right" "expression")
(mot "||" :at "left" "expression" :at "right" "expression")

(mot "&" :at "left" "expression" :at "right" "expression")
(mot "|" :at "left" "expression" :at "right" "expression")
(mot "^" :at "left" "expression" :at "right" "expression")

(mot "cast" :at "type" "simple type" :at "expression" "expression")
(mot "!." :at "expression" "expression")
(mot "-." :at "expression" "expression")
(mot "~." :at "expression" "expression")

(mot "=" :at "left" "element access" :at "right" "expression")
(mot "+=" :at "left" "element access" :at "right" "expression")
(mot "*=" :at "left" "element access" :at "right" "expression")
(mot "-=" :at "left" "element access" :at "right" "expression")
(mot "/=" :at "left" "element access" :at "right" "expression")
(mot "%=" :at "left" "element access" :at "right" "expression")
(mot "<<=" :at "left" "element access" :at "right" "expression")
(mot ">>=" :at "left" "element access" :at "right" "expression")
(mot "&=" :at "left" "element access" :at "right" "expression")
(mot "|=" :at "left" "element access" :at "right" "expression")
(mot "^=" :at "left" "element access" :at "right" "expression")

(mot "++." :at "access" "element access")
(mot ".++" :at "access" "element access")
(mot "--." :at "access" "element access")
(mot ".--" :at "access" "element access")

(typedef "activity" (enumt 'active 'inactive 'stop 'nonstop 'error 'nonerror))
(mot "process state checking" :at "process" "process name" :at "activity" "activity")


(typedef "binary expression" (uniont "+" "-" "*" "/" "%" ">>" "<<" "==" "!=" ">=" "<=" ">" "<" "&&" "||" "&" "|" "^"))
(typedef "unary expression" (uniont "cast" "!." "-." "~."))
(typedef "prefix&postfix" (uniont "++." ".++" "--." ".--"))
(typedef "assignment expression" (uniont "=" "+=" "-=" "*=" "/=" "%" "<<=" ">>=" "&=" "|=" "^="))

(typedef "expression" (uniont "binary expression" "unary expression" "prefix&postfix" "assignment expression" "element access" "process state checking" "constant"))

;Statements

(mot "reset timer")
(mot "set state" :at "state" "state name")

(mot "restart process")
(mot "start process" :at "process" "process")

(mot "stop current process")
(mot "stop process" :at "process" "process")

(mot "error current process")
(mot "error process" :at "process" "process")

(typedef "statement list" (uniont (listt "statement")))

(mot "timeout statement" :at "controlling expression" "time amount or ref" :at "statements" "statement list")
(typedef "time amount or ref" (uniont "constant" "element access"))


(mot "slice")
(mot "wait" :at "condition" "expression")
(mot "wait on timeout" :at "condition" "expression" :at "controlling expression" "time amount or ref" :at "statements" "statement list")
(mot "barrier statement" (uniont "wait" "slice" "wait" "wait on timeout"))

(mot "process oriented statement" (uniont "reset timer" "set state" "restart process" "start process" "stop current process" "stop process" "error current process" "error process" "timeout statement" "barrier statement"))

(mot "if then statement" :at "condition" "expression" :at "then" "statement")
(mot "if then else statement" :at "condition" "expression" :at "then" "statement" :at "else" "statement")
(typedef "if statement" (uniont "if then statement" "if then else statement"))

(mot "switch statement" :at "controlling expression" "expression" :at "cases" (listt "case statement") :at "default" "default statement")
(mot "default statement" :at "statements" "statement list")
(mot "case statement" :at "label" "integer constant" :at "statements" "statement list" :atv "break" bool nil)

(mot "for expr statement" :at "init" "expression" :at "condition" "expression" :at "update" "expression" :at "statement" "statement")
(mot "for decl statement" :at "init" "statement variable declaration" :at "condition" "expression" :at "update" "expression" :at "statement" "statement")
(typedef "for statement" (uniont "for expr statement" "for decl statement"))
(mot "statement block" :at "statements" "statement list")

(mot "expression statement" :at "expression" "expression")

(typedef "statement variable declaration" (uniont "simple variable declaration" "array variable declaration" "structure variable declaration" "enum variable declaration" "constant declaration"))

(typedef "statement" (uniont "expression statement" "if statement" "switch statement" "statement block" "statement variable declaration" "for statement"
"process oriented statement"))

;Declarations

(mot "state declaration" :at "name" "state name" :at "statements" "statement list")

(mot "constant declaration" :at "type" "simple type" :at "name" "variable name" :at "value" "expression")

(typedef "simple init" (uniont "expression"))
(mot "simple variable declaration" :at "type" "simple type" :at "name" "variable name" :at "init" "simple init" :atv "shared" bool nil)
(typedef "expression list" (listt "expression"))
(typedef "array init" (uniont "expression list"))
(mot "array variable declaration" :at "type" "array type" :at "name" "variable name" :at "size" int :at "init" "array init" :atv "shared" bool nil)

(mot "imported variable declaration" :at "name" "variable name" :at "source proc" "process name" :at "source var" "process name")

(mot "physical variable declaration" :at "type" "simple type" :at "name" "variable name" :at "port" "port name" :at "index" int)

(mot "enum variable declaration" :at "name" "variable name" :at "type" "enum name" :at "init" "enum element access" :atv "shared" bool nil)

(mot "struct field" :av "name" "field name" :av "init" "reflex init")
(typedef "struct init" (listt "struct field"))
(mot "structure variable declaration" :at "name" "variable name" :at "type" "structure name" :at "init" "struct init" :atv "shared" bool nil)

(typedef "reflex init" (uniont "simple init" "array init" "struct init" "enum element access"))

(typedef "process variable declaration" (uniont "statement variable declaration" "physical variable declaration"))

(mot "process declaration" 
    :at "name" "process name"
    :at "node" "node name"
    :at "variables" (listt "process variable declaration")
    :at "states" (listt "state declaration")
    :at "active" bool)


(mot "structure field declaration" :at "name" "field name" :at "type" "type")
(mot "structure declaration" :at "name" "variable name" :at "fields" (listt "structure field declaration"))

(mot "enum field" :at "name" "variable name" :at "value" int)
(mot "enum declaration" :at "name" "name" :at "fields" (listt "enum field"))

(typedef "port type" (enumt 'input 'output))
(mot "port declaration" :at "port type" "port type" :at "name" "port name" :at "addr1" int :at "addr2" int :at "size" int)

(mot "node declaration" :av "name" "node name" :av "clock" "clock" :av "variables" (listt "process variable declaration"))

(mot "program item declaration" :union
  ("port declaration"
  "statement variable declaration"
  "physical variable declaration"
  "structure declaration"  
  "enum declaration"
))

(typedef "clock" (uniont "natural constant" "time constant"))
(mot "program declaration" 
    :at "name" "program name" 
    :atv "clock" "clock" 100
    :at "nodes" (listt "node declaration")
    :at "declarations" (listt "program item declaration")
    :at "processes" (listt "process declaration")
)