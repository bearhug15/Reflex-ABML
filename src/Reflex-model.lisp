(uiop:define-package Reflex-semantics
  (:use #:cl))
(in-package #:Reflex-semantics)

;(is-instance i bool) всегда истинно?



(typedef "bool constant" (enumt 'true 'false))
(typedef "integer constant" int)
(typedef "natural constant" nat)
(typedef "float constant" real)
(typedef "string constant" string)
(mot "char constant" :at "value" string)

(mot "time constant" :at "d" nat :at "h" nat :at "m" nat :at "s" nat :at "ms" nat)

(typedef "number constant" (uniont "integer constant" "natural constant" 
  "float constant" ))
(typedef "constant" (uniont "bool constant" "number constant" "time constant" "string constant" "char constant"))


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

(typedef "common binary operation" (enumt "+" "-" "*" ">>" "<<" "==" "!=" ">=" "<=" ">" "<" "&" "|" "^"))
(mot "common binary expression"
  :at "left" "expression"
  :at "right" "expression" 
  :at "op" "common binary operation")
(typedef "division binary operation" (enumt "/" "%"))
(mot "division binary expression"
  :at "left" "expression"
  :at "right" "expression" 
  :at "op" "division binary operation")
(mot "conjunction binary expression"
  :at "left" "expression"
  :at "right" "expression")
(mot "disjunction binary expression"
  :at "left" "expression"
  :at "right" "expression")
(typedef "binary expression" (uniont "common binary expression" "division binary expression" "conjunction binary expression" "disjunction binary expression"))

(typedef "unary operation" (enumt "!." "-." "~."))
(mot "unary expression"
  :at "right" "expression" 
  :at "op" "unary operation")
(mot "cast"
  :at "type" "simple type"
  :at "right" "expression")

(typedef "common assignment operation" (enumt "=" "+=" "-=" "*=" "/=" "%=" "<<=" ">>=" "&=" "|=" "^="))
(mot "common assignment"
  :at "left" "element access" 
  :at "right" "expression"
  :at "op" "common assignment operation")
(typedef "division assignment operation" (enumt "/=" "%="))
(mot "division assignment"
  :at "left" "element access" 
  :at "right" "expression"
  :at "op" "division assignment operation")
(typedef "assignment expression" (uniont "common assignment" "division assignment"))


(typedef "prefix&postfix operation" (enumt "++." ".++" "--." ".--"))
(mot "prefix&postfix expression"
  :at "access" "element access"
  :at "op" "prefix&postfix operation")

(typedef "activity" (enumt 'active 'inactive 'stop 'nonstop 'error 'nonerror))
(mot "process state checking" :at "process" "process name" :at "activity" "activity")


(mot "function call" :av "name" "name" :av "args" (listt "expression"))

(typedef "expression" (uniont "binary expression" "unary expression" "cast" "prefix&postfix expression" "assignment expression" "element access" "process state checking" "constant" "function call"))

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
(typedef "barrier statement" (uniont "wait" "slice" "wait" "wait on timeout"))

(mot "process oriented statement" (uniont "reset timer" "set state" "restart process" "start process" "stop current process" "stop process" "error current process" "error process" "timeout statement" "barrier statement"))

(mot "if then statement" :at "condition" "expression" :at "then" "statement")
(mot "if then else statement" :at "condition" "expression" :at "then" "statement" :at "else" "statement")
(typedef "if statement" (uniont "if then statement" "if then else statement"))

(mot "switch statement" :at "controlling expression" "expression" :at "cases" (listt "case statement") :at "default" "default statement")
(mot "default statement" :at "statements" "statement list")
(mot "case statement" :at "label" "constant" :at "statements" "statement list" :atv "break" bool nil)

(typedef "init for" (uniont "expression" "statement variable declaration"))
(mot "for statement" :at "init" (listt "init for") :at "condition" "expression" :at "update" "expression" :at "statement" "statement")
(mot "statement block" :at "statements" "statement list")

(mot "expression statement" :at "expression" "expression")

(typedef "statement variable declaration" (uniont "simple variable declaration" "array variable declaration" "structure variable declaration" "enum variable declaration" "constant declaration"))

(typedef "statement" (uniont "expression statement" "if statement" "switch statement" "statement block" "statement variable declaration" "for statement"
"process oriented statement" "c code" "return statement"))

(mot "return statement"
  :at "expression" "expression")

(mot "c code"
  :at "code" string)

;Declarations

(mot "state declaration" :at "name" "state name" :at "statements" "statement list")

(mot "constant declaration" :at "type" "simple type" :at "name" "variable name" :at "value" "expression")

(typedef "simple init" (uniont "expression"))
(mot "simple variable declaration" :at "type" "simple type" :at "name" "variable name" :at "init" "simple init" :atv "shared" bool nil)
(typedef "expression list" (listt "expression"))
(typedef "struct list" (listt "struct init"))
(typedef "array init" (uniont "expression list"))
(mot "array variable declaration" :at "type" "array type" :at "name" "variable name" :at "size" int :at "init" "array init" :atv "shared" bool nil)

(mot "struct field" :av "name" "field name" :av "init" "reflex init")
(typedef "struct init" (listt "struct field"))
(mot "structure variable declaration" :at "name" "variable name" :at "type" "structure name" :at "init" "struct init" :atv "shared" bool nil)

(typedef "reflex init" (uniont "simple init" "array init" "struct init" "enum element access"))

(mot "enum variable declaration" :at "name" "variable name" :at "type" "enum name" :at "init" "enum element access" :atv "shared" bool nil)


(mot "imported variable declaration" :at "name" "variable name" :at "source proc" "process name" :at "source var" "process name")

(mot "physical variable declaration"
  :at "type" "type"
  :at "name" "variable name"
  :at "mapping type" (enumt 'direct 'indirect)
  :at "direction" (enumt 'input 'output)
  :atv "read port" "name" nil
  :atv "write port" "name" nil
  :atv "config port" "name" nil
  :atv "bit" "name" nil)
(typedef "process variable declaration" (uniont "simple variable declaration" 
"array variable declaration" 
"structure variable declaration" 
"enum variable declaration" 
"imported variable declaration"
"physical variable declaration"))

(mot "process declaration"
  :at "name" "process name"
  :atv "node" "node name" nil
  :at "imports" (listt "imported variable declaration")
  :at "variables" (listt "process variable declaration")
  :at "states" (listt "state declaration")
  :atv "active" bool)

(mot "structure field declaration" :at "name" "field name" :at "type" "type")
(mot "structure declaration" :at "name" "variable name" :at "fields" (listt "structure field declaration"))

(mot "enum field" :at "name" "variable name" :at "value" int)
(mot "enum declaration" :at "name" "name" :at "fields" (listt "enum field"))

(mot "farg" :av "type" "type" :av "name" "variable name")
(mot "function declaration"
  :av "name" "name"
  :av "return type" "type"
  :av "params" (listt "farg")
  :av "body" (listt "statement")
  :av "is declaration" bool)

(mot "isr"
  :at "vector" "name"
  :atv "node" "node name" nil
  :at "body" "statement block")

(mot "node declaration"
  :at "name" "node name"
  :at "clock" "clock"
  :at "globals" (listt "global variable declaration")
  :at "consts" (listt "const")
  :at "isrs" (listt "isr"))
;(mot "node declaration" :av "name" "node name" :av "clock" "clock" :av "variables" (listt "process variable declaration"))

(typedef "global variable declaration"
  (uniont
    "physical variable declaration"
    "simple variable declaration"
    "array variable declaration"
    "structure variable declaration"
    "enum variable declaration"
    "constant declaration"))

(typedef "global declaration"
  (uniont
    "global variable declaration"
    "enum declaration"
    "function declaration"))

(mot "register" :at "name" "name" :atv "type" "type" nil)
(mot "bit" :at "name" "name")
(mot "vector" :at "name" "name" :atv "type" "type" nil)

(mot "import"
  :at "name" "name"
  :at "registers" (listt "register")
  :at "bits" (listt "bit")
  :at "vectors" (listt "vector"))

(typedef "clock" (uniont "natural constant" "time constant"))
(mot "program declaration"
  :at "name" "program name"
  :at "clock" "clock"
  :at "imports" (listt "import")
  :at "registers" (listt "register")
  :at "bits" (listt "bit")
  :at "vectors" (listt "vector")
  :at "globals" (listt "global declaration")
  :at "isrs" (listt "isr")
  :at "nodes" (listt "node declaration")
  :at "processes" (listt "process declaration"))
