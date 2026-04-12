(uiop:define-package Reflex-semantics
  (:use #:cl))
(in-package #:Reflex-semantics)

(defstruct token
  type   ; :id :int :float :string :keyword :symbol :time :eof
  value
  line
  col)



(defparameter *keywords*
  '("program" "process" "state" "node" "clock" "active" "inactive" "looped"
    "if" "else" "for" "switch" "case" "default"
    "wait" "slice" "timeout" "on" 
    "set" "next" "start" "stop" "restart" "reset" "error"
    "current" "in" "break" "enum" "const"
    "input" "output" "as" "direct"))

(defparameter *multi-symbols*
  '("==" "!=" ">=" "<=" "&&" "||"
    "<<" ">>" "<<=" ">>="
    "+=" "-=" "*=" "/="
    "&=" "|=" "^="
    "++" "--" "::"))

(defstruct lexer
  source
  (pos 0)
  (line 1)
  (col 1)
  lookahead)

(defun eof-p (lx)
  (>= (lexer-pos lx) (length (lexer-source lx))))

(defun current-char (lx)
  (unless (eof-p lx)
    (char (lexer-source lx) (lexer-pos lx))))

(defun advance (lx)
  (when (current-char lx)
    (if (char= (current-char lx) #\Newline)
        (progn (incf (lexer-line lx)) (setf (lexer-col lx) 1))
        (incf (lexer-col lx)))
    (incf (lexer-pos lx))))

(defun skip-space-and-comments (lx)
  (loop
    ;; whitespace
    while (and (current-char lx)
               (find (current-char lx) " \t\r\n"))
    do (advance lx))
  ;; комментарии //
  (when (and (current-char lx)
             (char= (current-char lx) #\/)
             (char= (char (lexer-source lx) (1+ (lexer-pos lx))) #\/))
    (loop while (and (current-char lx)
                     (not (char= (current-char lx) #\Newline)))
          do (advance lx))
    (skip-space-and-comments lx)))

(defun read-identifier (lx)
  (let ((start (lexer-pos lx)))
    (loop while (and (current-char lx)
                     (or (alphanumericp (current-char lx))
                         (char= (current-char lx) #\_)))
          do (advance lx))
    (subseq (lexer-source lx) start (lexer-pos lx))))

(defun read-number (lx)
  (let ((start (lexer-pos lx)))
    (loop while (and (current-char lx)
                     (digit-char-p (current-char lx)))
          do (advance lx))
    (parse-integer
     (subseq (lexer-source lx) start (lexer-pos lx)))))

(defun read-time (lx)
  ;; формат: 0t...
  (advance lx) ;; 0
  (advance lx) ;; t
  (let ((start (lexer-pos lx)))
    (loop while (and (current-char lx)
                     (digit-char-p (current-char lx)))
          do (advance lx))
    (subseq (lexer-source lx) start (lexer-pos lx))))

(defun read-symbol (lx)
  (dolist (s *multi-symbols*)
    (let ((len (length s)))
      (when (and (<= (+ (lexer-pos lx) len) (length (lexer-source lx)))
                 (string= s (subseq (lexer-source lx)
                                    (lexer-pos lx)
                                    (+ (lexer-pos lx) len))))
        (dotimes (_ len) (advance lx))
        (return-from read-symbol s))))
  ;; одиночный символ
  (let ((c (current-char lx)))
    (advance lx)
    (string c)))

(defun next-token (lx)
  (when (lexer-lookahead lx)
    (prog1 (lexer-lookahead lx)
      (setf (lexer-lookahead lx) nil)))

  (skip-space-and-comments lx)

  (when (eof-p lx)
    (return-from next-token
      (make-token :type :eof :value nil
                  :line (lexer-line lx)
                  :col (lexer-col lx))))

  (let ((c (current-char lx))
        (line (lexer-line lx))
        (col (lexer-col lx)))
    (cond
      ;; time literal
      ((and (char= c #\0)
            (char= (char (lexer-source lx) (1+ (lexer-pos lx))) #\t))
       (let ((v (read-time lx)))
         (make-token :type :time :value v :line line :col col)))

      ;; number
      ((digit-char-p c)
       (make-token :type :int
                   :value (read-number lx)
                   :line line :col col))

      ;; identifier / keyword
      ((or (alpha-char-p c) (char= c #\_))
       (let ((id (read-identifier lx)))
         (make-token
          :type (if (member id *keywords* :test #'string=)
                    :keyword
                    :id)
          :value id
          :line line :col col)))

      ;; string literal
      ((char= c #\")
       (advance lx)
       (let ((start (lexer-pos lx)))
         (loop while (not (char= (current-char lx) #\"))
               do (advance lx))
         (let ((s (subseq (lexer-source lx) start (lexer-pos lx))))
           (advance lx)
           (make-token :type :string :value s
                       :line line :col col))))

      ;; operator / symbol
      (t
       (make-token :type :symbol
                   :value (read-symbol lx)
                   :line line :col col)))))

(defun peek-token (lexer &optional (n 0))
  (when (> n 0)
    (loop repeat n do (next-token lexer)))
  (let ((tok (or (lexer-lookahead lexer)
                 (setf (lexer-lookahead lexer)
                       (next-token lexer)))))
    tok))

(defun token-type (tok)
  (slot-value tok 'type))

(defun token-value (tok)
  (slot-value tok 'value))

(defun constant-token-p (tok)
  (member (token-type tok) '(:int :time :string)))

(defun keyword-is (tok s)
  (and (eq (token-type tok) :keyword)
       (string= (token-value tok) s)))

(defun symbol-is (tok s)
  (and (eq (token-type tok) :symbol)
       (string= (token-value tok) s)))

(defun id-token-p (tok)
  (eq (token-type tok) :id))



(defmacro expect (lexer type &optional value)
  `(let ((tok (next-token ,lexer)))
     (unless (and (eq (token-type tok) ,type)
                  ,@(when value
                      `((equal (token-value tok) ,value))))
       (error "Syntax error: expected ~A~@[ ~A~]"
              ,type ,value))
     tok))

(defun parse-program (lexer)
  (let ((ports '())
        (decls '())
        (nodes '())
        (processes '())
        (prog-name "program"))
    (loop
      for tok = (peek-token lexer)
      until (eq (token-type tok) :eof)
      do
        (case (token-type tok)
          (:keyword
           (case (intern (string-upcase (token-value tok)) :keyword)
             (:NODE (push (parse-node lexer) nodes))
             (:PROCESS (push (parse-process lexer) processes))
             (:ENUM (push (parse-enum lexer) decls))
             (:CONST (push (parse-const-decl lexer) decls))
             (t (error "Unexpected top-level keyword ~A"
                       (token-value tok)))))
          (t (error "Unexpected token at top level"))))
    (mo "program declaration"
        :av "name" prog-name
        :av "nodes" (nreverse nodes)
        :av "declarations" (nreverse decls)
        :av "processes" (nreverse processes))))

(defun parse-node (lexer)
  (expect lexer :keyword "node")
  (let ((name (token-value (expect lexer :id))))
    (expect lexer :symbol "{")
    (let ((clock nil)
          (vars '()))
      (loop
        until (equal (token-value (peek-token lexer)) "}")
        do
          (case (token-value (peek-token lexer))
            ("clock"
             (next-token lexer)
             (setf clock (parse-clock lexer))
             (expect lexer :symbol ";"))
            (t
             (push (parse-variable-decl lexer) vars))))
      (expect lexer :symbol "}")
      (mo "node declaration"
          :av "name" name
          :av "clock" clock
          :av "variables" (nreverse vars)))))

(defun parse-process (lexer)
  (let ((active nil))
    (when (equal (token-value (peek-token lexer)) "active")
      (next-token lexer)
      (setf active t))
    (expect lexer :keyword "process")
    (let ((name (token-value (expect lexer :id))))
      (expect lexer :symbol "::")
      (expect lexer :keyword "node")
      (let ((node (token-value (expect lexer :id))))
        (expect lexer :symbol "{")
        (let ((vars '())
              (states '()))
          (loop
            until (equal (token-value (peek-token lexer)) "}")
            do
              (case (token-value (peek-token lexer))
                ("state" (push (parse-state lexer) states))
                (t (push (parse-variable-decl lexer) vars))))
          (expect lexer :symbol "}")
          (mo "process declaration"
              :av "name" name
              :av "node" node
              :av "variables" (nreverse vars)
              :av "states" (nreverse states)
              :av "active" active))))))

(defun parse-state (lexer)
  (expect lexer :keyword "state")
  (let ((name (token-value (expect lexer :id)))
        (looped nil))
    (when (equal (token-value (peek-token lexer)) "looped")
      (next-token lexer)
      (setf looped t))
    (expect lexer :symbol "{")
    (let ((stmts '()))
      (loop
        until (equal (token-value (peek-token lexer)) "}")
        do
          (push (parse-statement lexer) stmts))
      (expect lexer :symbol "}")
      (mo "state declaration"
          :av "name" name
          :av "statements" (nreverse stmts)))))

(defun parse-statement (lexer)
  (let ((tok (peek-token lexer)))
    (cond
      ((keyword-is tok "if")
       (parse-if lexer))

      ((keyword-is tok "switch")
       (parse-switch lexer))

      ((keyword-is tok "for")
       (parse-for lexer))

      ((symbol-is tok "{")
       (parse-statement-block lexer))

      ((process-oriented-keyword-p tok)
       (parse-process-oriented-statement lexer))

      (t
       (parse-expression-statement lexer)))))

(defun process-oriented-keyword-p (tok)
  (member (token-value tok)
          '("set" "start" "stop" "restart" "reset"
            "error" "timeout" "slice" "wait")
          :test #'string=))

(defun parse-process-oriented-statement (lexer)
  (let ((kw (token-value (peek-token lexer))))
    (cond
      ((string= kw "slice")
       (next-token lexer)
       (expect lexer :symbol ";")
       (mo "slice"))

      ((string= kw "wait")
       (parse-wait lexer))

      ((string= kw "timeout")
       (parse-timeout lexer))

      ((string= kw "set")
       (parse-set lexer))

      ((string= kw "start")
       (parse-start-process lexer))

      ((string= kw "stop")
       (parse-stop lexer))

      ((string= kw "restart")
       (next-token lexer)
       (expect lexer :symbol ";")
       (mo "restart process"))

      ((string= kw "reset")
       (next-token lexer)
       (expect lexer :symbol ";")
       (mo "reset timer"))

      ((string= kw "error")
       (parse-lexer-error lexer))

      (t
       (error "Unknown process-oriented statement: ~A" kw)))))

(defun parse-wait (lexer)
  (expect lexer :keyword "wait")
  (let ((cond-expr (parse-expression lexer)))
    (if (keyword-is (peek-token lexer) "on")
        (progn
          (expect lexer :keyword "on")
          (expect lexer :keyword "timeout")
          (expect lexer :symbol "(")
          (let ((time-expr (parse-time-or-ref lexer)))
            (expect lexer :symbol ")")
            (let ((stmts (parse-statement-block lexer)))
              (mo "wait on timeout"
                  :av "condition" cond-expr
                  :av "controlling expression" time-expr
                  :av "statements" stmts))))
        (progn
          (expect lexer :symbol ";")
          (mo "wait" :av "condition" cond-expr)))))

(defun parse-timeout (lexer)
  (expect lexer :keyword "timeout")
  (expect lexer :symbol "(")
  (let ((tval (parse-time-or-ref lexer)))
    (expect lexer :symbol ")")
    (let ((stmts (parse-statement-block lexer)))
      (mo "timeout statement"
          :av "controlling expression" tval
          :av "statements" stmts))))

(defun parse-statement-block (lexer)
  (expect lexer :symbol "{")
  (let ((stmts '()))
    (loop
      until (symbol-is (peek-token lexer) "}")
      do (push (parse-statement lexer) stmts))
    (expect lexer :symbol "}")
    (mo "statement block"
        :av "statements" (nreverse stmts))))

(defun parse-expression-statement (lexer)
  (let ((expr (parse-expression lexer)))
    (expect lexer :symbol ";")
    (mo "expression statement"
        :av "expression" expr)))

(defun parse-if (lexer)
  (expect lexer :keyword "if")
  (expect lexer :symbol "(")
  (let ((cond-expr (parse-expression lexer)))
    (expect lexer :symbol ")")
    (let ((then-stmt (parse-statement lexer)))
      (if (keyword-is (peek-token lexer) "else")
          (progn
            (next-token lexer)
            (let ((else-stmt (parse-statement lexer)))
              (mo "if then else statement"
                  :av "condition" cond-expr
                  :av "then" then-stmt
                  :av "else" else-stmt)))
          (mo "if then statement"
              :av "condition" cond-expr
              :av "then" then-stmt)))))

(defun parse-switch (lexer)
  (expect lexer :keyword "switch")
  (expect lexer :symbol "(")
  (let ((ctrl-expr (parse-expression lexer)))
    (expect lexer :symbol ")")
    (expect lexer :symbol "{")
    (let ((cases '())
          (default nil))
      (loop
        until (symbol-is (peek-token lexer) "}")
        do
          (cond
            ((keyword-is (peek-token lexer) "case")
             (push (parse-case lexer) cases))
            ((keyword-is (peek-token lexer) "default")
             (setf default (parse-default lexer)))
            (t
             (error "Unexpected token in switch"))))
      (expect lexer :symbol "}")
      (mo "switch statement"
          :av "controlling expression" ctrl-expr
          :av "cases" (nreverse cases)
          :av "default" default))))

(defun parse-case (lexer)
  (expect lexer :keyword "case")
  (let ((label (parse-integer-constant lexer)))
    (expect lexer :symbol ":")
    (let ((stmts '())
          (break nil))
      (loop
        until (or (keyword-is (peek-token lexer) "case")
                  (keyword-is (peek-token lexer) "default")
                  (symbol-is (peek-token lexer) "}"))
        do
          (if (keyword-is (peek-token lexer) "break")
              (progn
                (next-token lexer)
                (expect lexer :symbol ";")
                (setf break t)
                (return))
              (push (parse-statement lexer) stmts)))
      (mo "case statement"
          :av "label" label
          :av "statements" (nreverse stmts)
          :av "break" break))))

(defun parse-default (lexer)
  (expect lexer :keyword "default")
  (expect lexer :symbol ":")
  (let ((stmts '()))
    (loop
      until (or (keyword-is (peek-token lexer) "case")
                (symbol-is (peek-token lexer) "}"))
      do (push (parse-statement lexer) stmts))
    (mo "default statement"
        :av "statements" (nreverse stmts))))

(defun parse-for (lexer)
  (expect lexer :keyword "for")
  (expect lexer :symbol "(")
  (let ((init (if (type-decl-start-p (peek-token lexer))
                  (parse-statement-variable-declaration lexer)
                  (parse-expression lexer))))
    (expect lexer :symbol ";")
    (let ((cond-expr (parse-expression lexer)))
      (expect lexer :symbol ";")
      (let ((update (parse-expression lexer)))
        (expect lexer :symbol ")")
        (let ((stmt (parse-statement lexer)))
          (if (mo-p init "statement variable declaration")
              (mo "for decl statement"
                  :av "init" init
                  :av "condition" cond-expr
                  :av "update" update
                  :av "statement" stmt)
              (mo "for expr statement"
                  :av "init" init
                  :av "condition" cond-expr
                  :av "update" update
                  :av "statement" stmt)))))))

(defun parse-set (lexer)
  (expect lexer :keyword "set")
  (expect lexer :keyword "state")
  (let ((name (token-value (expect lexer :id))))
    (expect lexer :symbol ";")
    (mo "set state"
        :av "state" name)))

(defun parse-start-process (lexer)
  (expect lexer :keyword "start")
  (expect lexer :keyword "process")
  (let ((name (token-value (expect lexer :id))))
    (expect lexer :symbol ";")
    (mo "start process"
        :av "process" name)))

(defun parse-stop (lexer)
  (expect lexer :keyword "stop")
  (if (keyword-is (peek-token lexer) "process")
      (progn
        (next-token lexer)
        (let ((name (token-value (expect lexer :id))))
          (expect lexer :symbol ";")
          (mo "stop process"
              :av "process" name)))
      (progn
        (expect lexer :keyword "current")
        (expect lexer :keyword "process")
        (expect lexer :symbol ";")
        (mo "stop current process"))))

(defun parse-lexer-error (lexer)
  (expect lexer :keyword "error")
  (if (keyword-is (peek-token lexer) "process")
      (progn
        (next-token lexer)
        (let ((name (token-value (expect lexer :id))))
          (expect lexer :symbol ";")
          (mo "error process"
              :av "process" name)))
      (progn
        (expect lexer :keyword "current")
        (expect lexer :keyword "process")
        (expect lexer :symbol ";")
        (mo "error current process"))))

(defparameter *binary-precedence*
  '(("||" 1)
    ("&&" 2)
    ("|"  3)
    ("^"  4)
    ("&"  5)
    ("==" 6) ("!=" 6)
    (">=" 7) ("<=" 7) (">" 7) ("<" 7)
    ("<<" 8) (">>" 8)
    ("+"  9) ("-"  9)
    ("*" 10) ("/" 10) ("%" 10)))

(defun binary-op-p (tok)
  (assoc (token-value tok) *binary-precedence* :test #'string=))

(defun precedence (op)
  (second (assoc op *binary-precedence* :test #'string=)))

(defun assignment-op-p (tok)
  (member (token-value tok)
          '("=" "+=" "-=" "*=" "/=" "<<=" ">>=" "&=" "|=" "^=")
          :test #'string=))

(defun parse-expression (lexer)
  (parse-assignment-expression lexer))

(defun parse-assignment-expression (lexer)
  (let ((lhs (parse-logical-or lexer)))
    (if (assignment-op-p (peek-token lexer))
        (let ((op (token-value (next-token lexer)))
              (rhs (parse-assignment-expression lexer)))
          (mo op
              :av "left" lhs
              :av "right" rhs))
        lhs)))

(defun parse-binary-expression (lexer min-prec)
  (let ((left (parse-unary-expression lexer)))
    (loop
      for tok = (peek-token lexer)
      for entry = (binary-op-p tok)
      while (and entry (>= (precedence (first entry)) min-prec))
      do
        (let* ((op (token-value (next-token lexer)))
               (prec (precedence op))
               (right (parse-binary-expression lexer (1+ prec))))
          (setf left
                (mo op
                    :av "left" left
                    :av "right" right))))
    left))

(defun parse-logical-or (lexer)
  (parse-binary-expression lexer 1))

(defun unary-op-p (tok)
  (member (token-value tok)
          '("!" "-" "~")
          :test #'string=))

(defun parse-unary-expression (lexer)
  (let ((tok (peek-token lexer)))
    (cond
      ;; cast
      ((symbol-is tok "(")
       (if (simple-type-start-p (peek-token lexer 1))
           (parse-cast-expression lexer)
           (parse-postfix-expression lexer)))

      ;; unary
      ((unary-op-p tok)
       (let ((op (token-value (next-token lexer)))
             (expr (parse-unary-expression lexer)))
         (mo (case op
               ("!" "!.")
               ("-" "-.")
               ("~" "~."))
             :av "expression" expr)))

      (t
       (parse-postfix-expression lexer)))))

(defun parse-cast-expression (lexer)
  (expect lexer :symbol "(")
  (let ((type (parse-simple-type lexer)))
    (expect lexer :symbol ")")
    (let ((expr (parse-unary-expression lexer)))
      (mo "cast"
          :av "type" type
          :av "expression" expr))))

(defun parse-postfix-expression (lexer)
  (let ((expr (parse-primary-expression lexer)))
    (loop
      while (member (token-value (peek-token lexer))
                    '("++" "--")
                    :test #'string=)
      do
        (let ((op (token-value (next-token lexer))))
          (setf expr
                (mo (case op
                      ("++" ".++")
                      ("--" ".--"))
                    :av "access" expr))))
    expr))

(defun parse-primary-expression (lexer)
  (let ((tok (peek-token lexer)))
    (cond
      ;; constants
      ((constant-token-p tok)
       (parse-constant lexer))

      ;; enum access
      ((and (id-token-p tok)
            (symbol-is (peek-token lexer 1) "::"))
       (parse-enum-element-access lexer))

      ;; variable / element access
      ((id-token-p tok)
       (parse-element-access lexer))

      ;; parenthesized
      ((symbol-is tok "(")
       (next-token lexer)
       (let ((expr (parse-expression lexer)))
         (expect lexer :symbol ")")
         expr))

      ;; prefix ++ --
      ((member (token-value tok) '("++" "--") :test #'string=)
       (let ((op (token-value (next-token lexer)))
             (acc (parse-element-access lexer)))
         (mo (case op
               ("++" "++.")
               ("--" "--."))
             :av "access" acc)))

      ;; process state check
      ((keyword-is tok "process")
       (parse-process-state-check lexer))

      (t
       (error "Unexpected token in expression: ~A" tok)))))

(defun parse-process-state-check (lexer)
  (expect lexer :keyword "process")
  (let ((name (token-value (expect lexer :id))))
    (expect lexer :keyword "in")
    (let ((state (token-value (expect lexer :keyword))))
      (mo "process state checking"
          :av "process" name
          :av "activity"
          (intern (string-upcase state) :keyword)))))

(defun parse-constant (lexer)
  (let ((tok (next-token lexer)))
    (case (token-type tok)
      (:int
       (mo "integer constant" (token-value tok)))
      (:time
       (mo "time constant" :av "ms" (token-value tok)))
      (:string
       (mo "string constant" (token-value tok)))
      (t
       (error "Not a constant")))))

(defun parse-integer-constant (lexer)
  (let ((tok (expect lexer :int)))
    (mo "integer constant" (token-value tok))))

(defun parse-time-or-ref (lexer)
  (let ((tok (peek-token lexer)))
    (cond
      ((eq (token-type tok) :time)
       (parse-constant lexer))
      ((eq (token-type tok) :id)
       (parse-element-access lexer))
      (t
       (error "Expected time constant or variable reference")))))

(defparameter *simple-types*
  '("int8" "int16" "int32" "int64"
    "uint8" "uint16" "uint32" "uint64"
    "float" "double" "bool" "time"))

(defun simple-type-start-p (tok)
  (and (eq (token-type tok) :id)
       (member (token-value tok) *simple-types* :test #'string=)))

(defun parse-simple-type (lexer)
  (let ((name (token-value (expect lexer :id))))
    (mo (cond
          ((member name '("bool") :test #'string=) "boolean type")
          ((member name '("float" "double") :test #'string=) "float type")
          ((string= name "time") "time type")
          ((char= (char name 0) #\u) "natural type")
          (t "integer type"))
        name)))

(defun type-decl-start-p (tok)
  (simple-type-start-p tok))

(defun parse-element-access (lexer)
  (let ((name (token-value (expect lexer :id)))
        (accesses '()))
    (loop
      while (or (symbol-is (peek-token lexer) ".")
                (symbol-is (peek-token lexer) "["))
      do
        (cond
          ((symbol-is (peek-token lexer) ".")
           (next-token lexer)
           (push (token-value (expect lexer :id)) accesses))
          ((symbol-is (peek-token lexer) "[")
           (next-token lexer)
           (push (parse-expression lexer) accesses)
           (expect lexer :symbol "]"))))
    (mo "element access"
        :av "name" name
        :av "accesses" (nreverse accesses))))

(defun parse-enum-element-access (lexer)
  (let ((enum (token-value (expect lexer :id))))
    (expect lexer :symbol "::")
    (let ((field (token-value (expect lexer :id))))
      (mo "enum element access"
          :av "name" enum
          :av "field" field))))

(defun parse-statement-variable-declaration (lexer)
  (let ((tok (peek-token lexer)))
    (cond
      ;; const
      ((keyword-is tok "const")
       (parse-const-decl lexer))

      ;; enum variable
      ((keyword-is tok "enum")
       (parse-enum-variable-declaration lexer))

      ;; struct variable
      ((keyword-is tok "struct")
       (parse-structure-variable-declaration lexer))

      ;; type ...
      ((simple-type-start-p tok)
       (parse-typed-variable-declaration lexer))

      (t
       (error "Unknown statement variable declaration")))))

(defun parse-typed-variable-declaration (lexer)
  (let ((type (parse-type lexer))
        (name (token-value (expect lexer :id))))
    (cond
      ;; array
      ((symbol-is (peek-token lexer) "[")
       (parse-array-variable-declaration lexer type name))

      ;; simple
      (t
       (parse-simple-variable-declaration lexer type name)))))

(defun parse-simple-variable-declaration (lexer type name)
  (let ((init nil))
    (when (symbol-is (peek-token lexer) "=")
      (next-token lexer)
      (setf init (parse-expression lexer)))
    (expect lexer :symbol ";")
    (mo "simple variable declaration"
        :av "type" type
        :av "name" name
        :av "init" init)))

(defun parse-array-variable-declaration (lexer elem-type name)
  (expect lexer :symbol "[")
  (let ((size (token-value (expect lexer :int))))
    (expect lexer :symbol "]")
    (let ((init nil))
      (when (symbol-is (peek-token lexer) "=")
        (next-token lexer)
        (setf init (parse-array-init lexer)))
      (expect lexer :symbol ";")
      (mo "array variable declaration"
          :av "type"
          (mo "array type"
              :av "element type" elem-type
              :av "size" size)
          :av "name" name
          :av "size" size
          :av "init" init))))

(defun parse-enum-variable-declaration (lexer)
  (expect lexer :keyword "enum")
  (let ((enum-name (token-value (expect lexer :id)))
        (var-name (token-value (expect lexer :id))))
    (expect lexer :symbol "=")
    (let ((init (parse-enum-element-access lexer)))
      (expect lexer :symbol ";")
      (mo "enum variable declaration"
          :av "name" var-name
          :av "type" enum-name
          :av "init" init))))

(defun parse-structure-variable-declaration (lexer)
  (expect lexer :keyword "struct")
  (let ((struct-name (token-value (expect lexer :id)))
        (var-name (token-value (expect lexer :id))))
    (expect lexer :symbol "=")
    (let ((init (parse-struct-init lexer)))
      (expect lexer :symbol ";")
      (mo "structure variable declaration"
          :av "name" var-name
          :av "type" struct-name
          :av "init" init))))

(defun parse-struct-init (lexer)
  (expect lexer :symbol "{")
  (let ((fields '()))
    (loop
      until (symbol-is (peek-token lexer) "}")
      do
        (let ((fname (token-value (expect lexer :id))))
          (expect lexer :symbol "=")
          (let ((init (parse-reflex-init lexer)))
            (expect lexer :symbol ";")
            (push (cons fname init) fields))))
    (expect lexer :symbol "}")
    (mo "struct init"
        :amap (nreverse fields))))


(defun parse-reflex-init (lexer)
  (let ((tok (peek-token lexer)))
    (cond
      ;; struct init
      ((symbol-is tok "{")
       (parse-struct-init lexer))

      ;; array init
      ((symbol-is tok "[")
       (parse-array-init lexer))

      ;; enum element
      ((and (id-token-p tok)
            (symbol-is (peek-token lexer 1) "::"))
       (parse-enum-element-access lexer))

      ;; simple init
      (t
       (parse-expression lexer)))))

(defun parse-array-init (lexer)
  (expect lexer :symbol "{")
  (let ((elems '()))
    (unless (symbol-is (peek-token lexer) "}")
      (loop
        do
          (push (parse-expression lexer) elems)
        while (symbol-is (peek-token lexer) ",")
        do (next-token lexer)))
    (expect lexer :symbol "}")
    (mo "array init" (nreverse elems))))


(defun parse-type (lexer)
  (let ((tok (peek-token lexer)))
    (cond
      ((simple-type-start-p tok)
       (parse-simple-type lexer))
      ((keyword-is tok "struct")
       (next-token lexer)
       (mo "structure type"
           :av "name" (token-value (expect lexer :id))))
      ((keyword-is tok "enum")
       (next-token lexer)
       (mo "enum type"
           :av "name" (token-value (expect lexer :id))))
      (t
       (error "Unknown type")))))



(defun mo-p (obj name)
  (and (consp obj)
       (string= (car obj) name)))

(defun parse-clock (lexer)
  (let ((tok (peek-token lexer)))
    (cond
      ((eq (token-type tok) :int)
       (parse-integer-constant lexer))
      ((eq (token-type tok) :time)
       (parse-constant lexer))
      (t
       (error "Invalid clock value")))))

(defun parse-variable-decl (lexer)
  (let ((tok (peek-token lexer)))
    (cond
      ((simple-type-start-p tok)
       (parse-statement-variable-declaration lexer))
      (t
       (error "Unknown variable declaration")))))

(defun parse-const-decl (lexer)
  (expect lexer :keyword "const")
  (let ((type (parse-simple-type lexer))
        (name (token-value (expect lexer :id))))
    (expect lexer :symbol "=")
    (let ((value (parse-expression lexer)))
      (expect lexer :symbol ";")
      (mo "constant declaration"
          :av "type" type
          :av "name" name
          :av "value" value))))

(defun parse-enum (lexer)
  (expect lexer :keyword "enum")
  (let ((fields '()))
    (expect lexer :symbol "{")
    (loop
      until (symbol-is (peek-token lexer) "}")
      do
        (let ((name (token-value (expect lexer :id))))
          (expect lexer :symbol "=")
          (let ((value (token-value (expect lexer :int))))
            (expect lexer :symbol ";")
            (push (mo "enum field"
                      :av "name" name
                      :av "value" value)
                  fields))))
    (expect lexer :symbol "}")
    (expect lexer :symbol ";")
    (mo "enum declaration"
        :av "fields" (nreverse fields))))

(defun parse-reflex-program-from-string (source)
  (let ((lexer (make-lexer source)))
    (parse-program lexer)))

(defun write-abml-to-file (abml filename)
  (with-open-file (out filename
                       :direction :output
                       :if-exists :supersede
                       :if-does-not-exist :create)
    (let ((*print-pretty* t)
          (*print-length* nil)
          (*print-level* nil))
      (pprint abml out))))
