(uiop:define-package #:reflex-annotations (:use #:cl)) 

(in-package #:reflex-annotations) 

;;;; ============================================================
 
;;;; LEXER
 
;;;; ============================================================


(defstruct token type value position) 

(define-condition lexer-error (error) 
  (
    (message :initarg :message :reader lexer-error-message) 
    (position :initarg :position :reader lexer-error-position)) 
  (:report 
    (lambda (c s) 
      (format s "Lexer error at position ~A: ~A" 
        (lexer-error-position c) 
        (lexer-error-message c))))) 

(defun lexer-error 
  (position format-string &rest args) 
  (error 'lexer-error :position position :message 
    (apply #'format nil format-string args))) 


(defun whitespace-char-p (c) 
  (member c '(#\Space #\Tab #\Newline #\Return))) 

(defun identifier-start-char-p (c) 
  (or (alpha-char-p c) (char= c #\_))) 

(defun identifier-char-p (c) 
  (or 
    (identifier-start-char-p c) (digit-char-p c))) 

(defun digit-char-p* (c) 
  (and c (digit-char-p c))) 

(defun peek-char-at (source position) 
  (when 
    (< position (length source)) 
    (char source position))) 

(defun starts-with-at-p 
  (source position prefix) 
  (let 
    (
      (end 
        (+ position (length prefix)))) 
    (and 
      (<= end (length source)) 
      (string= source prefix :start1 position :end1 end)))) 


(defparameter *multi-char-operators* '("<=>" "==>" "&&" "||" "<<" ">>" "<=" ">=" "!=")) 

(defparameter *single-char-operators* '("+" "-" "*" "/" "%" "<" ">" "=" "!" "^" "&" "|")) 

(defparameter *keywords* '("assume" "assert" "invariant" "define" "forall" "exists" "previously" "next" "once" "during" "pre" "prev" "past" "true" "false")) 


(defun make-simple-token (type value position) 
  (make-token :type type :value value :position position)) 


(defun lex-string (source position) 
  (let 
    ((start position) 
      (buffer 
        (make-string-output-stream))) (incf position) 
    (loop 
      (when 
        (>= position (length source)) 
        (lexer-error start "Unterminated string literal")) 
      (let 
        (
          (c 
            (char source position))) 
        (cond 
          ((char= c #\\) (incf position) 
            (when 
              (>= position (length source)) 
              (lexer-error start "Invalid escape sequence")) 
            (let 
              (
                (escaped 
                  (char source position))) 
              (write-char 
                (case escaped (#\\ #\\) (#\" #\") (#\n #\Newline) (#\t #\Tab) (#\r #\Return) (otherwise escaped)) buffer))) 
          ((char= c #\") (incf position) (return)) 
          (t (write-char c buffer))) (incf position))) 
    (values 
      (make-simple-token :string 
        (get-output-stream-string buffer) start) position))) 


(defun lex-number (source position) 
  (let 
    ((start position) (has-dot nil)) 
    (loop while 
      (< position (length source)) for c = 
      (char source position) do 
      (cond 
        ((digit-char-p c) (incf position)) 
        (
          (and (char= c #\.) (not has-dot)) (setf has-dot t) (incf position)) (t (return)))) 
    (let* 
      (
        (text 
          (subseq source start position)) 
        (value 
          (if has-dot 
            (read-from-string text) (parse-integer text)))) 
      (values 
        (make-simple-token 
          (if has-dot :float :integer) value start) position)))) 
 

(defun lex-identifier (source position) 
  (let ((start position)) 
    (loop while 
      (and 
        (< position (length source)) 
        (identifier-char-p 
          (char source position))) do (incf position)) 
    (let 
      (
        (text 
          (subseq source start position))) 
      (values 
        (make-simple-token 
          (if 
            (member text *keywords* :test #'string=) :keyword :identifier) text start) position)))) 


(defun lex-operator (source position) 
  (dolist 
    (op *multi-char-operators*) 
    (when 
      (starts-with-at-p source position op) 
      (return-from lex-operator 
        (values 
          (make-simple-token :operator op position) 
          (+ position (length op)))))) 
  (let* 
    (
      (c 
        (peek-char-at source position)) (s (string c))) 
    (when 
      (member s *single-char-operators* :test #'string=) 
      (return-from lex-operator 
        (values 
          (make-simple-token :operator s position) (1+ position))))) nil) 


(defun skip-line-comment (source position) 
  (loop while 
    (and 
      (< position (length source)) 
      (not 
        (char= 
          (char source position) #\Newline))) do (incf position)) position) 

(defun skip-block-comment (source position) 
  (let ((start position)) (incf position 2) 
    (loop while 
      (< position (length source)) do 
      (if 
        (starts-with-at-p source position "*/") 
        (return (+ position 2)) (incf position))) 
    (lexer-error start "Unterminated block comment"))) 


(defun lex (source) 
  (let 
    ((position 0) (tokens '())) 
  (labels 
    (
      (emit (type value pos) 
        (push 
          (make-simple-token type value pos) tokens))) 
    (loop while 
      (< position (length source)) do 
      (let 
        (
          (c 
            (char source position))) 
        (cond 
;; whitespace
 
          ((whitespace-char-p c) (incf position)) 
;; line comment
 
          (
            (starts-with-at-p source position "//") 
            (setf position 
              (skip-line-comment source position))) 
;; block comment
 
          (
            (starts-with-at-p source position "/*") 
            (setf position 
              (skip-block-comment source position))) 
;; string
 
          ((char= c #\") 
            (multiple-value-bind (token next) 
              (lex-string source position) (push token tokens) (setf position next))) 
;; number
 
          ((digit-char-p c) 
            (multiple-value-bind (token next) 
              (lex-number source position) (push token tokens) (setf position next))) 
;; identifier
 
          (
            (identifier-start-char-p c) 
            (multiple-value-bind (token next) 
              (lex-identifier source position) (push token tokens) (setf position next))) 
;; operators
 
          (
            (lex-operator source position) 
            (multiple-value-bind (token next) 
              (lex-operator source position) (push token tokens) (setf position next))) 
;; punctuation
 
          (
            (char= c #\() 
              (emit :lparen "(" position) (incf position)) ((char= c #\)) (emit :rparen ")" position) (incf position)) 
          ((char= c #\[) 
            (emit :lbracket "[" position) (incf position)) 
          ((char= c #\]) 
            (emit :rbracket "]" position) (incf position)) 
          ((char= c #\{) 
            (emit :lbrace "{" position) (incf position)) 
          ((char= c #\}) 
            (emit :rbrace "}" position) (incf position)) 
          ((char= c #\,) 
            (emit :comma "," position) (incf position)) 
          ((char= c #\.) 
            (emit :dot "." position) (incf position)) 
          ((char= c #\:) 
            (emit :colon ":" position) (incf position)) 
          ((char= c #\;)
 
              (emit :semicolon ";" position)(incf position)) 
;; unknown character
 
            (t 
              (lexer-error position "Unexpected character '~A'" c))))) 
      (push 
        (make-simple-token :eof nil position) tokens) (nreverse tokens)))) 

;;;; ============================================================
 
;;;; PARSER
 
;;;; ============================================================
 

(define-condition parser-error (error) 
  (
    (message :initarg :message :reader parser-error-message) 
    (token :initarg :token :reader parser-error-token)) 
  (:report 
    (lambda (c s) 
      (format s "Parser error near token ~A: ~A" 
        (parser-error-token c) 
        (parser-error-message c))))) 

(defun parser-error 
  (token format-string &rest args) 
  (error 'parser-error :token token :message 
    (apply #'format nil format-string args))) 


(defstruct parser-state tokens (position 0)) 

(defun current-token (state) 
  (nth 
    (parser-state-position state) 
    (parser-state-tokens state))) 

(defun advance (state) 
  (incf 
    (parser-state-position state))) 

(defun match-token 
  (state type &optional value) 
  (let 
    (
      (token (current-token state))) 
    (and token 
      (eq (token-type token) type) 
      (or (null value) 
        (equal (token-value token) value))))) 

(defun expect-token 
  (state type &optional value) 
  (let 
    (
      (token (current-token state))) 
    (unless 
      (match-token state type value) 
      (parser-error token "Expected token type ~A value ~A" type value)) (advance state) token)) 

(defun consume-token 
  (state type &optional value) 
  (when 
    (match-token state type value) 
    (let 
      (
        (token (current-token state))) (advance state) token))) 


(defun parse-type (state) 
  (let 
    (
      (token (current-token state))) 
    (unless 
      (or 
        (match-token state :identifier) 
        (match-token state :keyword)) 
      (parser-error token "Expected type name")) (advance state) (token-value token))) 


(defun parse-constant (state) 
  (let 
    (
      (token (current-token state))) 
    (cond 
      (
        (match-token state :integer) (advance state) (token-value token)) 
      (
        (match-token state :float) (advance state) (token-value token)) 
      (
        (match-token state :string) (advance state) (token-value token)) 
      (
        (and 
          (match-token state :keyword) 
          (member (token-value token) '("true" "false") :test #'string=)) (advance state) 
      (if 
        (string= (token-value token) "true") 'true 'false)) (t nil)))) 


(defun parse-identifier-expression (state) 
  (let 
    (
      (token 
        (expect-token state :identifier))) 
    (mo "identifier expression" :av "name" (token-value token)))) 


(defun parse-parenthesized-expression (state) 
  (expect-token state :lparen) 
  (let 
    (
      (expr 
        (parse-expression state))) 
    (expect-token state :rparen) expr)) 

(defun parse-argument-list (state) 
  (let ((args '())) 
  (unless 
    (match-token state :rparen) 
    (push 
      (parse-expression state) args) 
    (loop while 
      (consume-token state :comma) do 
      (push 
        (parse-expression state) args))) (nreverse args))) 

(defun parse-postfix-expression (state) 
  (let 
    (
      (expr 
        (parse-primary-expression state))) 
    (loop 
      (cond 
;; function call
        (
          (consume-token state :lparen) 
          (let 
            (
              (args 
                (parse-argument-list state))) 
            (expect-token state :rparen) 
            (setf expr 
              (mo "function call" :av "name" expr :av "arguments" arguments)))) 
;; struct access
        (
          (consume-token state :dot) 
          (let 
            (
              (struct 
                (expect-token state :identifier))) 
            (setf expr 
              (mo "struct access" :av "object" expr :av "member" (token-value struct))))) 
;; array access
        (
          (consume-token state :lbracket) 
          (let 
            (
              (index 
                (parse-expression state))) 
            (expect-token state :rbracket) 
            (setf expr 
              (mo "array access" :av "array" expr :av "index" index)))) (t (return expr)))))) 

(defun parse-primary-expression (state) 
  (or 
    (parse-constant state) 
    (when 
      (match-token state :identifier) 
      (parse-identifier-expression state)) 
    (when 
      (match-token state :lparen) 
      (parse-parenthesized-expression state)) 
    (parse-temporal-expression state) 
    (parse-quantified-expression state) 
    (parser-error (current-token state) "Expected primary expression"))) 


(defun unary-operator-p (token) 
  (and token 
    (eq (token-type token) :operator) 
    (member (token-value token) '("+" "-" "!") :test #'string=))) 

(defun parse-unary-expression (state) 
  (let 
    (
      (token (current-token state))) 
    (if 
      (unary-operator-p token) 
      (progn (advance state) 
        (mo "unary expression" :av "operator" (token-value token) :av "operand" 
          (parse-unary-expression state))) 
      (parse-postfix-expression state)))) 


(defparameter *binary-precedence* '(("<=>" . 1) ("==>" . 2) ("||" . 3) ("&&" . 4) ("=" . 5) ("!=" . 5) ("<" . 6) ("<=" . 6) (">" . 6) (">=" . 6) ("+" . 7) ("-" . 7) ("*" . 8) ("/" . 8) ("%" . 8) ("<<" . 9) (">>" . 9) ("&" . 10) ("|" . 10) ("^" . 10))) 

(defun binary-precedence (operator) 
  (cdr 
    (assoc operator *binary-precedence* :test #'string=))) 

(defun parse-binary-expression 
  (state &optional (min-precedence 0)) 
  (let 
    (
      (left 
        (parse-unary-expression state))) 
    (loop for token = (current-token state) for precedence = 
      (and token 
        (eq (token-type token) :operator) 
        (binary-precedence (token-value token))) while 
      (and precedence 
        (>= precedence min-precedence)) do (advance state) 
      (let* 
        (
          (operator (token-value token)) 
          (right 
            (parse-binary-expression state (1+ precedence)))) 
        (setf left 
          (mo "binary expression" :av "operator" operator :av "left" left :av "right" right)))) left)) 

(defun parse-expression (state) 
  (parse-binary-expression state)) 

(defun temporal-keyword-p (token) 
  (and token 
    (eq (token-type token) :keyword) 
    (member (token-value token) '("previously" "next" "once" "during") :test #'string=))) 

(defun parse-temporal-expression (state) 
  (let 
    (
      (token (current-token state))) 
    (when 
      (temporal-keyword-p token) (advance state) 
      (expect-token state :lparen) 
      (let 
        (
          (args 
            (parse-argument-list state))) 
        (expect-token state :rparen) 
        (mo (token-value token) :av "arguments" arguments))))) 


(defun parse-domain-expression (state) 
  (when 
    (consume-token state :keyword "in") 
    (let 
      (
        (expr 
          (parse-expression state))) 
      (mo "collection domain" :av "expression" 
        (parse-expression state))))) 

(defun parse-quantified-variable (state) 
  (let 
    (
      (type (parse-type state)) 
      (name-token 
        (expect-token state :identifier))) 
    (mo "quantified variable" :av "type" type :av "name" 
      (token-value name-token) :av "domain" 
      (parse-domain-expression state)))) 

(defun parse-quantified-expression (state) 
  (let 
    (
      (token (current-token state))) 
    (when 
      (and 
        (match-token state :keyword) 
        (member (token-value token) '("forall" "exists") :test #'string=)) (advance state) 
    (expect-token state :lparen) 
    (let ((variables '())) 
    (push 
      (parse-quantified-variable state) variables) 
    (loop while 
      (consume-token state :comma) do 
      (push 
        (parse-quantified-variable state) variables)) 
    (expect-token state :rparen) 
    (let 
      (
        (body 
          (parse-expression state))) 
      (mo "quantified expression" :av "quantifier" (token-value token) :av "variables" (nreverse variables) :av "body" body)))))) 


(defun parse-parameter (state) 
  (let 
    (
      (type (parse-type state)) 
      (name-token 
        (expect-token state :identifier))) 
    (mo "parameter" :av "type" type :av "name" 
      (token-value name-token)))) 

(defun parse-parameter-list (state) 
  (let ((params '())) 
  (unless 
    (match-token state :rparen) 
    (push 
      (parse-parameter state) params) 
    (loop while 
      (consume-token state :comma) do 
      (push 
        (parse-parameter state) params))) (nreverse params))) 


(defun parse-variable-definition (state type name) 
  (expect-token state :operator "=") 
  (mo "variable definition" :av "type" type :av "name" name :av "expression" 
    (parse-expression state))) 

(defun parse-function-definition (state type name) 
  (expect-token state :lparen) 
  (let 
    (
      (params 
        (parse-parameter-list state))) 
    (expect-token state :rparen) 
    (expect-token state :operator "=") 
    (mo "function definition" :av "type" type :av "name" name :av "parameters" parameters :av "expression" 
      (parse-expression state)))) 

(defun parse-definition (state) 
  (let 
    (
      (type (parse-type state)) 
      (name-token 
        (expect-token state :identifier))) 
    (let 
      (
        (name 
          (token-value name-token))) 
      (cond 
        (
          (match-token state :lparen) 
          (parse-function-definition state type name)) 
        (
          (match-token state :operator "=") 
          (parse-variable-definition state type name)) 
        (t 
          (parser-error (current-token state) "Expected function or variable definition")))))) 

(defun parse-definition-list (state) 
  (let ((definitions '())) 
  (loop while 
    (or 
      (match-token state :identifier) 
      (match-token state :keyword)) do 
    (push 
      (parse-definition state) definitions) 
    (consume-token state :semicolon)) 
  (nreverse definitions))) 

(defun annotation-keyword-p (token) 
  (and token 
    (eq (token-type token) :keyword) 
    (member (token-value token) '("assume" "assert" "invariant" "define") :test #'string=))) 

(defun parse-annotation (state) 
  (expect-token state :lbracket) 
  (let* 
    (
      (kind-token 
        (expect-token state :keyword)) 
      (kind 
        (token-value kind-token)) (language nil)) 
;; optional language
    (when 
      (consume-token state :lparen) 
      (let 
        (
          (lang-token 
            (expect-token state :identifier))) 
        (setf language 
          (token-value lang-token))) 
      (expect-token state :rparen)) 
    (expect-token state :colon) 
    (let 
      (
        (body 
          (if 
            (string= kind "define") 
            (parse-definition-list state) 
            (parse-expression state)))) 
      (expect-token state :rbracket) 
      (mo "annotation" :av "kind" kind :av "language" language :av "body" body)))) 

(defun parse-annotation-block-from-state (state) 
  (let ((annotations '())) 
  (loop until 
    (match-token state :eof) do 
    (push 
      (parse-annotation state) annotations)) 
  (mo "annotation block" :av "annotations" 
    (nreverse annotations)))) 


(defun parse-annotation-block (source) 
  (let* 
    ((tokens (lex source)) 
      (state 
        (make-parser-state :tokens tokens))) 
    (parse-annotation-block-from-state state)))