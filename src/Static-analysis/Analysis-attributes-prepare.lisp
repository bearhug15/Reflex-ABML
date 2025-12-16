(uiop:define-package Reflex-semantics
  (:use #:cl))
(in-package #:Reflex-semantics)


(mot "analysis env"
    :at "agents" (listt "analysis agent")
    :at "aclosures" (cot :amap "agent" (listt cot)))
    :at "process state names" (cot :amap "process name" (listt "state name"))

(mot "analysis agent"
    :at "current process" "process name"
    :at "current state" "state name"

    :at "collector" (listt "attributes")

    :at "value" "attributes")

(mot "attributes"
    :at "process change" (mot :amap "process name" (enumt 'start 'stop 'error))
    :at "pot process change" (listt (mot :at "process" "process name" :at "change" (enumt 'start 'stop 'error)))
    :at "reset" bool 
    :at "state changed" bool 
    :at "reach from" (listt "state name")
    :at "changes to" (listt "state name"))



(aclosure c :attribute "attributes prepare" :type "reset timer"
    :do (mo "attributes" :av "reset" t))

(aclosure c :attribute "attributes prepare" :type "set state"
    :instance i
    :agent a
    :env env 
    :ap i "state" state
    :do (mo "attributes" 
            :av "reset" t
            :av "changes to" 
                (if (null state)
                    (list (next-process-state agent env))
                    (list state)))
)

(aclosure c :attribute "attribute prepare" :type "restart process"
    :instance i
    :ap (aseq "agent" "current process") cur-proc
    :ap (aseq "agent" "current state") cur-state
    :p (first-state (aget c "env") cur-proc) fstate
    :p (= fstate cur-state) cur-fstate 
    :do (mo "attributes"
            :av "process change" (mo cur-proc 'start)
            :av "pot process change" (list (co :av "process" cur-proc :av "change" 'start))
            :av "reset" t
            :av "changes to" (if (not cur-fstate) (list fstate))
            :av "state changed" (not cur-fstate))
)
(aclosure c :attribute "attribute prepare" :type "start process"
    :instance i
    :ap i "process" process 
    :ap (aseq "agent" "current process") cur-proc
    :ap (aseq "agent" "current state") cur-state
    :p (first-state (aget c "env") cur-proc) fstate
    :p (= fstate cur-state) cur-fstate 
    :do (if (= process cur-proc)
            (eval-aclosure c :av "instance" (mo "restart process"))
            (mo "attributes"
                :av "process change" (mo :av process 'start)
                :av "pot process change" (list (co :av "process" process :av "change" 'start))))
    
)
(aclosure c :attribute "attribute prepare" :type "stop current process"
    :instance i 
    :ap (aseq "agent" "current process") cur-proc
    :ap (aseq "agent" "current state") cur-state
    :do (mo "attributes"
            :av "process change" (mo :av cur-proc 'stop)
            :av "pot process change" (list (co :av "process" cur-proc :av "change" 'stop))
            :av "reset" t
            :av "changes to" (list "stop")
            :av "state changed" t)
)
(aclosure c :attribute "attribute prepare" :type "stop process"
    :instance i
    :ap i "process" process 
    :ap (aseq "agent" "current process") cur-proc
    :ap (aseq "agent" "current state") cur-state
    :do (if (= process cur-proc)
            (eval-aclosure c :av "instance" (mo "stop current process"))
            (mo "attributes"
                :av "process change" (mo :av process 'stop)
                :av "pot process change" (list (co :av "process" process :av "change" 'stop))))
)
(aclosure c :attribute "attribute prepare" :type "error current process"
    :instance i 
    :ap (aseq "agent" "current process") cur-proc
    :ap (aseq "agent" "current state") cur-state
    :do (mo "attributes"
            :av "process change" (mo :av cur-proc 'error)
            :av "pot process change" (list (co :av "process" cur-proc :av "change" 'error))
            :av "reset" t
            :av "changes to" (list "error")
            :av "state changed" t)    
)
(aclosure c :attribute "attribute prepare" :type "error process"
    :instance i
    :ap i "process" process 
    :ap (aseq "agent" "current process") cur-proc
    :ap (aseq "agent" "current state") cur-state
    :do (if (= process cur-proc)
            (update-eval-aclosure c :av "instance" (mo "error current process"))
            (mo "attributes"
                :av "process change" (mo :av process 'error)
                :av "pot process change" (list (co :av "process" process :av "change" 'error))))
)

(aclosure c :attribute "attribute prepare" :type "statement list" :stage nil
    :instance i 
    :do (push-aclosure (aset c :av "stage" 'rest :av "rest" (cdr i) :av "collected attr" (mo "attributes")))
        (eval-aclosure (aset (clear-aclosure c) :av "instance" (car i)))
)
(aclosure c :attribute "attribute prepare" :type "statement list" :stage 'rest
    :instance i 
    :ap "rest" rst
    :ap "agent" a  
    :ap "collected attr" cattr
    :value val
    :do (if rst 
            (progn (add-cons-attributes cattr val)
                (push-aclosure (aset c :av "stage" 'rest :av "rest" (cdr i) ))
                (eval-aclosure (aset (clear-aclosure c) :av "instance" (car i))))
            (add-cons-attributes cattr val))
)

(aclosure c :attribute "attributes prepare" :type "timeout statement" :stage
    :instance i 
    :ap i "statements" sts
    :do (update-push-aclosure c :av "stage" 'sts )
        (clear-update-eval-aclosure c :av "instance" sts)
)
(aclosure c :attribute "attributes prepare" :type "timeout statement" :stage
    :instance i 
    :value val 
    :p (add-par-attributes-conc (add-par-attributes (mo "attributes") val)) res 
    :do (aset i "analysis attributes" res)
        res
)
#|
(mot "wait" :at "condition" "expression")
(mot "slice")
(mot "transition" :at "condition" "expression")
(mot "barrier statement" (uniont "wait" "slice" "transition"))
|#

(aclosure c :attribute "attributes prepare" :type "if then statement" :stage nil
    :instance i 
    :ap i "then" sts
    :do (update-push-aclosure c :av "stage" 'then)
        (clear-update-eval-aclosure c :av "instance" sts)
)
(aclosure c :attribute "attributes prepare" :type "if then statement" :stage 'then
    :instance i
    :value val 
    :p (add-par-attributes-conc (add-par-attributes (mo "attributes") val)) res
    :do (aset i "analysis attributes" res)
        res
)
(aclosure c :attribute "attributes prepare" :type "if then else statement" :stage nil 
    :instance i 
    :ap i "then" sts
    :do (update-push-aclosure c :av "stage" 'then)
        (clear-update-eval-aclosure c :av "instance" sts)
)
(aclosure c :attribute "attributes prepare" :type "if then else statement" :stage 'then 
    :instance i
    :value val 
    :ap i "else" sts
    :do (update-push-aclosure c :av "stage" 'else :av "then" val)
        (clear-update-eval-aclosure c :av "instance" sts)
)
(aclosure c :attribute "attributes prepare" :type "if then else statement" :stage 'then 
    :instance i
    :value val 
    :ap "then" then
    :p (add-par-attributes-conc (add-par-attributes then val)) res
    :do (aset i "analysis attributes" res)
        res
)

(aclosure c :attribute "attribute prepare" :type "switch statement" :stage nil 
    :instance i 
    :ap i "cases" css 
    :do (update-push-aclosure c :av "stage" 'conclude)
        (update-push-aclosure c :av "stage" 'default)
        (if css
            (update-push-aclosure c :av "stage" 'cases-label :av "cases" css))
)
(aclosure c :attribute "attribute prepare" :type "switch statement" :stage 'cases-label 
    :instance i 
    :ap "cases" css 
    :do (if css 
            (progn 
                (update-push-aclosure c :av "stage" 'case-label :av "cases" (cdr css))
                (update-push-aclosure c :av "stage" 'case-iter-true :av "cases")
                (clear-update-eval-aclosure c :av "instance" (car css))
                )
            (update-push-aclosure c :av "stage" 'default))
)
(aclosure c :attribute "attribute prepare" :type "switch statement" :stage 'case-iter-true 
    :instance i 
    :ap "cases" css
    :p (car css) cs
    :value val 
    :do (if (aget cs "break")
            (cons-to-inner-list c (list "agent" "collector") val)
            (progn (update-push-aclosure c :av "stage" 'cont-case-iter :av "css" (cdr css) :av "current" (list val))
                (clear-update-eval-aclosure c :av "instance" (car (cdr css)))))
)
(aclosure c :attribute "attribute prepare" :type "switch statement" :stage 'cont-case-iter  
    :instance i 
    :ap "cases" css 
    :p (car css) cs 
    :value val
    :ap "current" current 
    :do (if css
            (if (aget cs "break")
                (cons-to-inner-list c (list "agent" "collector") (cons-attributes (reverse (cons val current))))
                (progn (update-push-aclosure c :av "stage" 'cont-case-iter :av "css" (cdr css) :av "current" (cons val current))
                    (clear-update-eval-aclosure c :av "instance" (car (cdr css)))))
            (update-push-aclosure c :av "stage" 'default))
)
(aclosure c :attribute "attribute prepare" :type "switch statement" :stage 'default
    :instance i 
    :value val
    :ap i "default" default
    :ap "current" current 
    :do (if default
            (progn (update-push-aclosure c :av "stage" 'default-conc)
                (clear-update-eval-aclosure c :av "instance" default))
            (cons-to-inner-list c (list "agent" "collector") (cons-attributes (reverse current))))
)    
(aclosure c :attribute "attribute prepare" :type "switch statement" :stage 'default-conc
    :instance i 
    :value val
    :ap "current" current 
    :do (cons-to-inner-list c (list "agent" "collector") (cons-attributes (reverse (cons val current))))
)
(aclosure c :attribute "attribute prepare" :type "switch statement" :stage 'conclude
    :instance i 
    :agent a
    :ap a "collector" coll
    :p (par-attributes coll) par-attr
    :value val
    :do (aset a "collector" nil)
        (aset i "analysis attributes" par-attr)
        par-attr 
)



(aclosure c :attribute "attributes prepare" :type "default statement" 
    :instance i 
    :ap i "statements" sts
    :do (eval-aclosure (aset (clear-aclosure c) :av "instance" sts))     
)

(aclosure c :attribute "attributes prepare" :type "case statement" 
    :instance i 
    :ap i "statements" sts
    :do (eval-aclosure (aset (clear-aclosure c) :av "instance" sts))     
)
(aclosure c :attribute "attributes prepare" :type "statement block" 
    :instance i 
    :ap i "statements" sts
    :do (eval-aclosure (aset (clear-aclosure c) :av "instance" sts))     
)


;Declarations

(aclosure c :attribute "attribute prepare" :type "state declaration" :stage nil
    :instance i 
    :ap i "statements" sts
    :do (update-push-aclosure c :av "stage" 'next)
        (clear-update-eval-aclosure c :av "instance" sts)
)
(aclosure c :attribute "attribute prepare" :type "state declaration" :stage 'next
    :instance i 
    :value val
    :do (aset i "analysis attributes" val)
        val
)

(aclosure c :attribute "attribute prepare" :type "process declaration" :stage nil
    :instance i
    :ap i "states" states
    :do (update-push-aclosure c :av "stage" 'states :av "states" states)
)
(aclosure c :attribute "attribute prepare" :type "process declaration" :stage nil
    :instance i
    :ap "states" states
    (if states 
            (progn (update-push-aclosure c :av "states" (cdr states))
                (clear-update-eval-aclosure c :av "instance" (car states)))
            (update-push-aclosure c :av "stage" 'proc-eval))
)

(aclosure c :attribute "attribute prepare" :type "process declaration" :stage nil
    :instance i 
    :ap i "states" states
    :p (par-attributes (mapcar (lambda (state) (aget state "analysis attributes")) states)) proc-attr
    :do (aset i "analysis attributes" proc-attr)
)

(aclosure c :attribute "attribute prepare" :type "program declaration" :stage nil
    :instance i 
    :p (aget i "processes") procs 
    :do (update-push-aclosure c :av "stage" 'procs :av "procs" procs)
)
(aclosure c :attribute "attribute prepare" :type "program declaration" :stage 'procs
    :instance i 
    :ap "procs" procs
    :do (if states 
            (progn (update-push-aclosure c :av "procs" (cdr procs))
                (clear-update-eval-aclosure c :av "instance" (car procs)))
            (update-push-aclosure c :av "stage" 'prog-eval))
)
(aclosure c :attribute "attribute prepare" :type "program declaration" :stage 'prog-eval
    :instance i 
    :ap i "processes" procs
    :p (reverse procs) rev-procs
    :p (car (aget i "processes")) first-proc
    :do (aset first-proc (aseq "analysis attributes" "startS") nil)
        (mapc 
            (lambda (proc) 
                (if (exists-p1-with-p2-tail
                        (cdr (member proc rev-procs))
                        (lambda (oproc)
                            (and (not (aget oproc "startS"))
                                (= (aget oproc (aseq "analysis attributes" "process change" (aget proс "name"))) "start")))
                        (lambda (oproc)
                            (not (let ((potProcChange (aget oproc (aseq "stat" 0 "analysis attributes" "pot process change"))))
                                    (find-if
                                        (lambda (change) (and (= (aget change "process") (aget proc "name"))
                                                            (or (= (aget change "change") 'stop) (= (aget change "change") 'error))))
                                        potProcChange)))))
    
                    (aset proc (aseq "analysis attributes" "startS") nil)))
            procs)
)