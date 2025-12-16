(uiop:define-package Reflex-semantics
  (:use #:cl))
(in-package #:Reflex-semantics)

(defun group-static-analysis (closure term)
    (cond
        ((= (get-mode closure) 'prepare) (group-static-analysis-prepare closure)) 
        ((= (get-mode closure) 'work) (group-static-analysis-work closure term))))

(att "attributes" :at "group" int)

(defun setsInter (sets-set proc-set)
    (reduce 
        (lambda (coll el)
            (let ((inter (intersection el proc-set :test #'string=)))
                (union (set-difference el inter :test #'string=) (union inter coll))))
        sets-set
        :initial-value nil))

(defun object-union (obj1 obj2)
    (reduce (coll at)
        (aset coll at (aget obj2 at)) 
        (attributes obj2)
        :initial-value obj1))

(defun proc-id (env proc-name)
    (aget env (aseq "process id" proc-name)))

(defun sets-div (closure sets-set hpc procChange)
    (let* ((agent (aget closure "agent"))
            (env (aget closure "env"))
            (current-process (aget agent "current process"))
            (current-state (aget agent "current state"))
            (nhpc (object-union (iclone procChange) hpc))
            (startPpred (remove-if-not 
                            (lambda (proc) (and (< (proc-id env proc) (proc-id env current-process))
                                                (equal (aget nhpc proc) 'start)))
                            (attributes nhpc)))
            (startPsucc (remove-if-not 
                            (lambda (proc) 
                                (and (or (> (proc-id env proc) (proc-id env current-process))
                                        (and (= (proc-id env proc) (proc-id env current-process))
                                            (equal current-state (first-state env current-process))))
                                    (equal (aget nhpc proc) 'start)))
                            (attributes nhpc)))
            (stopPpred (remove-if-not 
                            (lambda (proc) (and (< (proc-id env proc) (proc-id env current-process))
                                                (equal (aget nhpc proc) 'stop)))
                            (attributes nhpc)))
            (stopPsucc (remove-if-not 
                            (lambda (proc) 
                                (and (> (proc-id env proc) (proc-id env current-process))
                                    (equal (aget nhpc proc) 'stop)))
                            (attributes nhpc)))
            (errorPpred (remove-if-not 
                            (lambda (proc) (and (< (proc-id env proc) (proc-id env current-process))
                                                (equal (aget nhpc proc) 'error)))
                            (attributes nhpc)))
            (errorPsucc (remove-if-not 
                            (lambda (proc) 
                                (and (> (proc-id env proc) (proc-id env current-process))
                                    (equal (aget nhpc proc) 'error)))
                            (attributes nhpc))))
        (list nhpc (reduce 
            (lambda (coll el)
                (setsInter coll el))
            (list startPpred startPsucc stopPpred stopPsucc errorPpred errorPsucc)
            :initial-value sets-set))
    )
)

(defun group-static-analysis-prepare (closure)
    (let* ((program (aget closure "instance")))
            (procs (aget program "processes"))
        (mapc 
            (lambda (proc) (aset proc (aseq "analysis attributes" "group") (uid proc)))
            procs)
        (eval-aclosure closure :av "attribute" "sets div" :av "hpc" (mo) :av "sets set" 
            (list
                (mapcar (lambda (proc) (aget proc "name")) (remove-if (lambda (proc) (aget proc (aseq "analysis attributes" "startS"))) procs))
                (mapcar (lambda (proc) (aget proc "name")) (remove-if-not (lambda (proc) (aget proc (aseq "analysis attributes" "startS"))) procs))))
        (let ((sets-set (aget closure (aseq "agent" "value"))))
            (loop for group in sets-set
                for index from 0
                do (mapc 
                        (lambda (gel)
                            (mapc 
                                (lambda (proc) (if (equal gel (aget proc "name")) (aset proc (aseq "analysis attributes" "group") index))) 
                                procs))
                        group))))
        
)

(mot "sets env"
    :at "agents" (listt "sets agent")
    :at "aclosures" (cot :amap "agent" (listt cot)))
    :at "process state names" (cot :amap "process name" (listt "state name")
    :at "process id" (cot :amap "process name" int)
    )

(mot "sets agent"
    :at "current process" "process name"
    :at "current state" "state name"

    ;return sets-set
    :at "value" any)

(aclosure c "sets div" "reset timer" 
    :instance i
    :agent a
    :ap "sets set" sets-set
    :ap "hpc" hpc
    :p (aget i (aseq "analysis attributes" "procChange")) procChange
    :do (sets-div c sets-set hpc procChnage))

(aclosure c "sets div" "set state" 
    :instance i
    :agent a
    :ap "sets set" sets-set
    :ap "hpc" hpc
    :p (aget i (aseq "analysis attributes" "procChange")) procChange
    :do (sets-div c sets-set hpc procChnage))

(aclosure c "sets div" "restart process" 
    :instance i
    :agent a
    :ap "sets set" sets-set
    :ap "hpc" hpc
    :p (aget i (aseq "analysis attributes" "procChange")) procChange
    :do (sets-div c sets-set hpc procChnage))

(aclosure c "sets div" "start process" 
    :instance i
    :agent a
    :ap "sets set" sets-set
    :ap "hpc" hpc
    :p (aget i (aseq "analysis attributes" "procChange")) procChange
    :do (sets-div c sets-set hpc procChnage))

(aclosure c "sets div" "stop current process" 
    :instance i
    :agent a
    :ap "sets set" sets-set
    :ap "hpc" hpc
    :p (aget i (aseq "analysis attributes" "procChange")) procChange
    :do (sets-div c sets-set hpc procChnage))

(aclosure c "sets div" "stop process" 
    :instance i
    :agent a
    :ap "sets set" sets-set
    :ap "hpc" hpc
    :p (aget i (aseq "analysis attributes" "procChange")) procChange
    :do (sets-div c sets-set hpc procChnage))

(aclosure c "sets div" "error current process" 
    :instance i
    :agent a
    :ap "sets set" sets-set
    :ap "hpc" hpc
    :p (aget i (aseq "analysis attributes" "procChange")) procChange
    :do (sets-div c sets-set hpc procChnage))

(aclosure c "sets div" "error process" 
    :instance i
    :agent a
    :ap "sets set" sets-set
    :ap "hpc" hpc
    :p (aget i (aseq "analysis attributes" "procChange")) procChange
    :do (sets-div c sets-set hpc procChnage))

(aclosure c "sets div" "statement list" :stage nil
    :instance i
    :ap "sets set" sets-set
    :ap "hpc" hpc
    :do (update-push-aclosure c :av "stage" 'rest :av "rest" (cdr i))
        (update-eval-aclosure c :av "instance" (car i))
)    
(aclosure c "sets div" "statement list" :stage 'rest
    :instance i
    :ap "sets set" sets-set
    :ap "hpc" hpc
    :ap "rest" rst
    :value val
    :do (if rst
            (progn (update-push-aclosure c :av "stage" 'sts :av "rest" (cdr rst))
                (update-eval-aclosure c :av "instance" (car rst) :av "sets set" (second val)))
            val)
)

(aclosure c "sets div" "timeout statement"
    :instance i
    :agent a
    :ap "sets set" sets-set
    :ap "hpc" hpc
    :p (sets-div c sets-set hpc procChnage) new-hpc-sets
    :do (update-eval-aclosure c :av "instance" (aget i "statements") :av "hpc" (first new-hpc-sets) :av "sets set" (second new-hpc-sets))
)

;(mot "wait" :at "condition" "expression")
;(mot "slice")
;(mot "transition" :at "condition" "expression")
;(mot "transition on timeout" :at "condition" "expression" :at "controlling expression" "time amount or ref" :at "statements" "statement list")
;(mot "barrier statement" (uniont "wait" "slice" "transition" "transition on timeout"))
(aclosure c "sets div" "if then statement"
    :instance i
    :agent a
    :ap "sets set" sets-set
    :ap "hpc" hpc
    :p (sets-div c sets-set hpc procChnage) new-hpc-sets
    :do (update-eval-aclosure c :av "instance" (aget i "then") :av "hpc" (first new-hpc-sets) :av "sets set" (second new-hpc-sets))

)

(aclosure c "sets div" "if then else statement" :stage nil
    :instance i
    :agent a
    :ap "sets set" sets-set
    :ap "hpc" hpc
    :p (sets-div c sets-set hpc procChnage) new-hpc-sets
    :do (update-push-aclosure c :av "stage" 'else :av "hpc" (first new-hpc-sets))
        (update-eval-aclosure c :av "instance" (aget i "then") :av "hpc" (first new-hpc-sets) :av "sets set" (second new-hpc-sets))
)
(aclosure c "sets div" "if then else statement" :stage 'else
    :instance i
    :agent a
    :ap "hpc" hpc
    :value val
    :do (update-eval-aclosure c :av "instance" (aget i "else") :av "hpc" hpc :av "sets set" val)
)

;Предполагается что была проведена нормализация
(aclosure c "sets div" "switch statement" :stage nil
    :instance i
    :agent a
    :ap "sets set" sets-set
    :ap "hpc" hpc
    :p (sets-div c sets-set hpc procChnage) new-hpc-sets
    :do (update-push-aclosure c :av "stage" 'rest :av "hpc" (first new-hpc-sets) :av "rest" (cdr (aget i "cases")))
        (update-eval-aclosure c :av "instance" (car (aget i "cases")) :av "hpc" (first new-hpc-sets) :av "sets set" (second new-hpc-sets))
)
(aclosure c "sets div" "switch statement" :stage 'rest
    :instance i
    :agent a
    :ap "sets set" sets-set
    :ap "hpc" hpc
    :ap "rest" rst
    :value val 
    :do (if rst 
            (progn (update-push-aclosure c :av "rest" (cdr rst))
                (update-eval-aclosure c :av "instance" (car rst) :av "sets set" val))
            (if (aget i "default")
                (update-eval-aclosure c :av "instance" (aget i "default") :av "sets set" val)
                val))
)

(aclosure c "sets div" "case statement"
    :instance i
    :agent a
    :ap "sets set" sets-set
    :ap "hpc" hpc
    :p (sets-div c sets-set hpc procChnage) new-hpc-sets
    :do (update-eval-aclosure c :av "instance" (aget i "statements") :av "hpc" (first new-hpc-sets) :av "sets set" (second new-hpc-sets))
)
(aclosure c "sets div" "default statement"
    :instance i
    :agent a
    :ap "sets set" sets-set
    :ap "hpc" hpc
    :p (sets-div c sets-set hpc procChnage) new-hpc-sets
    :do (update-eval-aclosure c :av "instance" (aget i "statements") :av "hpc" (first new-hpc-sets) :av "sets set" (second new-hpc-sets))
)
(aclosure c "sets div" "statement block"
    :instance i
    :agent a
    :ap "sets set" sets-set
    :ap "hpc" hpc
    :p (sets-div c sets-set hpc procChnage) new-hpc-sets
    :do (update-eval-aclosure c :av "instance" (aget i "statements") :av "hpc" (first new-hpc-sets) :av "sets set" (second new-hpc-sets))
)

(aclosure c "sets div" "expression statement"
    :instance i
    :agent a
    :ap "sets set" sets-set
    :ap "hpc" hpc
    :do sets-set
)

(aclosure c "sets div" "state declaration"
    :instance i
    :agent a
    :ap "sets set" sets-set
    :ap "hpc" hpc
    :do (aset agent "current state" (aget i "name"))
        (let ((new-hpc-sets (sets-div c sets-set hpc procChnage)))
            (update-eval-aclosure c :av "instance" (aget i "statements") :av "hpc" (first new-hpc-sets) :av "sets set" (second new-hpc-sets)))
)

(aclosure c "sets div" "process declaration" :stage nil
    :instance i
    :agent a
    :ap "sets set" sets-set
    :ap "hpc" hpc
    :do (aset agent "current process" (aget i "name"))
        (let ((new-hpc-sets (sets-div c sets-set hpc procChnage)))
            (update-push-aclosure c :av "stage" 'rest :av "hpc" (first new-hpc-sets) :av "rest" (cdr (aget i "states")))
            (update-eval-aclosure c :av "instance" (car (aget i "states")) :av "hpc" (first new-hpc-sets) :av "sets set" (second new-hpc-sets)))
)
(aclosure c "sets div" "process declaration" :stage 'rest
    :instance i
    :agent a
    :ap "sets set" sets-set
    :ap "hpc" hpc
    :ap "rest" rst
    :value val 
    :do (if rst 
            (progn (update-push-aclosure c :av "rest" (cdr rst))
                (update-eval-aclosure c :av "instance" (car rst) :av "sets set" val))
            val)
)

(aclosure c "sets div" "program declaration" :stage nil
    :instance i
    :agent a
    :ap "sets set" sets-set
    :ap "hpc" hpc
    :do (let ((new-hpc-sets (sets-div c sets-set hpc procChnage)))
            (update-push-aclosure c :av "stage" 'rest :av "hpc" (first new-hpc-sets) :av "rest" (cdr (aget i "processes")))
            (update-eval-aclosure c :av "instance" (car (aget i "processes")) :av "hpc" (first new-hpc-sets) :av "sets set" (second new-hpc-sets)))
)
(aclosure c "sets div" "program declaration" :stage 'rest
    :instance i
    :agent a
    :ap "sets set" sets-set
    :ap "hpc" hpc
    :ap "rest" rst
    :value val 
    :do (if rst 
            (progn (update-push-aclosure c :av "rest" (cdr rst))
                (update-eval-aclosure c :av "instance" (car rst) :av "sets set" val))
            val)
)

(defun group-static-analysis-work (closure term)
    (let* ((env (aget closure "env"))
            (agent (aget closure "agent"))
			(current-process (aget agent "current process"))
			(cur-first-state (first-state env current-process))
            (rev-cur-cond (aget agent "cur cond"))
			(cur-cond (reverse rev-cur-cond)))
        (cond 
			((is-instance term "pstate compare")
				(not (or (check-rule-1 env term cur-cond current-process)
						(check-rule-2 env term cur-cond current-process)
                        (check-rule-3 agent env term cur-cond current-process)
                        (check-rule-4 agent env term cur-cond current-process)
					)
				)
			)
        )
	))

(defun get-proc-group (env proc-name)
    (let ((procs (aget env (aseq "program" "processes")))
            (find-if 
                (lambda (proc) 
                    (if (= proc-name (aget proc "name"))
                        (aget proc (aseq "analysis attributes" "group"))
                        nil))
                procs))))

(defun get-proc (env proc-name)
    (let ((procs (aget env (aseq "program" "processes")))
            (find-if 
                (lambda (proc) 
                    (if (= proc-name (aget proc "name"))
                        proc
                        nil))
                procs))))

(defun check-rule-1 (env term cur-cond current-process)
    (let ((procs (aget env (aseq "program" "processes")))
            (cur-proc (get-proc env current-process)))
        (find-if 
            (lambda (formula)
                (if (is-instance formula "pstate compare")
                    (let ((other-proc-name (aget formula "process")))
                        (find-if
                            (lambda (other-proc)
                                (and (not (equal current-process other-proc-name)) 
                                    (= (get-proc-group env other-proc-name) (get-proc-group env current-process))
                                    (not (equal (equal (aget term "change") 'stop) 
                                                (equal (aget formula "change") 'stop)))))
                            procs))
                    nil))
            cur-cond)))

(defun check-rule-2 (env term cur-cond current-process)
    (let ((procs (aget env (aseq "program" "processes")))
            (cur-proc (get-proc env current-process)))
        (find-if 
            (lambda (formula)
                (if (is-instance formula "pstate compare")
                    (let ((other-proc-name (aget formula "process")))
                        (find-if
                            (lambda (other-proc)
                                (and (not (equal current-process other-proc-name)) 
                                    (= (get-proc-group env other-proc-name) (get-proc-group env current-process))
                                    (not (equal (equal (aget term "change") 'error) 
                                                (equal (aget formula "change") 'error)))))
                            procs))
                    nil))
            cur-cond)))

(defun check-rule-3 (agent env term cur-cond current-process)
    (let ((cur-state-name (aget agent "current state"))
            (procs (aget env (aseq "program" "processes")))
            (cur-proc (get-proc env current-process)))
        (find-if 
            (lambda (formula)
                (if (is-instance formula "pstate compare")
                    (let ((other-proc-name (aget formula "process")))
                        (find-if
                            (lambda (other-proc)
                                (and (not (equal current-process other-proc-name)) 
                                    (= (get-proc-group env other-proc-name) (get-proc-group env current-process))
                                    (null (aget (car (aget cur-proc "states")) (aseq "analysis attributes" "reach from")))
                                    (equal (aget (car (aget cur-proc "states")) "name") cur-state-name)
                                    (aget (car (aget cur-proc "states")) (aseq "analysis attributes" "state changed"))
                                    (equal (aget (car (aget other-proc "states")) "name") other-proc-name)))
                            procs))
                    nil))
            cur-cond)))

(defun check-rule-4 (agent env term cur-cond current-process)
    (let ((cur-state-name (aget agent "current state"))
            (procs (aget env (aseq "program" "processes")))
            (cur-proc (get-proc env current-process)))
        (find-if 
            (lambda (formula)
                (if (is-instance formula "pstate compare")
                    (let ((other-proc-name (aget formula "process")))
                        (find-if
                            (lambda (other-proc)
                                (and (not (equal current-process other-proc-name)) 
                                    (= (get-proc-group env other-proc-name) (get-proc-group env current-process))
                                    (null (aget (car (aget other-proc "states")) (aseq "analysis attributes" "reach from")))
                                    (equal (aget (car (aget other-proc "states")) "name") (aget formula "pstate"))
                                    (aget (car (aget other-proc "states")) (aseq "analysis attributes" "state changed"))
                                    (equal (aget (car (aget cur-proc "states")) "name") current-process)))
                            procs))
                    nil))
            cur-cond)))