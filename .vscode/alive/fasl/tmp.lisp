(uiop:define-package Reflex-semantics
  (:use #:cl))
(in-package #:Reflex-semantics)

(defun next-process-state (a env)
	(let* ((current-process (aget a "current process"))
            (current-state (aget a "current state"))
            (lst (member (aget env (aseq "process states names" current-process)) current-state)))
        (if (or (not lst) (= (length lst) 1))
            nil
            (car (cdr lst))))
)

(defun first-state (env process)
    (car (aget env (aseq "process states names" process))))

(mot "env"
    :at "agents" (listt "agent")
    :at "aclosures" (cot :amap "agent" (listt (cot)))

    :at "process states names" (cot :amap "process name" (listt "state name"))
)

(mot "agent"
    :at "current process" "process name"
    :at "current state" "state name"
    :at "next state" "state name"
    :at "new states" "state declaration"
    :atv "slice counter" int 0
    :atv "transition counter" int 0
    
    :at "value" any)

(aclosure "simplify program" "set state" i c 
    (match :av i "state" nil :p (aget c (aseq "agent" "next state")) next-state
        :do (aset i "state" next-state)))

(defun create-light-state (state-name state-type num)
    (concatenate state-name "_" state-type "_" num))

(defun break-into-states-sub (st-list coll cur-coll)
    (if (car st-list)
        (if (or (is-instance (car st-list) "slice") 
                (is-instance (car st-list) "transition") 
                (is-instance (car st-list) "transition on timeout")) 
            (break-into-states-sub
                    (cdr st-list) 
                    (cons (reverse cur-coll) coll)
                    (list (car st-list)))
            (break-into-states-sub (cdr st-list) coll (cons (car st-list) cur-coll)))
        (if (null cur-coll)
            (reverse coll)
            (reverse (cons cur-coll coll)))))

(defun break-into-states (st-list)
    (break-into-states-sub st-list '() '()))

(aclosure "simplify program" "state declaration" i c 
    (match :av c "stage" nil :ap c "agent" a :ap c "env" env :ap i "name" name :ap i "statements" sts
        :do (aset a "current state" name)
            (aset a "next state" (next-process-state a env))
            (update-push-aclosure c :av "stage" 'fstate :av "states" (break-into-states-sub sts)))
    (match :av c "stage" 'fstate :ap c "states" sts 
        :do (aset i "statements" (car sts))
            (update-push-aclosure c :av "stage" 'states :av "new states" (list i) :av "states" (cdr sts)))
    (match :av c "stage" 'statements :ap c "statements" sts
        :do (if (not (null sts))
                (update-push-aclosure c :av "statements" (cdr sts))
                (clear-update-eval-aclosure c :av "instance" (car sts))))
    (match :av c "stage" 'states :ap c "states" sts :v (null sts) t :ap c "new states" new-sts
        :do (reverse new-sts))
    (match :av c "stage" 'states :ap i "name" name :ap c "new states" new-sts :ap c "states" sts
        :p (car sts) cur-state
        :v (is-instance (car cur-state) "slice") t
        :p (aget c (aseq "agent" "slice counter")) counter
        :p (cdr cur-state) state-sts
        :p (create-light-state name "slice" counter) new-state-name
        :p (append (car new-sts) (mo "set state" :av "state" new-state-name)) updated-state
        :p (mo "state declaration" :av "name" new-state-name :av "statements" state-sts) new-state
        :do (aset c (aseq "agent" "slice counter") (+ counter 1))
            (update-push-aclosure c :av "stage" 'states :av "new states" (cons new-state (cons updated-state (cdr new-sts))) :av "states" (cdr sts))
            (update-push-aclosure c :av "stage" 'statements :av "statements" state-sts)
    )
    (match :av c "stage" 'states :ap i "name" name :ap c "new states" new-sts :ap c "states" sts
        :p (car sts) cur-state
        :v (is-instance (car cur-state) "transition") t
        :p (aget c (aseq "agent" "transition counter")) counter
        :p (cdr cur-state) state-sts
        :p (create-light-state name "transition" counter) new-state-name1
        :p (create-light-state name "transition" (+ counter 1)) new-state-name2
        :p (append (car new-sts) (mo "set state" :av "state" new-state-name1)) updated-state
        :p (mo "state declaration" 
            :av "name" new-state-name1 
            :av "statements" (list (mo "if then statement" 
                        :av "condition" (aget (car cur-state) "condition")
                        :av "then" (mo "set state" :av "state" new-state-name2)))) new-state1
        :p (mo "state declaration" :av "name" new-state-name2 
            :av "statements" state-sts) new-state2
        :do (aset c (aseq "agent" "slice counter") (+ counter 2))
            (update-push-aclosure c 
                :av "stage" 'states 
                :av "new states" (cons new-state2 (cons new-state1 (cons updated-state (cdr new-sts)))) 
                :av "states" (cdr sts))
            (update-push-aclosure c :av "stage" 'statements :av "statements" state-sts)
    )
    (match :av c "stage" 'states :ap i "name" name :ap c "new states" new-sts :ap c "states" sts
        :p (car sts) cur-state
        :v (is-instance (car cur-state) "transition on timeout") t
        :p (aget c (aseq "agent" "transition counter")) counter
        :p (cdr cur-state) state-sts
        :p (create-light-state name "transition" counter) new-state-name1
        :p (create-light-state name "transition" (+ counter 1)) new-state-name2
        :p (append (car new-sts) (mo "set state" :av "state" new-state-name1)) updated-state
        :p (mo "state declaration" 
            :av "name" new-state-name1 
            :av "statements" (list (mo "if then else statement" 
                        :av "condition" (aget (car cur-state) "condition")
                        :av "then" (mo "set state" :av "state" new-state-name2)
                        :av "else" (mo "timeout statement" 
                                    :av "controlling expression" (aget (car cur-state) "controlling expression")
                                    :av "statements" (aget (car cur-state) "statements"))))) new-state1
        :p (mo "state declaration" :av "name" new-state-name2 
            :av "statements" state-sts) new-state2
        :do (aset c (aseq "agent" "slice counter") (+ counter 2))
            (update-push-aclosure c 
                :av "stage" 'states 
                :av "new states" (cons new-state2 (cons new-state1 (cons updated-state (cdr new-sts)))) 
                :av "states" (cdr sts))
            (update-push-aclosure c :av "stage" 'statements :av "statements" state-sts)
    )
)

(aclosure "simplify program" "process declaration" i c 
    (match :av c "stage" nil :ap i "states" states :ap i "name" name
        :do (aset c (aseq "agent" "current process") name)
            (update-push-aclosure c :av "stage" 'states :av "states" (cdr states))
            (update-eval-aclosure c :av "instance" (car states)))
    (match :av c "stage" 'states :ap c "states" states :ap c "new states" nstates :p (aget c (aseq "agent" "value")) val
        :do (if states 
                (progn 
                    (update-push-aclosure c :av "stage" 'states :av "states" (cdr states) :av "new states" (append nstates val))
                    (clear-update-eval-aclosure c :av "instance" (car states)))
                (aset i "states" nstates))))

(aclosure "simplify program" "program declaration" i c 
    (match :av c "stage" nil :ap i "processes" procs
        :do (update-push-aclosure c :av "stage" 'procs :av "procs" (cdr procs))
            (update-eval-aclosure c :av "instance" (car procs)))
    (match :av c "stage" 'procs :ap c "procs" procs :v (not (null procs)) t
        :do (update-push-aclosure c :av "stage" 'procs :av "procs" (cdr procs))
            (update-eval-aclosure c :av "instance" (car procs))))