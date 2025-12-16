(defpackage Reflex-semantics/tests/main
  (:use :cl
        :Reflex-semantics
        :rove))
(in-package :Reflex-semantics/tests/main)

;; NOTE: To run this test file, execute `(asdf:test-system :Reflex-semantics)' in your Lisp.

(deftest test-target-1
  (testing "should (= 1 1) to be true"
    (ok (= 1 1))))
