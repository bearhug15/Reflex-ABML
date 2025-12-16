(asdf:defsystem "Reflex-semantics"
  :version "0.0.1"
  :author ""
  :license ""
  :depends-on (:cl-smt-lib)
  :components ((:module "src"
                :components
                ((:file "ABML-plugs")
                  (:file "main")
                  (:file "Reflex-concepts")
                  (:module "Reflex-axiomatic"
                    :components 
                    ((:file "Reflex-axiomatic-auxiliary")
                      (:file "Reflex-axiomatic")))
                  (:module "Reflex-prepare"
                    :components 
                    ((:file "Reflex-name-mapper")
                      (:file "Reflex-normalize")
                      (:file "Reflex-type-specifier")))
                  (:module "Reflex-operational"
                    :components 
                    ((:file "Reflex-operational-auxiliary")
                      (:file "Reflex-operational")))
                  (:module "Static-analysis"
                    :components
                    ((:file "Analysis-attributes-prepare")
                      (:file "Group-static-analysis")
                      (:file "Simple-static-analysis")
                      (:file "Static-analysis-auxiliary")
                      (:file "Static-analysis"))))))
  :description ""
  :in-order-to ((test-op (test-op "Reflex-semantics/tests"))))
