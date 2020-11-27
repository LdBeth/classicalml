(in-package #:asdf)

(defsystem classical-ml
  :name "Classical ML"
  :version "3.2.0"
  :serial t
  :components
  ((:file "package")
   (:file "site")
   (:module nuprlsys
    :depends-on ("package")
    :pathname "prl"
    :components ((:file "basic")
                 (:file "dependent")
                 ;;(:file "x-win")
                 (:file "control")
                 (:file "type")
                 (:file "vector")
                 (:file "data-defs"
                  :depends-on ("control" "type" "vector")) #|
                 (:file "scan-defs" :depends-on ("data-defs"))
                 (:file "action-buf" :depends-on ("data-defs"))
                 (:module scan
                  :depends-on ("scan-defs" "action-buf")
                  :components ((:file "scan")
                               (:file "ttree-gen")
                               (:file "best-ttree")
                               (:file "ttree-maint")
                               (:file "parse")
                               (:file "defn")
                               (:file "parse-goal")))
                 (:file "rule-defs" :depends-on ("data-defs"))
                 (:module rules
                   :depends-on ("rule-defs")
                   :serial t
                   :components ((:file "ref")
                                (:file "ref-support")
                                (:module parser
                                  :components ((:file "ruleparser")
                                               (:file "parse-eq")
                                               (:file "parse-comp")))
                                (:file "extract")
                                (:file "disp-rule")
                                (:file "rules")
                                (:file "rules-elim")
                                (:file "rules-intro")
                                (:file "rules-eq1")
                                (:file "rules-eq2")
                                (:file "tactic")
                                (:file "monot-aux")
                                (:file "monot")
                                (:file "division")
                                (:file "rules-comp")))
                 (:file "arith")
                 (:file "simplify")
                 (:file "equality")
                 (:file "prl")
                 (:file "eval")
                 (:file "theorem-obj")
                 (:file "red-defs")
                 (:file "disp-defs"
                  :depends-on ("red-defs"))
                 (:module editor
                   :depends-on ("disp-defs")
                   :components ((:file "red-status")
                                (:file "lib")
                                (:file "red")
                                (:file "ted")
                                (:file "disp-ttree")
                                (:file "disp-proof"))) |#
))
   (:module mlbase
    :depends-on (nuprlsys)
    :pathname "ml"
    :components ((:file "f-lispm")
                 (:file "f-macro" :depends-on ("f-lispm"))
                 (:file "dolists" :depends-on ("f-lispm"))
                 (:file "descriptor" :depends-on ("f-lispm"))
                 (:file "node-defs" :depends-on ("f-lispm"))
                 (:file "runtime-defs" :depends-on ("f-lispm"))))
   (:module mlsys
    :pathname "ml"
    :depends-on (nuprlsys)
    :components ((:file "f-iox-prl")
                 (:file "f-gp")
                 (:file "f-parser")
                 (:file "f-parsml")
                 (:file "f-mlprin")
                 (:file "f-typeml")
                 (:file "f-dml")
                 (:file "f-format")
                 (:file "f-writml")
                 (:file "f-tml")
                 (:file "f-lis")
                 (:file "f-obj")
                 (:file "compiler")
                 (:file "convert")
                 (:file "runtime")
                 (:file "translate")))
   #|
   (:module mlprl
    :pathname "ml"
    :depends-on (nuprlsys)
    :components ((:file "f-iox-prl")
                 (:file "ml-refine")
                 (:file "ml-rule")
                 (:file "ml-term")
                 (:file "ml-prl")
                 (:file "primitives")
                 (:file "io")
                 (:file "new-rules"))) |#
   ))
