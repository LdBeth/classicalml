(in-package #:common-lisp-user)

(defpackage #:nuprl
  (:use #:common-lisp)
  (:shadow #:substitute #:copy-seq #:trap #:function))

(defpackage #:ml-runtime
  (:nicknames #:mlr)
  (:use #:common-lisp))
