(in-package :user)

(defpackage :demos
  (:use CL :ok-utils :okbc))

(defpackage :fskb
  (:use CL :ok-utils :ok-back))

(pushnew :okbc-demos *features*)
