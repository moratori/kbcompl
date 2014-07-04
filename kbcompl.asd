


(defpackage kbcompl.asd
	(:use :cl :asdf))

(in-package :kbcompl.asd)


(defsystem kbcompl
	:serial t
	:version "1.0"
	:author "moratori"
	:components 
		((:module "src"
		  :serial t
		  :components 
				((:file "knuth-bendix"))
		  	)))


