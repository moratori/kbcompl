

(defpackage :kbcompl.system.main
  (:use :cl)
  (:export
    :prove-eqexpr
    :prove-eqexpr%
    :completion

    :eqexpr

    :endless-critical-pair-error
    :endless-regularization-error
    :same-complexity-error
    ))

(in-package :kbcompl.system.main)



(defvar +LIMIT+ 50)

(define-condition endless-critical-pair-error () ())
(define-condition endless-regularization-error () ())
(define-condition same-complexity-error-error () ())
 

(defstruct (vterm  (:constructor vterm (var const)))
  (var nil :type symbol)
  (const nil :type boolean))

(defstruct (fterm (:constructor fterm (fsymbol &rest terms)))
  (fsymbol nil  :type symbol)
  (terms   nil :type list))

(defstruct (rw-rule (:constructor rw-rule (left right)))
  left
  right)

(defstruct (eqexpr (:constructor eqexpr (left right)))
  left
  right)



(defmethod term= ((t1 vterm) (t2 vterm))
  (and
	(eq (vterm-var t1) (vterm-var t2))
	(eq (vterm-const t1) (vterm-const t2))))


(defmethod term= ((t1 fterm) (t2 fterm))
  (and 
	(eq (fterm-fsymbol t1) 
		(fterm-fsymbol t2))
	(let ((argv1 (fterm-terms t1))
		  (argv2 (fterm-terms t2)))
	  (and 
		(= (length argv1) 
		   (length argv2))
		(every 
		  (lambda (x y) (term= x y)) argv1 argv2)))))

(defmethod term= (a b)
  nil)




(defmethod substitute-term ((target vterm) old new)
  (if (term= old target) new target))

(defmethod substitute-term ((target fterm) old new)
  (apply #'fterm 
		 (fterm-fsymbol target)
		 (mapcar 
		   (lambda (x) 
			 (substitute-term x old new)) 
		   (fterm-terms target))))




(defun occurrence? (vterm fterm) 
	(cond 
		((fterm-p fterm)
		 (some 
			 (lambda (x)
				 (occurrence? vterm x)) 
			 (fterm-terms fterm)))
		(t 
			(term= vterm fterm))))


(defun subst-term (new old seq)
  (substitute-if new (lambda (x) (term= x old)) seq))

(defun subst-old-rule (old-rules new-rules)
  ;; new-rules = ((old . new))
  ;; old-rules = ((old1 . new1) (old2 . new2) ...)
  (if (null new-rules) old-rules
	 (destructuring-bind (old . new) (car new-rules)
	   (subst-old-rule
(mapcar 
	  (lambda (x)
		(destructuring-bind (each-old . each-new) x
		 (cons each-old
			   (cond 
				 ((vterm-p each-new)
					(car (subst-term new old (list each-new))))
				 ((fterm-p each-new)
					(apply #'fterm (fterm-fsymbol each-new) 
						   (subst-term new old (fterm-terms each-new))))
				 (t (error (make-condition 'struct-unmatch-error 
					   :sue-val each-new
					   :sue-where 'subst-old-rule)))))))
	  old-rules)
		(cdr new-rules)
		 )
	   )
	)
 )


(defun absurd (result)
  (cond
	((typep result 'boolean) result)
	(t
	  (loop named exit 
			for x in result
			finally (return-from exit result)
			do 
			(loop for y in result
				  do
				  (destructuring-bind (x1 . x2) x
					(destructuring-bind (y1 . y2) y
					  (when (and 
							  (term= x1 y1)
							  (not (term= x2 y2)))
						(return-from exit nil)))))))))

(defun subst-new-rule (old-rules new-rules)
  ;; new-rules = ((old . new))
  ;; old-rules = ((old1 . new1) (old2 . new2) ...)
  (reduce 
	(lambda (x y)
	  (subst-old-rule x (list y))) 
	old-rules :initial-value new-rules))

(defmethod mgu ((t1 vterm) (t2 vterm))
  (cond 
	((term= t1 t2) t)
	((and (vterm-const t1) 
		  (not (vterm-const t2)))
	 (acons t2 t1 nil))
	((and (vterm-const t2) 
		  (not (vterm-const t1)))
	 (acons t1 t2 nil))
	((not (or (vterm-const t1)
			  (vterm-const t2)))
	 (acons t1 t2 nil)
	 )
	(t nil)))


(defmethod mgu ((t1 fterm) (t2 vterm))
  (cond 
	((vterm-const t2)
	 (eq (fterm-fsymbol t1)
		 (vterm-var t2)))
	(t 
		(unless (occurrence? t2 t1)	
			(acons t2 t1 nil)))))

(defmethod mgu ((t1 vterm) (t2 fterm))
  (mgu t2 t1))


(defmethod mgu ((t1 fterm) (t2 fterm))
  (cond 
	;; 変数の場合と同様、全く同一なら単一化の処理は必要ない
	((term= t1 t2) t)
	((not (eq (fterm-fsymbol t1)
			  (fterm-fsymbol t2)))
	 nil)
	((/= (length (fterm-terms t1))
		 (length (fterm-terms t2)))
	 nil)
	(t
	  (labels 
		((main (result argv1 argv2)
			(if (null argv1) result
			  (let ((unifier (mgu (car argv1) 
								  (car argv2))))
				;(print unifier)
					(cond 
					  ;; 単一化は失敗
					  ((null unifier) nil)

					  ((listp unifier)
						(apply #'main 
							   (append (subst-old-rule result unifier) 
									   (subst-new-rule result unifier))
							   (reduce 
								 (lambda (x y)
								   (destructuring-bind (old . new) y
									 (destructuring-bind (a1 a2) x
									   (list 
										 (subst-term new old a1)
										 (subst-term new old a2))))) 
								 unifier :initial-value (list (cdr argv1) (cdr argv2)))))
					  
					  (t (main result
						   	   (cdr argv1)
							   (cdr argv2))))))))
		
		(absurd
		  (main nil
		  	  (fterm-terms t1)
			  (fterm-terms t2)))))))







(defmethod term-using? ((vterm vterm) (term vterm))
  (term= vterm term))


(defmethod term-using? ((vterm vterm) (term fterm))
  (some 
	(lambda (x)
	  (term-using? vterm x))
	(fterm-terms term)))



(defun rec-match (term1 term2)

  ;; term1 は 必ず等号の左辺でなければいけないとする
  ;; -> そういうのじゃなくて、置き換え元が定数となるようなことがあり得ない
  ;;    ようにすればいいだけじゃね???

  
  (assert 
    (and (or (typep term1 'vterm)
             (typep term1 'fterm))
         (or (typep term2 'vterm)
             (typep term2 'fterm))))
  (cond 
    ((and (typep term1 'vterm)
          (typep term2 'vterm))
     (when (term-using? term1 term2)
       (mgu term1 term2)))
    ((or 
       (and (typep term1 'vterm)
            (typep term2 'fterm))
       (and (typep term1 'fterm)
            (typep term2 'fterm)))
     ;; 関数項の初めから見ていき
     ;; 初めにマッチしたものを返す。
     ;; 全ては見ない
     ;; recmatch(a,f(b,x,y))
     ;; とかだったら x -> a のみを返す
     (let ((first-order-mgu (mgu term1 term2)))
       (if first-order-mgu 
         first-order-mgu
         (some 
           (lambda (each-term)
             (rec-match term1 each-term)) (fterm-terms term2)))))
    ((and (typep term1 'fterm)
          (typep term2 'vterm))
     ;(rec-match term2 term1)
     (mgu term2 term1))))




(defun substitute-fterm (tar old new)
  (cond 
    ((vterm-p tar)
     tar)
    ((term= tar old) new)
    (t 
     (assert (fterm-p tar))
     (apply #'fterm 
            (fterm-fsymbol tar)
            (mapcar 
              (lambda (each)
                (substitute-fterm each old new)) 
              (fterm-terms tar))))))

(defun substitute-term-recursive (pair t-term)
  (destructuring-bind (old . new) pair
    (if (vterm-p old) 
          (substitute-term t-term old new)
          (substitute-fterm t-term old new))))



(defmethod get-order ((term vterm))
  (if (vterm-const term) 1 2))

(defmethod get-order ((term fterm))
  (1+ (apply #'+ (mapcar (lambda (x) (* (length (fterm-terms term)) (get-order x)))  (fterm-terms term)))))




(defun get-regular% (term rules)
  (get-regular term rules +LIMIT+)
  )



;;; 正規形を求める
;;; つまりこれ以上簡約できない形まで変形する
(defmethod get-regular ((term vterm) rules cnt)
  (assert (and (listp rules) (every (lambda (x) (typep x 'rw-rule)) rules)))

  (when (> 0 cnt)
    (error (make-condition 'endless-regularization-error)))
  
  ;; どの規則のドメインにも合致しないなら
  ;; やってみて、変わってたらもっかいにした方がよくないか？
  ;; fterm版ではそうする
  (if (every (lambda (rule) (not (mgu (rw-rule-left rule) term))) rules)
    term
    
    (get-regular

      (reduce 
      (lambda (res each)
        (let* ((left (rw-rule-left each))
               (right (rw-rule-right each))
               (unifier (mgu res left)))
          (cond 
            ((null unifier) res)
            ((eq unifier t) right)
            (t 
             ;; ここ unifier 使う必要なくね?
            (let ((one (car unifier)))
              (substitute-term right (car one) (cdr one)))))))
      rules
      :initial-value term)
      
      rules
      (1- cnt)
      )
    )) 
 

(defun matching (term unifier)
  (if (eq unifier t)
    term
    (reduce 
    (lambda (res x)
      (substitute-term res (car x) (cdr x)))
    unifier
    :initial-value term
    )
    )
  
  )


(defmethod get-regular ((term fterm) rules cnt)
(when (> 0 cnt)
    (error (make-condition 'endless-regularization-error)))
  (let ((result 
          (reduce 
    (lambda (res each)
      (let* ((r-left (rw-rule-left each))
             (r-right (rw-rule-right each))
             (unifier (rec-match r-left term)))
       
        (if (null unifier)
          res
          (substitute-term-recursive 
            (cons (matching r-left unifier) (matching r-right unifier))
            res))))
    rules
    :initial-value term)
          ))
    (if (term= result term) result
      (get-regular result rules (1- cnt))
      )
    
    )
  )
 

(defmethod show ((term vterm))
  (format nil "~A" (vterm-var term)))

(defmethod show ((term fterm))
  (format nil "~A(~{~A~^,~})"
          (symbol-name (fterm-fsymbol term))
          (mapcar #'show (fterm-terms term))))
 

(defmethod rule= ((r1 rw-rule) (r2 rw-rule))
  (and 
    (term= (rw-rule-left r1) (rw-rule-left r2))
    (term= (rw-rule-right r1) (rw-rule-right r2))))



(defun get-critical-pair (r)
  (let (result)
    (loop for r1 in r do 
      (loop for r2 in r do
        (loop for target in r
           if (and (not (rule= r1 r2)) (not (rule= r2 target))) do
           (let* ((left (rw-rule-left target))
                  (reg-left1 (get-regular% left (list r1)))
                  (reg-left2 (get-regular% left (list r2)))
                  (right (rw-rule-right target))
                  (reg-right1 (get-regular% right (list r1)))
                  (reg-right2 (get-regular% right (list r2))))
             
             (when (not (term= reg-left1 reg-left2))
               (push (eqexpr reg-left1 reg-left2) result))

             (when (not (term= reg-right1 reg-right2))
               (push (eqexpr reg-right1 reg-right2) result))))))
    result
    ) 
  )


(defun regular-rule (r)
  r)

(defun regular-eq (e)
  e)



(defun dump-rules (r)
  (dolist (each r)
    (format t "~A -> ~A~%" (show (rw-rule-left each)) (show (rw-rule-right each)))
    )
  )

(defun dump-eqexpr (r)
  (dolist (each r)
    (format t "~A = ~A~%" (show (eqexpr-left each)) (show (eqexpr-right each)))
    )
  (format t "~%")
  )


;; 新しいRから生成された等式をEに戻す処理が抜けてる
(defun completion (E &optional (R nil) (limit 150))
  

  (when (> 0 limit)
    (error 
      (make-condition 'endless-critical-pair-error)))

  (if (null E) R
    (let* ((eqexpr (first E))
           (left (get-regular% (eqexpr-left eqexpr) r))
           (right (get-regular% (eqexpr-right eqexpr) r))
           (lo (get-order left))
           (ro (get-order right))) 
      (if (term= left right) 
        (completion (cdr e) r (1- limit))
        (cond 
          ((>= lo ro)
           (let ((next-r (regular-rule  (cons (rw-rule left right) r))))
             (completion
               (regular-eq (append (cdr e) (get-critical-pair next-r)))
               next-r
               (1- limit))))
          ((> ro lo)
           (let ((next-r (regular-rule (cons (rw-rule right left) r))))
             (completion
               (regular-eq (append (cdr e) (get-critical-pair next-r)))
               next-r
               (1- limit))))
          (t 
           (error 
             (make-condition 'same-complexity-error))))))))


(defun completion-toplevel (e)
  (let ((rule (completion e)))
    (dolist (each rule)
      (format t "~%~A -> ~A"
              (show (rw-rule-left each))
              (show (rw-rule-right each)))))
  (format t "~%"))



(defun prove-eqexpr% (eqexpr ruleset)
  (term= 
       (get-regular%
         (eqexpr-left eqexpr)
         ruleset)
       (get-regular% 
         (eqexpr-right eqexpr)
         ruleset)))


(defun prove-eqexpr (eqexpr axioms)
  (prove-eqexpr% eqexpr (completion axioms)))




  


#|
;; { A = B , g(x,B) , g(A,B) = C} |- f(B) = C
(print 
  (prove-eqexpr
    (eqexpr 
      (fterm 'f (vterm 'B t))
      (vterm 'C t))
    (list 
       (eqexpr 
         (vterm 'A t)
         (vterm 'B t))
       (eqexpr
         (fterm 'g (vterm 'x nil) (vterm 'B t))
         (fterm 'f (vterm 'x nil)))
       (eqexpr 
         (fterm 'g (vterm 'A t) (vterm 'B t))
         (vterm 'C t)))))


;; { add(x,ZERO) = x , add(x,s(y)) = s(add(x,y))} |- add(s(ZERO),s(s(ZERO))) = s(s(s(ZERO)))
(print 
  (prove-eqexpr 
    (eqexpr
      (fterm 'add (fterm 's (vterm 'ZERO t)) (fterm 's (fterm 's (vterm 'ZERO t))))
      (fterm 's (fterm 's (fterm 's (vterm 'ZERO t)))))
    (list 
      (eqexpr 
        (fterm 'add (vterm 'x nil) (vterm 'ZERO t))
        (vterm 'x nil))
      (eqexpr 
        (fterm 'add (vterm 'x nil) (fterm 's (vterm 'y nil)))
        (fterm 's (fterm 'add (vterm 'x nil) (vterm 'y nil)))))))


|#
