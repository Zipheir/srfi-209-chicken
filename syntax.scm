;;; Copyright (C) 2020--2023 Wolfgang Corcoran-Mathe
;;;
;;; Permission is hereby granted, free of charge, to any person obtaining a
;;; copy of this software and associated documentation files (the
;;; "Software"), to deal in the Software without restriction, including
;;; without limitation the rights to use, copy, modify, merge, publish,
;;; distribute, sublicense, and/or sell copies of the Software, and to
;;; permit persons to whom the Software is furnished to do so, subject to
;;; the following conditions:
;;;
;;; The above copyright notice and this permission notice shall be included
;;; in all copies or substantial portions of the Software.
;;;
;;; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
;;; OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
;;; MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
;;; IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
;;; CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
;;; TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
;;; SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

;;;; SRFI 209 syntax

(define-syntax define-enum
  (er-macro-transformer
    (lambda (expr rename compare)
      (define (check-enum-spec lis)
        (every (match-lambda
                 (x (symbol? x))
                 ((x v) (symbol? x))
                 (e (syntax-error 'define-enum "invalid enum spec" e)))
               lis))

      (define (enum-spec-names lis)
        (map (match-lambda
               (x x)
               ((x _) x))
             lis))

      (let ((type-name (list-ref expr 1))
            (enum-spec (list-ref expr 2))
            (constructor (list-ref expr 3)))
        (check-enum-spec enum-spec)
        (let ((names (enum-spec-names enum-spec))
              (indices (iota (length enum-spec)))
              (define (rename 'define))
              (define-syntax (rename 'define-syntax))
              (syntax-rules (rename 'syntax-rules))
              (oref (rename '%enum-ordinal->enum-no-check))
              (etype (rename 'etype)))
          `(,(rename 'begin)
            (,define ,etype
              (,(rename 'make-enum-type) (quote ,enum-spec)))

            (,define-syntax ,type-name
              (,syntax-rules ,names
                ,@(map (lambda (nm i)
                         `((_ ,nm) (,oref ,etype ,i)))
                       names
                       indices)
                ((_ name)
                 (,(rename syntax-error) (quote ,type-name)
                                         "invalid enum name"
                                         'name))))))))))

;; [Deprecated] As define-enum, except that type-name is bound to
;; a macro that returns its symbol argument if the corresponding
;; enum is in the new type.
(define-syntax define-enumeration
  (syntax-rules ()
    ((_ type-name (name-val ...) constructor)
     (begin
      (define etype (make-enum-type '(name-val ...)))
      (define-syntax type-name
        (syntax-rules ()
          ((_ name)
           (and (enum-name->enum etype 'name) 'name))))
      (define-syntax constructor
        (syntax-rules ()
          ((_ . names)
           (list->enum-set etype
                           (map (lambda (s)
                                  (enum-name->enum etype s))
                                'names)))))))))
