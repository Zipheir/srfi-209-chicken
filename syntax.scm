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

(begin-for-syntax
 ;; Like 'assert', but calls 'syntax-error' if the tested condition
 ;; is false.
 (define-syntax assert/syntax-error
   (syntax-rules ()
     ((_ loc expr)
      (assert/syntax-error loc expr "syntax violation"))
     ((_ loc expr msg)
      (unless expr
        (syntax-error loc msg 'expr)))))

 ;; Helper for writing complex ER macros.
 (define-syntax let-renamed
   (syntax-rules ()
     ((_ rename (id ...) e0 e1 ...)
      (let ((id (rename 'id)) ...) e0 e1 ...))))
 )

;;;; SRFI 209 syntax

(define-syntax define-enum
  (er-macro-transformer
    (lambda (expr rename compare)
      (define (unique-ids? list)
        (let unique ((list list))
          (or (null? list)
              (let ((x (car list))
                    (rest (cdr list)))
                (and (not (find (lambda (y) (compare x y)) rest))
                     (unique rest))))))

      (define (check-unique-ids list)
        (unless (unique-ids? list)
          (syntax-error 'define-enum "enum names must be unique" list)))

      ;; Extract the enum names and check for enum-spec well-formedness.
      (define (enum-spec-names lis)
        (map (lambda (x)
               (cond ((symbol? x) x)
                     ((and (pair? x) (= (length x) 2)) (car x))
                     (else (syntax-error 'define-enum
                             "invalid enum name" x))))
             lis))

      (let* ((type-name (list-ref expr 1))
             (enum-spec (list-ref expr 2))
             (constructor (list-ref expr 3))
             (names (enum-spec-names enum-spec))
             (indices (iota (length enum-spec)))
             (oref (rename '%enum-ordinal->enum-no-check)))
        (let-renamed rename (define define-syntax syntax-rules etype
                             begin enum-set make-enum-type)
          (assert/syntax-error 'define-enum (symbol? type-name)
           "type name must be an identifier")
          (assert/syntax-error 'define-enum
            (or (pair? enum-spec) (null? enum-spec)))
          (assert/syntax-error 'define-enum (symbol? constructor)
           "constructor name must be an identifier")
          (check-unique-ids names)
          `(,begin
            (,define ,etype
              (,make-enum-type (quote ,enum-spec)))

            (,define-syntax ,type-name
              (,syntax-rules ,names
                ,@(map (lambda (nm i)
                         `((_ ,nm) (,oref ,etype ,i)))
                       names
                       indices)
                ((_ (x ...))
                 (,(rename syntax-error) (quote ,type-name)
                                         "invalid enum name"
                                         '(x ...)))
                ((_ name)
                 (,(rename syntax-error) (quote ,type-name)
                                         "enum name not found in type"
                                         'name))))

            (,define-syntax ,constructor
              (,syntax-rules ()
                ((_ arg ...)
                 (,enum-set ,etype (,type-name arg) ...))))))))))

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
