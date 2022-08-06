;;; Copyright (C) 2020 Wolfgang Corcoran-Mathe
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
;;;

;;;; Utility

(: exact-natural? (* --> boolean))
(define (exact-natural? obj)
  (and (exact-integer? obj) (not (negative? obj))))

(: bitvector-subset? (* * --> boolean))
(define (bitvector-subset? vec1 vec2)
  (let loop ((i (- (bitvector-length vec1) 1)))
    (cond ((< i 0) #t)
          ((and (bitvector-ref/bool vec1 i)
                (zero? (bitvector-ref/int vec2 i)))
           #f)
          (else (loop (- i 1))))))

;;;; Types

(define-type comparator (struct comparator))

(define-record-type <enum-type>
  (make-raw-enum-type enum-vector name-table comparator)
  enum-type?
  (enum-vector enum-type-enum-vector set-enum-type-enum-vector!
    : (or vector false))
  (name-table enum-type-name-table set-enum-type-name-table! : *)  ; hash-table
  (comparator enum-type-comparator set-enum-type-comparator!
    : (or comparator false)))

(define-type enum-type (struct <enum-type>))

(define-record-type <enum>
  (make-enum type name ordinal value)
  enum?
  (type enum-type : enum-type)
  (name enum-name : symbol)
  (ordinal enum-ordinal : fixnum)
  (value enum-value : *))

(define-type enum (struct <enum>))

(: make-enum-type ((list-of (or symbol (list symbol *))) -> enum-type))
(define (make-enum-type names+vals)
  (assume (or (pair? names+vals) (null? names+vals)))
  (let* ((type (make-raw-enum-type #f #f #f))
         (enums (generate-enums type names+vals)))
    (set-enum-type-enum-vector! type (list->vector enums))
    (set-enum-type-name-table! type (make-name-table enums))
    (set-enum-type-comparator! type (make-enum-comparator type))
    type))

(: generate-enums
   (enum-type (list-of (or symbol (list symbol *))) -> (list-of enum)))
(define (generate-enums type names+vals)
  (map (lambda (elt ord)
         (cond ((and (pair? elt) (= 2 (length elt)) (symbol? (car elt)))
                (make-enum type (car elt) ord (cadr elt)))
               ((symbol? elt) (make-enum type elt ord ord))
               (else (error "make-enum-type: invalid argument" elt))))
       names+vals
       (iota (length names+vals))))

(: symbol-comparator comparator)
(define symbol-comparator
  (make-comparator symbol?
                   eqv?
                   (lambda (sym1 sym2)
                     (string<? (symbol->string sym1)
                               (symbol->string sym2)))
                   symbol-hash))

(: make-name-table ((list-of enum) -> *))  ; hash-table
(define (make-name-table enums)
  (hash-table-unfold null?
                     (lambda (enums)
                       (values (enum-name (car enums)) (car enums)))
                     cdr
                     enums
                     symbol-comparator))

(: %enum-type=? (enum-type enum-type -> boolean))
(define (%enum-type=? etype1 etype2)
  (eqv? etype1 etype2))

(: make-enum-comparator (enum-type -> comparator))
(define (make-enum-comparator type)
  (make-comparator
   (lambda (obj)
     (and (enum? obj) (eq? (enum-type obj) type)))
   eq?
   (lambda (enum1 enum2)
     (< (enum-ordinal enum1) (enum-ordinal enum2)))
   (lambda (enum)
     (symbol-hash (enum-name enum)))))

;;;; Predicates

(: enum-type-contains? (enum-type enum --> boolean))
(define (enum-type-contains? type enum)
  (assume (enum-type? type))
  (assume (enum? enum))
  ((comparator-type-test-predicate (enum-type-comparator type)) enum))

(: %enum-type-contains?/no-check (enum-type enum --> boolean))
(define (%enum-type-contains?/no-check type enum)
  ((comparator-type-test-predicate (enum-type-comparator type)) enum))

(: %well-typed-enum? (enum-type * --> boolean))
(define (%well-typed-enum? type obj)
  (and (enum? obj) (%enum-type-contains?/no-check type obj)))

(: %compare-enums (procedure (list-of enum) --> boolean))
(define (%compare-enums compare enums)
  (assume (and (pair? enums) (pair? (cdr enums)))
          "invalid number of arguments")
  (assume (enum? (car enums)))
  (let ((type (enum-type (car enums))))
    (assume (every (lambda (e) (%well-typed-enum? type e)) (cdr enums))
            "invalid arguments")
    (apply compare (enum-type-comparator type) enums)))

(: enum=? (enum enum #!rest enum --> boolean))
(define (enum=? enum1 enum2 . enums)
  (assume (enum? enum1))
  (let* ((type (enum-type enum1))
         (comp (enum-type-comparator type)))
    (cond ((null? enums)                            ; fast path
           (assume (%well-typed-enum? type enum2) "enum=?: invalid argument")
           ((comparator-equality-predicate comp) enum1 enum2))
          (else                                     ; variadic path
           (assume (every (lambda (e) (%well-typed-enum? type e)) enums)
                   "enum=?: invalid arguments")
           (apply =? comp enum1 enum2 enums)))))

(: enum<? (#!rest enum --> boolean))
(define (enum<? . enums) (%compare-enums <? enums))

(: enum>? (#!rest enum --> boolean))
(define (enum>? . enums) (%compare-enums >? enums))

(: enum<=? (#!rest enum --> boolean))
(define (enum<=? . enums) (%compare-enums <=? enums))

(: enum>=? (#!rest enum --> boolean))
(define (enum>=? . enums) (%compare-enums >=? enums))

;;;; Enum finders

;;; Core procedures

(: enum-name->enum (enum-type symbol --> (or enum false)))
(define (enum-name->enum type name)
  (assume (enum-type? type))
  (assume (symbol? name))
  (hash-table-ref/default (enum-type-name-table type) name #f))

(: enum-ordinal->enum (enum-type fixnum --> (or enum false)))
(define (enum-ordinal->enum enum-type ordinal)
  (assume (enum-type? enum-type))
  (assume (exact-natural? ordinal))
  (and (< ordinal (enum-type-size enum-type))
       (vector-ref (enum-type-enum-vector enum-type) ordinal)))

;; Fast version for internal use.
(: %enum-ordinal->enum-no-check (enum-type fixnum --> enum))
(define (%enum-ordinal->enum-no-check enum-type ordinal)
  (vector-ref (enum-type-enum-vector enum-type) ordinal))

;;; Derived procedures

(: %enum-project (forall (a) (enum-type procedure * (enum -> a) -> a)))
(define (%enum-project type finder key proc)
  (assume (enum-type? type))
  (cond ((finder type key) => proc)
        (else (error "no enum found" type key))))

(: enum-name->ordinal (enum-type symbol -> fixnum))
(define (enum-name->ordinal type name)
  (assume (symbol? name))
  (%enum-project type enum-name->enum name enum-ordinal))

(: enum-name->value (enum-type symbol -> *))
(define (enum-name->value type name)
  (assume (symbol? name))
  (%enum-project type enum-name->enum name enum-value))

(: enum-ordinal->name (enum-type fixnum -> symbol))
(define (enum-ordinal->name type ordinal)
  (assume (exact-natural? ordinal))
  (%enum-project type %enum-ordinal->enum-no-check ordinal enum-name))

(: enum-ordinal->value (enum-type fixnum -> *))
(define (enum-ordinal->value type ordinal)
  (assume (exact-natural? ordinal))
  (%enum-project type %enum-ordinal->enum-no-check ordinal enum-value))

;;;; Enum type accessors

(: enum-type-size (enum-type --> fixnum))
(define (enum-type-size type)
  (assume (enum-type? type))
  (vector-length (enum-type-enum-vector type)))

(: enum-min (enum-type --> enum))
(define (enum-min type)
  (assume (enum-type? type))
  (vector-ref (enum-type-enum-vector type) 0))

(: enum-max (enum-type --> enum))
(define (enum-max type)
  (assume (enum-type? type))
  (let ((vec (enum-type-enum-vector type)))
    (vector-ref vec (- (vector-length vec) 1))))

(: enum-type-enums (enum-type --> (list-of enum)))
(define (enum-type-enums type)
  (assume (enum-type? type))
  (vector->list (enum-type-enum-vector type)))

(: enum-type-names (enum-type --> (list-of symbol)))
(define (enum-type-names type)
  (assume (enum-type? type))
  (let ((vec (enum-type-enum-vector type)))
    (list-tabulate (vector-length vec)
                   (lambda (n) (enum-name (vector-ref vec n))))))

(: enum-type-values (enum-type --> list))
(define (enum-type-values type)
  (assume (enum-type? type))
  (let ((vec (enum-type-enum-vector type)))
    (list-tabulate (vector-length vec)
                   (lambda (n) (enum-value (vector-ref vec n))))))

;;;; Enum object procedures

(: enum-next (enum --> (or enum false)))
(define (enum-next enum)
  (assume (enum? enum))
  (enum-ordinal->enum (enum-type enum) (+ (enum-ordinal enum) 1)))

(: enum-prev (enum --> (or enum false)))
(define (enum-prev enum)
  (assume (enum? enum))
  (let ((ord (enum-ordinal enum)))
    (and (> ord 0)
         (enum-ordinal->enum (enum-type enum) (- ord 1)))))

;;;; Enum set constructors

(define-record-type <enum-set>
  (make-enum-set type bitvector)
  enum-set?
  (type enum-set-type : enum-type)
  (bitvector enum-set-bitvector set-enum-set-bitvector! : *)) ; bitvector

(define-type enum-set (struct <enum-set>))

(: enum-empty-set (enum-type -> enum-set))
(define (enum-empty-set type)
  (assume (enum-type? type))
  (make-enum-set type (make-bitvector (enum-type-size type) #f)))

(: enum-type->enum-set (enum-type -> enum-set))
(define (enum-type->enum-set type)
  (assume (enum-type? type))
  (make-enum-set type (make-bitvector (enum-type-size type) #t)))

(: enum-set (enum-type #!rest enum -> enum-set))
(define (enum-set type . enums) (list->enum-set type enums))

(: list->enum-set (enum-type (list-of enum) -> enum-set))
(define (list->enum-set type enums)
  (assume (or (pair? enums) (null? enums)))
  (let ((vec (make-bitvector (enum-type-size type) #f)))
    (for-each (lambda (e)
                (assume (%well-typed-enum? type e) "ill-typed enum")
                (bitvector-set! vec (enum-ordinal e) #t))
              enums)
    (make-enum-set type vec)))

;; Returns a set of enums drawn from the enum-type/-set src with
;; the same names as the enums of eset.
(: enum-set-projection ((or enum-type enum-set) enum-set -> enum-set))
(define (enum-set-projection src eset)
  (assume (or (enum-type? src) (enum-set? src)))
  (assume (enum-set? eset))
  (let ((type (if (enum-type? src) src (enum-set-type src))))
    (list->enum-set
     type
     (enum-set-map->list
      (lambda (enum)
        (let ((name (enum-name enum)))
          (or (enum-name->enum type name)
              (error 'enum-set-projection
                     "enum name not found in type"
                     name
                     type))))
      eset))))

(: enum-set-copy (enum-set -> enum-set))
(define (enum-set-copy eset)
  (make-enum-set (enum-set-type eset)
                 (bitvector-copy (enum-set-bitvector eset))))

;; [Deprecated]
(: make-enumeration ((list-of symbol) -> enum-set))
(define (make-enumeration names)
  (enum-type->enum-set (make-enum-type (zip names names))))

;; [Deprecated]
(: enum-set-universe (enum-set -> enum-set))
(define (enum-set-universe eset)
  (assume (enum-set? eset))
  (enum-type->enum-set (enum-set-type eset)))

;; [Deprecated]  Returns a procedure which takes a list of symbols
;; and returns an enum set containing the corresponding enums.  This
;; extracts the type of eset, but otherwise ignores this argument.
(: enum-set-constructor (enum-set -> ((list-of enum) -> enum-set)))
(define (enum-set-constructor eset)
  (assume (enum-set? eset))
  (let ((type (enum-set-type eset)))
    (lambda (names)
      (list->enum-set type
                      (map (lambda (sym)
                             (or (enum-name->enum type sym)
                                 (error "name is not a member of type"
                                        type
                                        sym)))
                           names)))))

;; [Deprecated] Returns a procedure which takes a symbol and returns
;; the corresponding enum ordinal or #f.  This doesn't make any use
;; of eset, beyond pulling out its enum type.
(: enum-set-indexer (enum-set --> (symbol -> (or fixnum false))))
(define (enum-set-indexer eset)
  (assume (enum-set? eset))
  (let ((type (enum-set-type eset)))
    (lambda (name)
      (cond ((enum-name->enum type name) => enum-ordinal)
            (else #f)))))

;;;; Enum set predicates

(: enum-set-contains? (enum-set enum --> boolean))
(define (enum-set-contains? eset enum)
  (assume (enum-set? eset))
  (assume (%well-typed-enum? (enum-set-type eset) enum)
          "enum-set-contains?: invalid argument")
  (bitvector-ref/bool (enum-set-bitvector eset) (enum-ordinal enum)))

;; FIXME: Avoid double (type, then set) lookup.
(: enum-set-member? (symbol enum-set --> boolean))
(define (enum-set-member? name eset)
  (assume (symbol? name))
  (assume (enum-set? eset))
  (bitvector-ref/bool (enum-set-bitvector eset)
                      (enum-name->ordinal (enum-set-type eset) name)))

(: %enum-set-type=? (enum-set enum-set --> boolean))
(define (%enum-set-type=? eset1 eset2)
  (%enum-type=? (enum-set-type eset1) (enum-set-type eset2)))

(: enum-set-empty? (enum-set --> boolean))
(define (enum-set-empty? eset)
  (assume (enum-set? eset))
  (zero? (bitvector-count #t (enum-set-bitvector eset))))

(define (bit-nand a b)
  (not (and (= 1 a) (= 1 b))))

(: enum-set-disjoint? (enum-set enum-set --> boolean))
(define (enum-set-disjoint? eset1 eset2)
  (assume (enum-set? eset1))
  (assume (enum-set? eset2))
  (assume (%enum-type=? (enum-set-type eset1) (enum-set-type eset2)))
  (let ((vec1 (enum-set-bitvector eset1))
        (vec2 (enum-set-bitvector eset2)))
    (let ((len (bitvector-length vec1)))
      (let loop ((i 0))
        (or (= i len)
            (and (bit-nand (bitvector-ref/int vec1 i)
                           (bitvector-ref/int vec2 i))
                 (loop (+ i 1))))))))

(: enum-set=? (enum-set enum-set --> boolean))
(define (enum-set=? eset1 eset2)
  (assume (%enum-type=? (enum-set-type eset1) (enum-set-type eset2)))
  (bitvector=? (enum-set-bitvector eset1) (enum-set-bitvector eset2)))

(: enum-set<? (enum-set enum-set --> boolean))
(define (enum-set<? eset1 eset2)
  (assume (enum-set? eset1))
  (assume (enum-set? eset2))
  (assume (%enum-type=? (enum-set-type eset1) (enum-set-type eset2)))
  (let ((vec1 (enum-set-bitvector eset1))
        (vec2 (enum-set-bitvector eset2)))
    (and (bitvector-subset? vec1 vec2)
         (not (bitvector=? vec1 vec2)))))

(: enum-set>? (enum-set enum-set --> boolean))
(define (enum-set>? eset1 eset2)
  (assume (enum-set? eset1))
  (assume (enum-set? eset2))
  (assume (%enum-type=? (enum-set-type eset1) (enum-set-type eset2)))
  (let ((vec1 (enum-set-bitvector eset1))
        (vec2 (enum-set-bitvector eset2)))
    (and (bitvector-subset? vec2 vec1)
         (not (bitvector=? vec1 vec2)))))

(: enum-set<=? (enum-set enum-set --> boolean))
(define (enum-set<=? eset1 eset2)
  (assume (enum-set? eset1))
  (assume (enum-set? eset2))
  (assume (%enum-type=? (enum-set-type eset1) (enum-set-type eset2)))
  (bitvector-subset? (enum-set-bitvector eset1)
                     (enum-set-bitvector eset2)))

(: enum-set>=? (enum-set enum-set --> boolean))
(define (enum-set>=? eset1 eset2)
  (assume (enum-set? eset1))
  (assume (enum-set? eset2))
  (assume (%enum-type=? (enum-set-type eset1) (enum-set-type eset2)))
  (bitvector-subset? (enum-set-bitvector eset2)
                     (enum-set-bitvector eset1)))

(: enum-set-subset? (enum-set enum-set --> boolean))
(define (enum-set-subset? eset1 eset2)
  (assume (enum-set? eset1))
  (assume (enum-set? eset2))
  (let ((names
         (lambda (eset)
           (enum-set-fold (lambda (e ns)
                            (cons (enum-name e) ns))
                          '()
                          eset))))
    (lset<= eq? (names eset1) (names eset2))))

(: enum-set-any? ((enum -> boolean) enum-set -> boolean))
(define (enum-set-any? pred eset)
  (assume (procedure? pred))
  (call-with-current-continuation
   (lambda (return)
     (enum-set-fold (lambda (e _) (and (pred e) (return #t)))
                    #f
                    eset))))

(: enum-set-every? ((enum -> boolean) enum-set -> boolean))
(define (enum-set-every? pred eset)
  (assume (procedure? pred))
  (call-with-current-continuation
   (lambda (return)
     (enum-set-fold (lambda (e _) (or (pred e) (return #f)))
                    #t
                    eset))))

;;;; Enum set mutators

(: enum-set-adjoin (enum-set #!rest enum -> enum-set))
(define (enum-set-adjoin eset . enums)
  (apply enum-set-adjoin! (enum-set-copy eset) enums))

(: enum-set-adjoin! (enum-set #!rest enum -> enum-set))
(define enum-set-adjoin!
  (case-lambda
    ((eset enum)                 ; fast path
     (assume (enum-set? eset))
     (assume (%well-typed-enum? (enum-set-type eset) enum))
     (bitvector-set! (enum-set-bitvector eset) (enum-ordinal enum) #t)
     eset)
    ((eset . enums)              ; variadic path
     (assume (enum-set? eset))
     (let ((type (enum-set-type eset))
           (vec (enum-set-bitvector eset)))
       (for-each (lambda (e)
                   (assume (%well-typed-enum? type e)
                           "enum-set-adjoin!: ill-typed enum")
                   (bitvector-set! vec (enum-ordinal e) #t))
                 enums)
       eset))))

(: enum-set-delete (enum-set #!rest enum -> enum-set))
(define (enum-set-delete eset . enums)
  (apply enum-set-delete! (enum-set-copy eset) enums))

(: enum-set-delete! (enum-set #!rest enum -> enum-set))
(define enum-set-delete!
  (case-lambda
    ((eset enum)                ; fast path
     (assume (enum-set? eset))
     (assume (%well-typed-enum? (enum-set-type eset) enum)
             "enum-set-delete!: ill-typed enum")
     (bitvector-set! (enum-set-bitvector eset) (enum-ordinal enum) #f)
     eset)
    ((eset . enums)             ; variadic path
     (enum-set-delete-all! eset enums))))

(: enum-set-delete-all (enum-set (list-of enum) -> enum-set))
(define (enum-set-delete-all eset enums)
  (enum-set-delete-all! (enum-set-copy eset) enums))

(: enum-set-delete-all! (enum-set (list-of enum) -> enum-set))
(define (enum-set-delete-all! eset enums)
  (assume (enum-set? eset))
  (assume (or (pair? enums) (null? enums)))
  (unless (null? enums)
    (let ((type (enum-set-type eset))
          (vec (enum-set-bitvector eset)))
       (for-each (lambda (e)
                   (assume (%well-typed-enum? type e)
                           "enum-set-delete-all!: ill-typed enum")
                   (bitvector-set! vec (enum-ordinal e) #f))
                 enums)))
  eset)

;;;; Enum set operations

(: enum-set-size (enum-set --> fixnum))
(define (enum-set-size eset)
  (assume (enum-set? eset))
  (bitvector-count #t (enum-set-bitvector eset)))

(: enum-set->enum-list (enum-set --> (list-of enum)))
(define (enum-set->enum-list eset)
  (assume (enum-set? eset))
  (enum-set-map->list values eset))

(: enum-set->list (enum-set --> (list-of symbol)))
(define (enum-set->list eset)
  (enum-set-map->list enum-name eset))

;; Slightly complicated by the order in which proc is applied.
(: enum-set-map->list
   (forall (a) ((enum -> a) enum-set -> (list-of a))))
(define (enum-set-map->list proc eset)
  (assume (procedure? proc))
  (assume (enum-set? eset))
  (let* ((vec (enum-set-bitvector eset))
         (len (bitvector-length vec))
         (type (enum-set-type eset)))
    (letrec
     ((build
       (lambda (i)
         (cond ((= i len) '())
               ((bitvector-ref/bool vec i)
                (cons (proc (%enum-ordinal->enum-no-check type i))
                      (build (+ i 1))))
               (else (build (+ i 1)))))))
      (build 0))))

(: enum-set-count ((enum -> boolean) enum-set -> fixnum))
(define (enum-set-count pred eset)
  (assume (procedure? pred))
  (enum-set-fold (lambda (e n) (if (pred e) (+ n 1) n)) 0 eset))

(: enum-set-filter ((enum -> boolean) enum-set -> enum-set))
(define (enum-set-filter pred eset)
  (enum-set-filter! pred (enum-set-copy eset)))

(: enum-set-filter! ((enum -> boolean) enum-set -> enum-set))
(define (enum-set-filter! pred eset)
  (assume (procedure? pred))
  (assume (enum-set? eset))
  (let* ((type (enum-set-type eset))
         (vec (enum-set-bitvector eset)))
    (let loop ((i (- (bitvector-length vec) 1)))
      (cond ((< i 0) eset)
            ((and (bitvector-ref/bool vec i)
                  (not (pred (%enum-ordinal->enum-no-check type i))))
             (bitvector-set! vec i #f)
             (loop (- i 1)))
            (else (loop (- i 1)))))))

(: enum-set-remove ((enum -> boolean) enum-set -> enum-set))
(define (enum-set-remove pred eset)
  (enum-set-remove! pred (enum-set-copy eset)))

(: enum-set-remove! ((enum -> boolean) enum-set -> enum-set))
(define (enum-set-remove! pred eset)
  (assume (procedure? pred))
  (assume (enum-set? eset))
  (let* ((type (enum-set-type eset))
         (vec (enum-set-bitvector eset)))
    (let loop ((i (- (bitvector-length vec) 1)))
      (cond ((< i 0) eset)
            ((and (bitvector-ref/bool vec i)
                  (pred (%enum-ordinal->enum-no-check type i)))
             (bitvector-set! vec i #f)
             (loop (- i 1)))
            (else (loop (- i 1)))))))

(: enum-set-for-each (procedure enum-set -> undefined))
(define (enum-set-for-each proc eset)
  (assume (procedure? proc))
  (enum-set-fold (lambda (e _) (proc e)) '() eset))

(: enum-set-fold ((enum * -> *) * enum-set -> *))
(define (enum-set-fold proc nil eset)
  (assume (procedure? proc))
  (assume (enum-set? eset))
  (let ((type (enum-set-type eset)))
    (let* ((vec (enum-set-bitvector eset))
           (len (bitvector-length vec)))
      (let loop ((i 0) (state nil))
        (cond ((= i len) state)
              ((bitvector-ref/bool vec i)
               (loop (+ i 1)
                     (proc (%enum-ordinal->enum-no-check type i) state)))
              (else (loop (+ i 1) state)))))))

;;;; Enum set logical operations

(: %enum-set-logical-op ((* * -> *) enum-set enum-set -> enum-set))
(define (%enum-set-logical-op bv-proc eset1 eset2)
  (assume (enum-set? eset1))
  (assume (enum-set? eset2))
  (assume (%enum-set-type=? eset1 eset2) "enum sets have different types")
  (make-enum-set (enum-set-type eset1)
                 (bv-proc (enum-set-bitvector eset1)
                          (enum-set-bitvector eset2))))

;; bv-proc mutates eset1.
(: %enum-set-logical-op! ((* * -> *) enum-set enum-set -> enum-set))
(define (%enum-set-logical-op! bv-proc eset1 eset2)
  (assume (enum-set? eset1))
  (assume (enum-set? eset2))
  (assume (%enum-set-type=? eset1 eset2) "enum sets have different types")
  (bv-proc (enum-set-bitvector eset1) (enum-set-bitvector eset2))
  eset1)

(: enum-set-union (enum-set enum-set -> enum-set))
(define enum-set-union
  (cut %enum-set-logical-op bitvector-ior <> <>))

(: enum-set-intersection (enum-set enum-set -> enum-set))
(define enum-set-intersection
  (cut %enum-set-logical-op bitvector-and <> <>))

(: enum-set-difference (enum-set enum-set -> enum-set))
(define enum-set-difference
  (cut %enum-set-logical-op bitvector-andc2 <> <>))

(: enum-set-xor (enum-set enum-set -> enum-set))
(define enum-set-xor
  (cut %enum-set-logical-op bitvector-xor <> <>))

(: enum-set-union! (enum-set enum-set -> enum-set))
(define enum-set-union!
  (cut %enum-set-logical-op! bitvector-ior! <> <>))

(: enum-set-intersection! (enum-set enum-set -> enum-set))
(define enum-set-intersection!
  (cut %enum-set-logical-op! bitvector-and! <> <>))

(: enum-set-difference! (enum-set enum-set -> enum-set))
(define enum-set-difference!
  (cut %enum-set-logical-op! bitvector-andc2! <> <>))

(: enum-set-xor! (enum-set enum-set -> enum-set))
(define enum-set-xor!
  (cut %enum-set-logical-op! bitvector-xor! <> <>))

(: enum-set-complement (enum-set -> enum-set))
(define (enum-set-complement eset)
  (assume (enum-set? eset))
  (make-enum-set (enum-set-type eset)
                 (bitvector-not (enum-set-bitvector eset))))

(: enum-set-complement! (enum-set -> enum-set))
(define (enum-set-complement! eset)
  (assume (enum-set? eset))
  (bitvector-not! (enum-set-bitvector eset))
  eset)

;;;; Syntax

;; Defines a new enum-type T, binds type-name to a macro which
;; takes a symbol to an enum in T, and binds constructor to a
;; macro taking symbols to an enum set of type T.
(define-syntax define-enum
  (syntax-rules ()
    ((_ type-name (name-val ...) constructor)
     (begin
      (define etype (make-enum-type '(name-val ...)))
      (define-syntax type-name
        (syntax-rules ()
          ((_ name)
           (enum-name->enum etype 'name))))
      (define-syntax constructor
        (syntax-rules ()
          ((_ . names)
           (list->enum-set etype
                           (map (lambda (s)
                                  (enum-name->enum etype s))
                                'names)))))))))

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
