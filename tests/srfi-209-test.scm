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

;;; Test suite for chibi-scheme (http://synthcode.com/scheme/chibi)
;;; Adapted for the CHICKEN test egg.

(import (scheme)
        (chicken base)
        (srfi 1)
        (srfi 128)
        (srfi 209)
        (test))

;; (chibi test) shim
(define-syntax test-not
  (syntax-rules ()
    ((_ expr) (test-assert (not expr)))))

;;;; Utility

(define always (constantly #t))
(define never (constantly #f))

;; Run a procedure on fresh copies of two enum sets.
(define (fresh-sets proc eset1 eset2)
  (proc (enum-set-copy eset1) (enum-set-copy eset2)))

;;;; Test types

(define color-names
  '(red tangerine orange yellow green cyan blue violet))

(define color (make-enum-type color-names))

(define color-red (enum-name->enum color 'red))

(define color-tangerine (enum-name->enum color 'tangerine))

(define color-blue (enum-name->enum color 'blue))

(define color-green (enum-name->enum color 'green))

(define color-set (enum-type->enum-set color))

(define reddish (list->enum-set
                 color
                 (map (lambda (name)
                        (enum-name->enum color name))
                      (take color-names 3))))

(define ~reddish (list->enum-set
                  color
                  (map (lambda (ord)
                         (enum-name->enum color ord))
                       (drop color-names 3))))

(define empty-colors (enum-empty-set color))

(define pizza-descriptions
  '((margherita "tomato and mozzarella")
    (funghi     "mushrooms")
    (bianca     "ricotta and mozzarella")
    (chicago    "deep-dish")
    (hawaiian   "pineapple and ham")))

(define pizza-names (map car pizza-descriptions))

(define pizza (make-enum-type pizza-descriptions))

(define pizza-chicago (enum-name->enum pizza 'chicago))
(define pizza-bianca (enum-name->enum pizza 'bianca))

;;;; Finders and enum accessors

;;; Later tests make heavy use of these, so test these first.

(test-group "Finders and accessors"
  (test 'red (enum-name (enum-name->enum color 'red)))
  (test 0 (enum-ordinal (enum-name->enum color 'red)))
  (test-assert (eqv? color (enum-type (enum-name->enum color 'red))))
  (test 'red (enum-name (enum-ordinal->enum color 0)))
  (test 0 (enum-ordinal (enum-ordinal->enum color 0)))
  (test-assert (eqv? color (enum-type (enum-ordinal->enum color 0))))
  (test-assert (eqv? (enum-name->enum color 'red) (enum-ordinal->enum color 0)))
  (test "deep-dish" (enum-value (enum-name->enum pizza 'chicago)))

  (test 0 (enum-name->ordinal color 'red))
  (test 6 (enum-name->ordinal color 'blue))
  (test "mushrooms" (enum-name->value pizza 'funghi))
  (test (enum-name->ordinal color 'blue) (enum-name->value color 'blue))
  (test 'red (enum-ordinal->name color 0))
  (test 'chicago (enum-ordinal->name pizza 3))
  (test "mushrooms" (enum-ordinal->value pizza 1))
  (test 6 (enum-ordinal->value color 6))
)

(test-group "Enum type constructors"
  ;; Mixing name and name+value args.
  (test-assert (enum-type?
                (make-enum-type
                 '(vanilla (chocolate 2) strawberry (pistachio 4))))))

;;;; Predicates

(test-group "Predicates"
  (test-assert (enum? color-red))
  (test-not (enum? 'z))     ; Ensure enums aren't just symbols.

  (test-assert (every (lambda (e) (enum-type-contains? color e))
                      (map (lambda (s)
                             (enum-name->enum color s))
                           color-names)))
  (test-not (any (lambda (e) (enum-type-contains? color e))
                 (map (lambda (s) (enum-name->enum pizza s)) pizza-names)))

  (test-assert (enum=? color-red (enum-ordinal->enum color 0)))
  (test-not    (enum=? color-red color-tangerine))
  (test-assert (enum=? color-red color-red color-red))
  (test-not    (enum=? color-red color-red color-tangerine))

  (test-assert (enum<? color-red color-tangerine))
  (test-not    (enum<? color-tangerine color-tangerine))
  (test-not    (enum<? color-tangerine color-red))
  (test-assert (enum<? color-red color-green color-blue))
  (test-not    (enum<? color-red color-blue color-blue))
  (test-not    (enum>? color-red color-tangerine))
  (test-not    (enum>? color-tangerine color-tangerine))
  (test-assert (enum>? color-tangerine color-red))
  (test-assert (enum>? color-blue color-green color-red))
  (test-not    (enum>? color-blue color-red color-red))
  (test-assert (enum<=? color-red color-tangerine))
  (test-assert (enum<=? color-tangerine color-tangerine))
  (test-not    (enum<=? color-tangerine color-red))
  (test-assert (enum<=? color-red color-blue color-blue))
  (test-not    (enum<=? color-blue color-blue color-red))
  (test-not    (enum>=? color-red color-tangerine))
  (test-assert (enum>=? color-tangerine color-tangerine))
  (test-assert (enum>=? color-tangerine color-red))
  (test-assert (enum>=? color-blue color-red color-red))
  (test-not    (enum>=? color-blue color-red color-blue))
)

;;;; Enum type accessors

(test-group "Enum type accessors"
  (test (length color-names) (enum-type-size color))
  (test (length pizza-names) (enum-type-size pizza))
  (test 'red (enum-name (enum-min color)))
  (test 'margherita (enum-name (enum-min pizza)))
  (test 'violet (enum-name (enum-max color)))
  (test 'hawaiian (enum-name (enum-max pizza)))

  (test (enum-type-size color) (length (enum-type-enums color)))
  (test-assert (equal? (map enum-name (enum-type-enums color)) color-names))
  (test-assert (equal? (map enum-ordinal (enum-type-enums color))
                       (iota (enum-type-size color))))
  (test-assert (equal? (map enum-value (enum-type-enums pizza))
                       (map cadr pizza-descriptions)))

  (test-assert (equal? (enum-type-names color) color-names))
  (test-assert (equal? (enum-type-names pizza) pizza-names))
  (test-assert (equal? (enum-type-values pizza)
                       (map cadr pizza-descriptions)))
  (test-assert (equal? (enum-type-values color)
                       (iota (enum-type-size color))))
)

(test-group "Enum operations"
  (test-assert (enum=? (enum-next color-red) color-tangerine))
  (test-assert (enum=? (enum-prev color-tangerine) color-red))
  (test-assert (enum=? (enum-next pizza-bianca) pizza-chicago))
  (test-assert (enum=? (enum-prev pizza-chicago) pizza-bianca))
  (test-not (enum-next (enum-max color))                  )
  (test-not (enum-prev (enum-min color))                  )
)

;;;; Enum comparators

(test-group "Enum comparators"
  (let ((pizza-comparator (make-enum-comparator pizza)))
    (test-assert (comparator? pizza-comparator))
    (test-assert (comparator-ordered? pizza-comparator))
    (test-assert (comparator-hashable? pizza-comparator))

    (test-assert (every (lambda (e) (comparator-test-type pizza-comparator e))
                        (enum-type-enums pizza)))
    (test-not (any (lambda (e) (comparator-test-type pizza-comparator e))
                   (enum-type-enums color)))

    (test-assert (=? pizza-comparator
                     pizza-chicago
                     (enum-name->enum pizza 'chicago)))

    (test-not    (=? pizza-comparator pizza-bianca pizza-chicago))
    (test-assert (<? pizza-comparator pizza-bianca pizza-chicago))
    (test-not    (<? pizza-comparator pizza-bianca pizza-bianca))
    (test-not    (<? pizza-comparator pizza-chicago pizza-bianca))
    (test-not    (>? pizza-comparator pizza-bianca pizza-chicago))
    (test-not    (>? pizza-comparator pizza-bianca pizza-bianca))
    (test-assert (>? pizza-comparator pizza-chicago pizza-bianca))
    (test-assert (<=? pizza-comparator pizza-bianca pizza-chicago))
    (test-assert (<=? pizza-comparator pizza-bianca pizza-bianca))
    (test-not    (<=? pizza-comparator pizza-chicago pizza-bianca))
    (test-not    (>=? pizza-comparator pizza-bianca pizza-chicago))
    (test-assert (>=? pizza-comparator pizza-bianca pizza-bianca))
    (test-assert (>=? pizza-comparator pizza-chicago pizza-bianca)))
)

(test-group "Basic enum set operations"
  ;; Ensure that an enum set created from an enum type with
  ;; enum-type->enum-set contains every enum of the original type.
  (test-assert (let ((pizza-set (enum-type->enum-set pizza)))
                 (every (lambda (enum)
                          (enum-set-contains? pizza-set enum))
                        (enum-type-enums pizza))))

  (test-assert (let ((pizza-set (list->enum-set pizza (enum-type-enums pizza))))
                 (every (lambda (enum)
                          (enum-set-contains? pizza-set enum))
                        (enum-type-enums pizza))))

  (test-assert (let ((pizza-set (apply enum-set pizza (enum-type-enums pizza))))
                 (every (lambda (enum) (enum-set-contains? pizza-set enum))
                        (enum-type-enums pizza))))

  (test-assert (enum-set-contains? (enum-set color color-red color-blue)
                                   color-red))
  (test-not (enum-set-contains? (enum-set color color-red color-blue)
                                color-tangerine))

  (test-assert (eqv? (enum-set-type color-set) color))
  (test-assert (eqv? (enum-set-type (enum-type->enum-set pizza)) pizza))

  (test-assert (enum-set-empty? (enum-empty-set pizza)))

  (test-assert (enum-set-empty? empty-colors))
  (test-not (enum-set-empty? color-set))

  (test-assert (enum-set=? (enum-set-projection color reddish) reddish))
  (let* ((color* (make-enum-type color-names))
         (reddish* (list->enum-set color*
                                   (map (lambda (name)
                                          (enum-name->enum color* name))
                                        (take color-names 3)))))
    (test-assert (enum-set=? (enum-set-projection color* reddish) reddish*)))

  (test-not (eqv? color-set (enum-set-copy color-set)))
)

;;;; Enum set predicates

(test-group "Enum set predicates"
  (test-assert (enum-set-disjoint? color-set empty-colors))
  (test-not    (enum-set-disjoint? color-set reddish))
  (test-assert (enum-set-disjoint? reddish ~reddish))

  ;;; comparisons

  (test-assert (enum-set=? color-set (enum-set-copy color-set)))

  (test-not    (enum-set=? color-set empty-colors))
  (test-assert (enum-set<? reddish color-set))
  (test-not    (enum-set<? color-set reddish))
  (test-not    (enum-set<? color-set color-set))
  (test-not    (enum-set>? reddish color-set))
  (test-assert (enum-set>? color-set reddish))
  (test-not    (enum-set>? color-set color-set))
  (test-assert (enum-set<=? reddish color-set))
  (test-not    (enum-set<=? color-set reddish))
  (test-assert (enum-set<=? color-set color-set))
  (test-not    (enum-set>=? reddish color-set))
  (test-assert (enum-set>=? color-set reddish))
  (test-assert (enum-set>=? color-set color-set))

  ;;; enum-set-subset?
  (test-assert (enum-set-subset? reddish color-set))
  (test-not    (enum-set-subset? color-set reddish))
  (test-assert (enum-set-subset? reddish reddish))
  (let ((color-set* (make-enumeration '(red green blue))))
    (test-assert (enum-set-subset? color-set* color-set))
    (test-not    (enum-set-subset? color-set color-set*)))

  ;;; any & every

  (test-assert (enum-set-any? (lambda (e) (eq? 'green (enum-name e)))
                              color-set))
  (test-not (enum-set-any? (lambda (e) (eq? 'mauve (enum-name e)))
                           color-set))
  (test-not (enum-set-any? never empty-colors))
  (test-not (enum-set-every? (lambda (e) (eq? 'green (enum-name e)))
                             color-set))
  (test-assert (enum-set-every? (lambda (e) (< (enum-ordinal e) 10))
                                color-set))
  (test-assert (enum-set-every? never empty-colors))
)

;;;; Enum set mutators

(test-group "Enum set mutators"
  (let ((reddish+green (enum-set-adjoin reddish color-green)))
    (test-assert (enum-set<? reddish reddish+green))
    (test-assert (enum-set-contains? reddish+green color-green)))

  (let ((reddish+green
         (enum-set-adjoin! (enum-set-copy reddish) color-green)))
    (test-assert (enum-set<? reddish reddish+green))
    (test-assert (enum-set-contains? reddish+green color-green)))

  (let ((reddish* (enum-set-delete reddish color-tangerine)))
    (test-assert (enum-set<? reddish* reddish))
    (test-not    (enum-set-contains? reddish* color-tangerine)))

  (let ((reddish* (enum-set-delete! (enum-set-copy reddish)
                                    color-tangerine)))
    (test-assert (enum-set<? reddish* reddish))
    (test-not    (enum-set-contains? reddish* color-tangerine)))

  (let ((reddish* (enum-set-delete-all reddish (list color-tangerine))))
    (test-assert (enum-set<? reddish* reddish))
    (test-not    (enum-set-contains? reddish* color-tangerine)))

  (let ((reddish** (enum-set-delete-all! (enum-set-copy reddish)
                                         (list color-tangerine))))
    (test-assert (enum-set<? reddish** reddish))
    (test-not    (enum-set-contains? reddish** color-tangerine)))

  (test-assert (enum-set-empty?
                (enum-set-delete-all! (enum-set-copy color-set)
                                      (enum-type-enums color))))
)

(test-group "Derived enum set operations"
  (test (length color-names) (enum-set-size color-set))
  (test 0 (enum-set-size empty-colors))

  (test-assert (equal? (enum-set->enum-list color-set) (enum-type-enums color)))
  (test-assert (null? (enum-set->enum-list empty-colors)))
  (test-assert (= (enum-set-size color-set)
                  (length (enum-set->enum-list color-set))))

  (test color-names (enum-set->list color-set))
  (test (map car pizza-descriptions)
        (enum-set->list (enum-type->enum-set pizza)))
  (test (enum-set-size color-set) (length (enum-set->enum-list color-set)))

  (test color-names (enum-set-map->list enum-name color-set))
  (test-assert (null? (enum-set-map->list enum-name empty-colors)))
  (test-assert (equal? (enum-set-map->list enum-name color-set)
                       (enum-set->list color-set)))

  (test 1 (enum-set-count (lambda (e) (enum=? e color-blue)) color-set))
  (test 0 (enum-set-count (lambda (e) (enum=? e color-blue)) reddish))
  (test (length pizza-descriptions)
        (enum-set-count (lambda (e) (string? (enum-value e)))
                        (enum-type->enum-set pizza)))

  ;;; filter & remove

  (test-assert (enum-set<? (enum-set-filter (lambda (e) (enum=? e color-red))
                                            color-set)
                           color-set))
  (test (filter (lambda (s) (eq? s 'red)) color-names)
        (enum-set-map->list enum-name
                            (enum-set-filter (lambda (e) (enum=? e color-red))
                                             color-set)))
  (test-assert (enum-set=? (enum-set-filter always color-set) color-set))
  (test-assert (enum-set-empty? (enum-set-filter never color-set)))
  (test-assert (enum-set<? (enum-set-remove (lambda (e) (enum=? e color-red))
                                            color-set)
                           color-set))
  (test (remove (lambda (s) (eq? s 'red)) color-names)
        (enum-set-map->list enum-name
                            (enum-set-remove (lambda (e) (enum=? e color-red))
                                             color-set)))
  (test-assert (enum-set=? (enum-set-remove never color-set) color-set))
  (test-assert (enum-set-empty? (enum-set-remove always color-set)))

  (test (length color-names)
        (let ((n 0))
          (enum-set-for-each (lambda (_)
                               (set! n (+ n 1)))
                             color-set)
          n))

  (test (reverse color-names)
        (enum-set-fold (lambda (enum lis)
                         (cons (enum-name enum) lis))
                       '()
                       color-set))

  (test-assert (enum-set=? color-set (enum-set-universe reddish)))

  (let* ((ds '(red yellow green))
         (us-traffic-light (make-enumeration ds))
         (light-type (enum-set-type us-traffic-light)))
    (test-assert (every (lambda (e) (enum-set-contains? us-traffic-light e))
                        (map (lambda (sym) (enum-name->enum light-type sym))
                             ds)))
    (test-assert (every (lambda (e) (eqv? (enum-name e) (enum-value e)))
                        (enum-set->enum-list us-traffic-light))))

  (let ((color-con (enum-set-constructor reddish)))
    (test-assert (eqv? (enum-set-type (color-con '(green))) color))
    (test-assert (enum-set=? (color-con color-names) color-set)))

  (test-assert (enum-set-member? 'red reddish))
  (test-not (enum-set-member? 'blue reddish))

  (let ((idx (enum-set-indexer reddish)))
    (test 0 (idx 'red))
    (test 4 (idx 'green))
    (test-not (idx 'margherita)))
)

(test-group "Enum set logical operations"
  (test-assert (enum-set=? color-set (enum-set-union reddish ~reddish)))
  (test-assert (enum-set-empty? (enum-set-intersection reddish ~reddish)))
  (test-assert (enum-set=? ~reddish (enum-set-difference color-set reddish)))
  (test-assert (enum-set=? color-set (enum-set-xor reddish ~reddish)))
  (test-assert (enum-set-empty? (enum-set-xor reddish reddish)))

  (test-assert (enum-set=? color-set
                           (fresh-sets enum-set-union! reddish ~reddish)))
  (test-assert (enum-set-empty?
                (fresh-sets enum-set-intersection! reddish ~reddish)))
  (test-assert
   (enum-set=? ~reddish
               (fresh-sets enum-set-difference! color-set reddish)))
  (test-assert
   (enum-set=? color-set
               (fresh-sets enum-set-xor! reddish ~reddish)))
  (test-assert (enum-set-empty?
                (fresh-sets enum-set-xor! reddish reddish)))

  (test-assert (enum-set-empty? (enum-set-complement color-set)))
  (test-assert (enum-set=? (enum-set-complement reddish) ~reddish))
  (test-assert (enum-set-empty?
                (enum-set-complement! (enum-set-copy color-set))))
  (test-assert (enum-set=?
                (enum-set-complement! (enum-set-copy reddish)) ~reddish))
)

(test-group "Syntax"
  (define-enum hobbit (frodo sam merry pippin) hobbit-set)
  (define-enumeration wizard (gandalf saruman radagast) wizard-set)

  (test 'merry (enum-name (hobbit merry)))
  (test-assert (enum-set? (hobbit-set)))
  (test-assert (enum-set-empty? (hobbit-set)))
  (test-assert (enum-set-contains? (hobbit-set merry pippin) (hobbit pippin)))

  (test 'radagast (wizard radagast))
  (test-assert (enum-set? (wizard-set)))
  (test-assert (enum-set-empty? (wizard-set)))
  (test-assert (enum-set-member? (wizard gandalf) (wizard-set saruman gandalf)))
)

(test-exit)
