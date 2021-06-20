(module (srfi 209)
  (enum-type? enum? enum-type-contains? enum=? enum<? enum>?
   enum<=? enum>=?

   make-enum-type

   enum-type enum-name enum-ordinal enum-value

   enum-name->enum enum-ordinal->enum enum-name->ordinal
   enum-name->value enum-ordinal->name enum-ordinal->value

   enum-type-size enum-min enum-max enum-type-enums
   enum-type-names enum-type-values

   enum-next enum-prev

   enum-type->enum-set enum-set list->enum-set enum-set-projection
   enum-set-copy enum-empty-set make-enumeration enum-set-universe
   enum-set-constructor enum-set-type enum-set-indexer

   enum-set? enum-set-contains? enum-set=? enum-set-member?
   enum-set-empty? enum-set-disjoint? enum-set<? enum-set>?
   enum-set<=? enum-set>=? enum-set-any? enum-set-every?
   enum-set-subset?

   enum-set-adjoin! enum-set-delete! enum-set-delete-all!
   enum-set-adjoin enum-set-delete enum-set-delete-all

   enum-set-size enum-set->list enum-set-map->list enum-set-for-each
   enum-set-filter enum-set-remove enum-set-count enum-set-fold
   enum-set->enum-list
   enum-set-filter! enum-set-remove!

   enum-set-union enum-set-intersection enum-set-difference
   enum-set-xor enum-set-complement enum-set-union!
   enum-set-intersection! enum-set-difference! enum-set-xor!
   enum-set-complement!

   make-enum-comparator

   define-enum define-enumeration
   )

  (import (scheme)
          (chicken base)
          (srfi 1)
          (only (srfi 69) make-hash-table hash-table-ref/default
                          hash-table-set!)
          (only (srfi 113) list->set set<=?)
          (srfi 128)
          (srfi 178)
          (srfi 145))

  ;; Missing from SRFI 69.
  (define (hash-table-unfold stop? mapper successor seed comp)
    (let ((res (make-hash-table #:test (comparator-equality-predicate comp)
                                #:hash (comparator-hash-function comp))))
      (let loop ((seed seed))
        (if (stop? seed)
            res
            (let-values (((k v) (mapper seed)))
              (hash-table-set! res k v)
              (loop (successor seed)))))))

  (include "209.scm"))
