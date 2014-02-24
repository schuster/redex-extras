#lang racket/base

(provide

 different? ; any any -> boolean
 ;; Returns #t if the two terms are different terms; #f if they are the same term

 dict-lookup ; ((any_key any_val) ...) any_key-target -> any_val or #f
 ;; Returns the first value associated with the given key in the given Redex alist, or #f if not found

 dict-extend ; ((any_key any_val) ...) (any_key any_val) ... -> ((any_key any_val) ...)
 ;; Extends the the given Redex alist with the given key-value pairs, such that the new pairs shadow
 ;; any existing ones. The additions are made from the left, such that mappings to the left are
 ;; shadowed by those to the right

 dict-append ; ((any_key any_val) ...) ... -> ((any_key any_val) ...)
 ;; Appends the given Redex alists together such that the pairs from later lists shadow pairs in
 ;; earlier ones

 apply-reduction-relation*/reachable ; reduction-relation term -> (term ...)
 ;; Produces all terms reachable in zero or more steps from t using reduction relation rel

 dict-set ; ((any_key any_val) ...) any_key any_val -> ((any_key any_val) ...)
 ;; Replaces the binding for the given key with the given value, or adds the binding if none exists

 filter-by-name ; ((any_1 any_2 ...) ...) (any_3 ...) -> ((any_4 any_5 ...) ...)
 ;; Given a list of tuples in which the first element is an identifier and a list of
 ;; identifiers, return the first list with only the elements whose identifiers are in the second
 ;; list
 )

;; ---------------------------------------------------------------------------------------------------

(require racket/match
         racket/set
         redex/reduction-semantics)

(define-language all-lang)

;; ---------------------------------------------------------------------------------------------------
;; Misc. helpers

(define-metafunction all-lang
  different? : any any -> boolean
  [(different? any any) #f]
  [(different? _ _) #t])

(module+ test
  (check-false (term (different? (a b c) (a b c))))
  (check-true (term (different? a (a))))
  (check-true (term (different? (a b c) (a b d)))))

;; ---------------------------------------------------------------------------------------------------
;; Dictionary operations

(define-metafunction
  all-lang
  dict-lookup : ((any_key any_val) ...) any_key-target -> any_val or #f
  [(dict-lookup () any_key) #f]
  [(dict-lookup ((any_key any_val) any_rest ...) any_key) any_val]
  [(dict-lookup ((any_other-key any_val) any_rest ...) any_key)
   (dict-lookup (any_rest ...) any_key)])

(define-metafunction
  all-lang
  dict-extend : ((any_key any_val) ...) (any_key2 any_val2) ... -> ((any_key any_val) ...)
  [(dict-extend (any_old-pairs ...) any_new-pairs ...) (any_new-reversed ... any_old-pairs ...)
   (where (any_new-reversed ...) ,(reverse (term (any_new-pairs ...))))])

(define-metafunction
  all-lang
  dict-set : ((any_key any_val) ...) any_key-target any_new-val -> ((any_key any_val) ...)
  [(dict-set (any_1 ... (any_key any_old-val) any_2 ...) any_key any_new-val)
   (any_1 ... (any_key any_new-val) any_2 ...)]
  [(dict-set (any_rest ...) any_key any_val)
   (any_rest ... (any_key any_val))])

(define-metafunction
  all-lang
  dict-append : ((any_key any_val) ...) ... -> ((any_key any_val) ...)
  [(dict-append any ...)
   (any_reversed ... ...)
   (where ((any_reversed ...) ...) ,(reverse (term (any ...))))])

(module+ test
  (require rackunit)

  (check-false (term (dict-lookup () 5)))
  (check-equal? (term (dict-lookup ((5 6) (7 8)) 5)) 6)
  (check-equal? (term (dict-lookup ((x 6) (y 7)) y)) 7)

  (check-equal? (term (dict-lookup (dict-extend ((x 4)) (x 3)) x)) 3)
  (check-equal? (term (dict-lookup (dict-extend ((x 4)) (y 3)) y)) 3)
  (check-equal? (term (dict-lookup (dict-extend ((x 4)) (y 3)) x)) 4)
  (check-equal? (term (dict-lookup (dict-extend () (y 3)) y)) 3)

  (check-equal? (term (dict-lookup (dict-append () ((y 3))) y)) 3)

  (define d (term (dict-extend () (a 1) (b 2) (c 3))))
  (define d2 (term (dict-extend () (a 4) (b 5) (d 6))))
  (define d3 (term (dict-append ,d ,d2)))
  (check-equal? (term (dict-lookup ,d3 a)) 4)
  (check-equal? (term (dict-lookup ,d3 b)) 5)
  (check-equal? (term (dict-lookup ,d3 c)) 3)
  (check-equal? (term (dict-lookup ,d3 d)) 6))

(define (apply-reduction-relation*/reachable rel t)
  (let loop ([worklist (list t)]
             [processed-terms (set)])
    (match worklist
      ['() (set->list processed-terms)]
      [(list next-term rest-worklist ...)
       (cond [(set-member? processed-terms next-term)
              (loop rest-worklist processed-terms)]
             [else (loop (append rest-worklist (apply-reduction-relation rel next-term))
                         (set-add processed-terms next-term))])])))

(module+ test
  (define-language number-lang
    (e natural
       (+ e e))
    (E hole
       (+ E e)
       (+ natural E)))

  (define math-step
    (reduction-relation number-lang
      (--> (in-hole E (+ natural_1 natural_2))
           (in-hole E ,(+ (term natural_1) (term natural_2))))))

  (define (list-same-elements? l1 l2)
    (set=? (list->set l1) (list->set l2)))

  (check list-same-elements?
         (apply-reduction-relation*/reachable math-step 42)
         (list 42))
  (check list-same-elements?
         (apply-reduction-relation*/reachable math-step '(+ 1 2))
         (list '(+ 1 2) 3))
  (check list-same-elements?
         (apply-reduction-relation*/reachable math-step '(+ (+ 1 2) (+ 3 4)))
         (list '(+ (+ 1 2) (+ 3 4)) '(+ 3 (+ 3 4)) '(+ 3 7) 10)))

;; ---------------------------------------------------------------------------------------------------
;; Filtering lists of name/value pairs

(define-metafunction all-lang
  filter-by-name : ((any_1 any_2 ...) ...) (any_3 ...) -> ((any_4 any_5 ...) ...)
  [(filter-by-name () any) ()]
  [(filter-by-name ((any_id any_body ...) any_rest ...) (any_1 ... any_id any_2 ...))
   ((any_id any_body ...) any_rest-results ...)
   (where (any_rest-results ...) (filter-by-name (any_rest ...) (any_1 ... any_id any_2 ...)))]
  [(filter-by-name (any_1 any_rest ...) (any_id ...))
   (filter-by-name (any_rest ...) (any_id ...))])

(module+ test
  (require rackunit)
  (check-equal? (term (filter-by-name ((a 1) (b 2) (c 3) (d 4)) ())) null)
  (check-equal? (term (filter-by-name ((a 1) (b 2) (c 3) (d 4)) (c d b a)))
               '((a 1) (b 2) (c 3) (d 4)))
  (check-equal? (term (filter-by-name ((a 1) (b 2) (c 3) (d 4)) (c d))) '((c 3) (d 4))))
