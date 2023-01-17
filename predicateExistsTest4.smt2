;; Solution: https://github.com/Z3Prover/z3/issues/341
;; Option 1:
;; (set-logic AUFLIA)
;; Option 2:
;; (check-sat-using smt)
;; Underlying problem: push disables simplifiers that are unsound in an incremental setting

;; Only a problem when mbqi is false
(set-option :smt.mbqi false)
(declare-sort P 0)
(declare-const someP P)

;; Makes a difference, hides unsat behind unknown... :(
(push)

(assert (not (exists ((otherP P))
    (= otherP someP)
    )))
(check-sat)
