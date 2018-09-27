;
; Blocksworld Problem 1: build a simple tower
;
; Author: Ron Petrick
;
; A set of blocks (a,b,c,d,e,f) is initially on a table.
; The planner should find a plan to stack the blocks so that
; a is on b, b is on c.
;
(define (problem blocksworld-problem1)
  (:domain blocksworld)

  (:objects
      a
      b
      c
  )

  (:init
      (onTable a)
      (onTable b)
      (onTable c)

      (clear a)
      (clear b)
      (clear c)

      (handEmpty)
  )

  (:goal
      (and
          (on a b)
          (on b c)
      )
  )
)
