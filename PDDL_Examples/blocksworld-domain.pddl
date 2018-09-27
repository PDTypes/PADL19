;
; Domain: Blocksworld
;
; Author: Ron Petrick
;
; A robot with a single gripper can pick up blocks from a
; table or from the top of a stack and place blocks
; on the table or on another stack.
;
(define (domain blocksworld)
    (:requirements
        :strips
    )

    (:predicates
        (handEmpty)
        (holding ?x)
        (onTable ?x)
        (on ?x ?y)
        (clear ?x)
    )

(:action pickup_from_table
    :parameters
        (?x)
    :precondition
        (and
           (handEmpty)
           (onTable ?x)
           (clear ?x)
        )
    :effect
        (and
           (not (handEmpty))
           (not (onTable ?x))
           (holding ?x)
        )
)


(:action putdown_on_table
    :parameters
        (?x)
    :precondition
        (and
            (holding ?x)
        )
    :effect
        (and
            (not (holding ?x))
            (onTable ?x)
            (handEmpty)
        )
)


(:action pickup_from_stack
    :parameters
        (?x ?y)
    :precondition
        (and
            (on ?x ?y)
            (clear ?x)
            (handEmpty)
        )
    :effect
        (and
            (not (on ?x ?y))
            (not (handEmpty))
            (holding ?x)
            (clear ?y)
        )
)


(:action putdown_on_stack
    :parameters
        (?x ?y)
    :precondition
        (and
            (holding ?x)
            (clear ?y)
        )
    :effect
        (and
            (not (holding ?x))
            (not (clear ?y))
            (on ?x ?y)
            (handEmpty)
        )
)

)
