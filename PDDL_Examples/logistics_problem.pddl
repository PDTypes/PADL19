;
; Logistics Problem 1: move the packages to office2
; 
; Author: Ron Petrick
;
; A simple logistics problem for the non-typed domain.
;
(define (problem logistics-problem1)
    (:domain logistics1)

    (:objects
        truck1 truck2 
        city1 city2 
        airplane1             
        airport1 airport2 
        package1 
        office1 office2  
    )

    (:init
        (package package1)

        (vehicle truck1)
        (vehicle truck2)
        (vehicle airplane1)

        (truck truck1)
        (truck truck2)
        (airplane airplane1)

        (city city1)
        (city city2)

        (location office1)
        (location office2)
        (location airport1)
        (location airport2)
        (airport airport1)
        (airport airport2)

        (inCity airport1 city1)
        (inCity airport2 city2)
        (inCity office1 city1)
        (inCity office2 city2)

        (isAt package1 office1)
        (isAt truck1 airport1)
        (isAt truck2 airport2)
        (isAt airplane1 airport1)
    )

    (:goal
            (isAt package1 office2)
    )
)
