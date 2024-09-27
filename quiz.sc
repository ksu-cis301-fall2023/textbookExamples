// #Sireum #Logika
//@Logika: --manual --background disabled
import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.pred._
import org.sireum.justification.natded.prop._

@pure def quiz1[T](P: T => B @pure, Q: T => B @pure): Unit = {
  //@formatter:off
  Deduce(
  (
    ∀ ((x: T) => P(x) __>: Q(x))
  )
   |-
   (
     (∀ ((x: T) => (!Q(x))) ) __>: (∀ ((x: T) => (!P(x))))
   )
    Proof(
      1 (  ∀ ((x: T) => P(x) __>: Q(x))                       ) by Premise,
      2 SubProof(
        3 Assume(  ∀ ((x: T) => !Q(x))  ),
        4 SubProof ( (a: T) => (
          5 (  !Q(a)                                       ) by AllE[T](3),
          6 SubProof(
            7 Assume (  P(a)  ),
            8 (  P(a) __>: Q(a)                               ) by AllE[T](1),
            9 (  Q(a)                                      ) by ImplyE(8, 7),
            10 (  F                                        ) by NegE(9, 5)
          ),
          11 (  !P(a)                                      ) by NegI(6),
        )),
        12 (  ∀ ((x: T) => !P(x))                          ) by AllI[T] (4)
      ),
      13 (  (∀ ((x: T) => !Q(x))) __>: (∀ ((x: T) => !P(x)))  ) by ImplyI(2)
  )
  )
  //@formatter:on
}


@pure def quiz2[T](P: T => B @pure, Q: T => B @pure): Unit = {
  //@formatter:off
  Deduce(
    (
      ∃ ((x: T) => !P(x) & !Q(x))
      )
      |-
      (
        ∃ ((x: T) => !(P(x) & Q(x)))
        )
      Proof(
        1 (  ∃ ((x: T) => !P(x) & !Q(x))         ) by Premise,
        2 Let ( (a: T) => SubProof(
          3 Assume(  !P(a) & !Q(a)  ),
          4 (  !P(a)                             ) by AndE1(3),
          5 (  !Q(a)                             ) by AndE2(3),
          6 SubProof(
            7 Assume(  P(a) & Q(a)  ),
            8 (  P(a)                            ) by AndE1(7),
            9 (  F                               ) by NegE(8, 4)
          ),
          10 (  !(P(a) & Q(a))                   ) by NegI(6),
          11 (  ∃( (x: T) => (!(P(x) & Q(x)) ))  ) by ExistsI[T](10) 
        )),
        12 (  ∃( (x: T) => !(P(x) & Q(x)) )      ) by ExistsE[T](1, 2)
      )
    )
  //@formatter:on
}