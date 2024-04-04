// #Sireum #Logika
//@Logika: --manual --background save
import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._
import org.sireum.justification.natded.pred._

@pure def sequent[T](P: (T) => B @pure): Unit = {
  //@formatter:off
  Deduce(
    (
      !(∃((x: T) => P(x)))
    )
      ⊢
      (
        ∀((x: T) => !P(x))
        )
      Proof(
        1 (  !(∃((x: T) => P(x)))   ) by Premise,

        2 Let ( (a: T) => SubProof(
          3 SubProof(
            4 Assume (  P(a)  ),
            5 (  ∃((x: T) => P(x))  ) by ExistsI[T](3),
            6 (  F                  ) by NegE(4, 1)
          ),
          7 (  !P(a)                ) by NegI(3)
        )),
        8 (  ∀((x: T) => !P(x))     ) by AllI[T](2)

      )

      //@formatter:on
   )
}