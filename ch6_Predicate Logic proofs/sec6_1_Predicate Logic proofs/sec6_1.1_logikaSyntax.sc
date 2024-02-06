// #Sireum #Logika
//@Logika: --manual --background type
import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.pred._
import org.sireum.justification.natded.prop._


@pure def sequent[T](P: T => B @pure): Unit = {
  Deduce(
    //@formatter: off
    ∀{ (x: T) => P(x) }  ⊢  (∀{ (y: T) => P(y) })
    Proof(
      1  (∀{ (x: T) => P(x) })            by Premise,
      2  Let { (a: T) => SubProof(
        3  (P(a))                         by AllE[T](1)
      )},
      4  (∀{ (y: T) => P(y) })            by AllI[T](2)

    )
  //@formatter:on
  )
}
