// #Sireum #Logika
//@Logika: --manual --background save
import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.pred._

@pure def sequent[T](x: T, y: T, P: T => B @pure): Unit = {
  Deduce((∀{ (x: T) => P(x) })  ⊢  (∀{ (y: T) => P(y) }) Proof(
    //@formatter:off
    1  (∀{ (x: T) => P(x) }) by Premise,
    2  Let { (a: T) => SubProof(
      4  (P(a)) by AllE[T](1)
    )},
    5  (∀{ (y: T) => P(y) }) by AllI[T](2)
    //@formatter:on
  ))
}