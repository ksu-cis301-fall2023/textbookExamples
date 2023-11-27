// #Sireum #Logika
//@Logika: --manual --background save
import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.pred._

@pure def sequent[T](x: T, y: T, P: (T, T) => B @pure): Unit = {
  Deduce((∀{ (x: T) => ∀{ (y: T) => P(x, y) } })  ⊢  (∀{ (y: T) => ∀{ (x: T) => P(y, x) } }) Proof(
    //@formatter:off
    1  (∀{ (x: T) => ∀{ (y: T) => P(x, y) } }) by Premise,
    2  Let { (a: T) => SubProof(
      4  Let { (b: T) => SubProof(
        6  (∀{ (y: T) => P(a, y) }) by AllE[T](1),
        7  (P(a, b)) by AllE[T](6)
      )},
      8  (∀{ (x: T) => P(a, x) }) by AllI[T](4)
    )},
    9  (∀{ (y: T) => ∀{ (x: T) => P(y, x) } }) by AllI[T](2)
    //@formatter:on
  ))
}