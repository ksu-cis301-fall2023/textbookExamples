// #Sireum #Logika
//@Logika: --manual --background save
import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._
import org.sireum.justification.natded.pred._

@pure def sequent[T](x: T, S: T => B @pure, Pz: T => B @pure, D: T => B @pure): Unit = {
  Deduce((∀{ (x: T) => (S(x) __>: Pz(x)) }, ∀{ (x: T) => (Pz(x) __>: D(x)) }, ∀{ (x: T) => !D(x) })  ⊢  (∀{ (x: T) => !S(x) }) Proof(
    //@formatter:off
    1  (∀{ (x: T) => (S(x) __>: Pz(x)) }) by Premise,
    2  (∀{ (x: T) => (Pz(x) __>: D(x)) }) by Premise,
    3  (∀{ (x: T) => !D(x) }) by Premise,
    4  Let { (a: T) => SubProof(
      6  (S(a) __>: Pz(a)) by AllE[T](1),
      7  (Pz(a) __>: D(a)) by AllE[T](2),
      8  (!D(a)) by AllE[T](3),
      9  SubProof(
        10  Assume(S(a)),
        11  (Pz(a)) by ImplyE(6, 10),
        12  (D(a)) by ImplyE(7, 11),
        13  (F) by NegE(12, 8)
      ),
      14  (!S(a)) by NegI(9)
    )},
    15  (∀{ (x: T) => !S(x) }) by AllI[T](4)
    //@formatter:on
  ))
}