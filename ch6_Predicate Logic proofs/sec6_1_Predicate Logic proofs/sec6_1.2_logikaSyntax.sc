// #Sireum #Logika
//@Logika: --manual --background save
import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._
import org.sireum.justification.natded.pred._

@pure def sequent[T](x: T, isStudent: T => B @pure, hasPhone: T => B @pure, hasLaptop: T => B @pure): Unit = {
  Deduce((∀{ (x: T) => (isStudent(x) __>: hasPhone(x) | hasLaptop(x)) }, ∀{ (x: T) => isStudent(x) })  ⊢  (∀{ (x: T) => (hasPhone(x) | hasLaptop(x)) }) Proof(
    //@formatter:off
    1  (∀{ (x: T) => (isStudent(x) __>: hasPhone(x) | hasLaptop(x)) }) by Premise,
    2  (∀{ (x: T) => isStudent(x) }) by Premise,
    3  Let { (bob: T) => SubProof(
      5  (isStudent(bob) __>: hasPhone(bob) | hasLaptop(bob)) by AllE[T](1),
      6  (isStudent(bob)) by AllE[T](2),
      7  (hasPhone(bob) | hasLaptop(bob)) by ImplyE(5, 6)
    )},
    8  (∀{ (x: T) => (hasPhone(x) | hasLaptop(x)) }) by AllI[T](3)
    //@formatter:on
  ))
}