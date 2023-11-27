// #Sireum #Logika
//@Logika: --manual --background save
import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._
import org.sireum.justification.natded.pred._

@pure def sequent[T](x: T, P: T => B @pure): Unit = {
  Deduce((!(∃{ (x: T) => P(x) }))  ⊢  (∀{ (x: T) => !P(x) }) Proof(
    //@formatter:off
    1  (!(∃{ (x: T) => P(x) })) by Premise,
    2  Let { (a: T) => SubProof(
      4  SubProof(
        5  Assume(P(a)),
        6  (∃{ (x: T) => P(x) }) by ExistsI[T](5),
        7  (F) by NegE(6, 1)
      ),
      8  (!P(a)) by NegI(4)
    )},
    9  (∀{ (x: T) => !P(x) }) by AllI[T](2)
    //@formatter:on
  ))
}


@pure def sequent[T](x: T, P: T => B @pure): Unit = {
   Deduce((∀{ (x: T) => !P(x) }) ⊢ (!(∃{ (x: T) => P(x) })) Proof(
      //@formatter:off
      1 (∀{ (x: T) => !P(x) }) by Premise,
      2 Let {}
)
}