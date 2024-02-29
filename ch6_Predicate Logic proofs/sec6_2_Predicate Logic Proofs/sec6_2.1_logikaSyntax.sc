// #Sireum #Logika
//@Logika: --manual --background save
import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.pred._

@pure def sequent[T](x: T, y: T, Human: T => B @pure): Unit = {
  Deduce((∃{ (x: T) => (Human(x)) })  ⊢  (∃{ (y: T) => (Human(y)) }) Proof(
    //@formatter:off


    //@formatter:on
  ))
}