// #Sireum #Logika
//@Logika: --manual --background save
import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.pred._

@pure def sequent[T](x: T, y: T, Human: T => B @pure): Unit = {
  Deduce((∃{ (x: T) => (Human(x)) })  ⊢  (∃{ (y: T) => (Human(y)) }) Proof(
    //@formatter:off
           1 (  ∃{ (x: T) => (Human(x)) }  ) by Premise,
           2 SubProof { (bob: T) => (
              3 Assume(  Human(bob)  ),
             
           ),
              4 (  CLAIM  ) by Premise},



    //@formatter:on
  ))
}