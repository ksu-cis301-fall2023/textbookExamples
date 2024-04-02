// #Sireum #Logika
//@Logika: --manual --background save
import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.pred._

@pure def sequent[T](isHuman: T => B @pure, isMortal: T => B @pure): Unit = {
  Deduce(∀((h: T) => isHuman(h) __>: isMortal(h)), ∃((x: T) => isHuman(x))  ⊢  (∃{ (y: T) => (isMortal(y)) }) Proof(
    //@formatter:off
           1 (  ∃{ (x: T) => (Human(x)) }  ) by Premise,
           2 SubProof { (bob: T) => (
              3 Assume(  Human(bob)  ),

           )},



    //@formatter:on
  ))
}