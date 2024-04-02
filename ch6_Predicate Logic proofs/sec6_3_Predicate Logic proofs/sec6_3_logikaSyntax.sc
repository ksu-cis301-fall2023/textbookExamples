// #Sireum #Logika
//@Logika: --manual --background save
import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.pred._

@pure def sequent[T](P: (T, T) => B @pure, bob: T): Unit = {
  Deduce(∀((x: T) => ∀((y: T) => P(x, y)))  ⊢  ∀((x: T) => ∀((y: T) => P(y, x))) Proof(
    //@formatter:off
    1  (∀((x: T) => ∀((y: T) => P(x, y)))) by Premise,

    //line 20 is just to test the AllE[T] rule with nested quantifiers
    20 ( ∀((y: T) => P(bob, y)))  by AllE[T](1),

    2 Let ( (a: T) => SubProof(
      3 Let ( (b: T) => SubProof(
        4 (   ∀((y: T) => P(b, y))  )   by AllE[T](1),
        5 (   P(b, a)               )   by AllE[T](4)
      )),
      6 (   ∀((y: T) => P(y, a))    )  by AllI[T](3)
    )),
    7 (   ∀((x: T) => ∀((y: T) => P(y, x))) ) by AllI[T](2)
    //@formatter:on
  ))
}