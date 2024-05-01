// #Sireum #Logika
//@Logika: --manual --background save
import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._
import org.sireum.justification.natded.pred._

@pure def sequent[T](x: T, Adult: T => B @pure, Kid: T => B @pure): Unit = {
  Deduce((∃{ (x: T) => (Adult(x) | Kid(x)) })  ⊢  ((∃{ (x: T) => Adult(x) }) | (∃{ (x: T) => Kid(x) })) Proof(

    1 (  ∃{ (x: T) => (Adult(x) | Kid(x)) }                        ) by Premise,
    2  Let { (alice: T) => SubProof(
      3  Assume(  Adult(alice) | Kid(alice)  ),
      4  SubProof(
        5  Assume(  Adult(alice)  ),
        6 (  ∃{ (x: T) => Adult(x) }                               ) by ExistsI[T](5),
        7 (  (∃{ (x: T) => Adult(x) }) | (∃{ (x: T) => Kid(x) })   ) by OrI1(6)
      ),
      8  SubProof(
        9  Assume(  Kid(alice)  ),
        10 (  ∃{ (x: T) => Kid(x) }                                ) by ExistsI[T](9),
        11 (  (∃{ (x: T) => Adult(x) }) | (∃{ (x: T) => Kid(x) })  ) by OrI2(10)
      ),
      12 (  (∃{ (x: T) => Adult(x) }) | (∃{ (x: T) => Kid(x) })    ) by OrE(3, 4, 8)
    )},
    13 (  (∃{ (x: T) => Adult(x) }) | (∃{ (x: T) => Kid(x) })      ) by ExistsE[T](1, 2)

  ))
}