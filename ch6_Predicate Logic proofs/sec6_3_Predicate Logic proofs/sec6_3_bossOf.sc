// #Sireum #Logika
//@Logika: --manual --background save
import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.pred._

@pure def sequent[T](IsBossOf: (T, T) => B @pure): Unit = {
  //@formatter:off
  Deduce(
    ∃((x: T) => ∀((y: T) => IsBossOf(x, y)))
  ⊢
    ∀((y: T) => ∃((x: T) => IsBossOf(x, y)))
  Proof(

    1 (   ∃((x: T) => ∀((y: T) => IsBossOf(x, y)))  )    by Premise,
    2 Let ( (b: T) => SubProof(
      4 Assume( ∀((y: T) => IsBossOf(a, y))),

      3 Let ( (a: T) => SubProof(

        5 ( IsBossOf(a, b)    )   by AllE[T](4),
        6 ( ∃((x: T) => IsBossOf(x, b)))  by ExistsI[T](5)
      )),
      7 (∃((x: T) => IsBossOf(x, b)))   by ExistsE[T](1, 3)
    )),
      8 (∀((y: T) => ∃((x: T) => IsBossOf(x, y))))  by AllI[T](2)
    )
  )
  //@formatter:on
}