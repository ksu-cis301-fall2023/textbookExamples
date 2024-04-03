// #Sireum #Logika
//@Logika: --manual --background save
import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.pred._

// A x A y (P(x, y) -> Q(x, y)), A x A y P(x, y) |- A x A y Q(x, y)
@pure def sequent[T](P: (T, T) => B @pure, Q: (T, T) => B @pure): Unit = {
  //@formatter:off
    Deduce(
    (
      ∀((x: T) => ∀((y: T) => (P(x, y) __>: Q(x, y)))),
      ∀((x: T) => ∀((y: T) => P(x, y)))
    )
    ⊢
    (
          ∀((x: T) => ∀((y: T) => Q(x, y)))
      )
      Proof(
        1 (  ∀( (x: T) => ∀( (y: T) => (P(x, y) __>: Q(x, y))))  ) by Premise,
        2 (  ∀( (x: T) => ∀( (y: T) => P(x, y)))              ) by Premise,

        3 Let ( (a: T) => SubProof(
          4 Let ( (b: T) => SubProof (
            5 (  ∀( (y: T) => (P(a, y) __>: Q(a, y)))            ) by AllE[T](1),
            6 (  P(a, b) __>: Q(a, b)                            ) by AllE[T](5),
            7 (  ∀( (y: T) => P(a, y))                        ) by AllE[T](2),
            8 (  Q(a, b)                                      ) by AllE[T](7)
          )),
          9 (  ∀((y: T) => Q(a, y))                           ) by AllI[T](4)
        )),
      10 (  ∀((x: T) => ∀((y: T) => Q(x, y)))                 ) by AllI[T](3)

    //@formatter:on
  ))
}