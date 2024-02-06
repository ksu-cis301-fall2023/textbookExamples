// #Sireum #Logika
//@Logika: --manual --background type
import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._
import org.sireum.justification.natded.pred._

/*
original proof:

∀ x isHealthy(x), ∀ y isHappy(y)  |-  ∀ z(isHealthy(z) ∧ isHappy(z))
{

  1. ∀ x isHealthy(x)                   premise
  2. ∀ y isHappy(y)                     premise
  3. {
       4. a
       5. isHealthy(a)                  ∀e 1 a
       6. isHappy(a)                    ∀e 2 a
       7. isHealthy(a) ∧ isHappy(a)     ∧i 5 6
  }
  8. ∀ z (isHealthy(z) ∧ isHappy(z))    ∀i 3
}

 */

@pure def healthyHappy[T](isHealthy: T => B @pure, isHappy: T => B @pure): Unit = {
     Deduce(
          //@formatter: off
          (
            ∀{(x: T) => isHealthy(x)},
            ∀{(y: T) => isHappy(y)}
          )
          ⊢
            (
              ∀{(z: T) => isHealthy(z) & isHappy(z)}
            )
          Proof (
               1 (∀{(x: T) => isHealthy(x)})                by Premise,
               2 (∀{(y: T) => isHappy(y)})                  by Premise,
               3 Let {(a: T) => SubProof(
                    4 (isHealthy(a))                          by AllE[T](1),
                    5 (isHappy(a))                          by AllE[T](2),
                    6 (isHealthy(a) & isHappy(a))           by AndI(4, 5)
               )},
               7 (∀{(z: T) => isHealthy(z) & isHappy(z)})   by AllI[T](3)
          )
          //@formatter: on
     )
}
