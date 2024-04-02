// #Sireum #Logika
//@Logika: --manual --background save
import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.pred._
import org.sireum.justification.natded.prop._


@pure def socMortal[T](isHuman: T => B @pure, isMortal: T => B @pure, Socrates: T): Unit = {
  Deduce (
    //@formatter: off
    (∀((x: T) => (isHuman(x) __>: isMortal(x))), isHuman(Socrates)) |- (isMortal(Socrates))
    Proof(
      1 (     ∀ ((x: T) => (isHuman(x) __>: isMortal(x)))      )   by Premise,
      2 (     isHuman(Socrates)                           )   by Premise,
      3 (     isHuman(Socrates) __>: isMortal(Socrates)      )   by AllE[T](1),
      4 (     isMortal(Socrates)                          )   by ImplyE(3, 2)
    )
    //@formatter: on
  )
}