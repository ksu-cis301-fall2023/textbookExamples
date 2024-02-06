// #Sireum #Logika
//@Logika: --manual --background type

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

@pure def and3(p: B, q: B): Unit = {
    Deduce(
        //@formatter:off
        (p & q) ⊢ (q)

             Proof(
             1 (p & q)              by Premise,
             2 (q)                  by AndE2(1)
        )
        //@formatter:on
    )
}