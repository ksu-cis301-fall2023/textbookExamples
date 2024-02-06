// #Sireum #Logika
//@Logika: --manual --background type

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

@pure def not1(q: B): Unit = {
     Deduce(
          //@formatter:off
          (q, !q) ⊢ (F)

               Proof(
                    1 (q)               by Premise,
                    2 (!q)              by Premise,
                    3 (F)               by NegE(1, 2)
               )
          //@formatter:on
     )
}