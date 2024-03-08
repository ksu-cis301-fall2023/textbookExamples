// #Sireum #Logika
//@Logika: --manual --background type

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

@pure def implies1(a: B, b: B, c: B): Unit = {
     Deduce(
          //@formatter:off
          (a ->: b,
          b ->: c)
          |-
               (a ->: c)

          Proof(
            1 (  a ->: b  ) by Premise,
            2 (  b ->: c  ) by Premise,
            3 SubProof(
              
            ),
            
          )
          //@formatter:on
     )
}