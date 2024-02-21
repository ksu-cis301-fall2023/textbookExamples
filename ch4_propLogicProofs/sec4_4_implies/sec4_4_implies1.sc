// #Sireum #Logika
//@Logika: --manual --background type

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

@pure def implies1(a: B, b: B, c: B): Unit = {
     Deduce(
          //@formatter:off
          (a __>: b,
          b __>: c)
          |-
               (a __>: c)

          Proof( //do ->
               1 (a __>: b) by Premise,
               2 (b __>: c) by Premise,
               3 SubProof(
                    4 Assume(a),
                    5 (b)     by ImplyE(1, 4),
                    6 (c)     by ImplyE(2, 5)
               ),
               7 (a ->: c)    by ImplyI(3)
          )
          //@formatter:on
     )
}