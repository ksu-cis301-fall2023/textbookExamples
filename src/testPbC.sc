// #Sireum #Logika
//@Logika: --manual --background disabled

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

@pure def bad(p: B, q: B): Unit = {
  Deduce(
    //@formatter: off

    ( q ) |- ( !p )
      Proof(
      2 (  q                 ) by Premise,
      3 SubProof(
        4 Assume (  !q  ),
        6 (  F             ) by NegE(2, 4)
      ),
      7 (  !p                ) by PbC(3)
    )
    //@formatter:on
  )
}