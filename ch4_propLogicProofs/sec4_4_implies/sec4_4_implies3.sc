// #Sireum #Logika
//@Logika: --manual --background type

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

@pure def implies3(p: B, q: B, r: B): Unit = {
  Deduce(
    //@formatter:off
    (p __>: r, q __>: r) ⊢ ((p | q) __>: r)
      Proof(
      1 (  p __>: r             ) by Premise,
      2 (  q __>: r             ) by Premise,
      3 SubProof(
        //assume p ∨ q, try to get to r

        4 Assume(  p | q  ),

        //nested subproof for OR elimination on p ∨ q
        //try to get to r in both cases

        5 SubProof(
          6 Assume(  p  ),
          7 (  r             ) by ImplyE(1, 6)
        ),
        8 SubProof(
          9 Assume(  q  ),
          10 (  r            ) by ImplyE(2, 9)
        ),
        11 (  r              ) by OrE(4, 5, 8)

        //goal: get to r
      ),

      //use ImplyI to conclude (p ∨ q) →: r
      12 (  (p | q) __>: r      ) by ImplyI(3)
    )
    //@formatter:on
  )
}