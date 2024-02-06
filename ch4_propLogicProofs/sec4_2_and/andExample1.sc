// #Sireum #Logika
//@Logika: --manual --background type

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

@pure def andExample1(p: B, q: B, r: B): Unit = {
    Deduce(
        //@formatter:off
        (p & (q & r)) ⊢ (r & p)

             Proof(
                1 (p & (q & r))                 by Premise,
                2 (p)                           by AndE1(1),
                3 (q & r)                       by AndE2(1),
                4 (r)                           by AndE2(3),
                5 (r & p)                       by AndI(4, 2)
            )
        //@formatter:on
    )
}

/*
p ∧ (q ∧ r) ⊢ r ∧ p
{
    1. p ∧ (q ∧ r)          premise
    2. p                    AndE1(1)
    3. q ∧ r                AndE2(1)
    4. q                    AndE1(3)
    5. r                    AndE2(3)
    6. r ∧ p                AndI(5, 2)
}
*/
