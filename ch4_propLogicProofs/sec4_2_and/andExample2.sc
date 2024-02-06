// #Sireum #Logika
//@Logika: --manual --background type

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

@pure def andExample2(p: B, q: B, r: B, a: B, t: B, s: B): Unit = {
    Deduce(
        //@formatter:off
        (p & q & r, a & (t | s)) ⊢ (q & (t | s))

             Proof(
                 1 (p & q & r)                      by Premise,
                 2 (a & (t | s))                    by Premise,
                 3 (p & q)                          by AndE1(1),
                 4 (r)                              by AndE2(1),
                 5 (a)                              by AndE1(2),
                6 (t | s)                           by AndE2(2),
                7 (p)                               by AndE1(3),
                8 (q)                               by AndE2(3),
                9 (q & (t | s))                     by AndI(8, 6)
        )
        //@formatter:on
    )
}