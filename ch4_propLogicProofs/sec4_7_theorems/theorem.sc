// #Sireum #Logika
//@Logika: --manual --background type

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

@pure def theorem(p: B, q: B): Unit = {
    Deduce(
        //@formatter:off
         ⊢ ((p __>: q) __>: ((!p __>: q) __>: q))
             Proof(
                1 SubProof(
                     2 Assume(p __>: q),
                     3 SubProof (
                         4 Assume(!p __>: q),
                         5 SubProof (
                             6 Assume !(p | !p),
                             7 SubProof (
                                  8 Assume p,
                                  9 (p | !p)            by OrI1(8),
                                  10 (F)                by NegE(9, 6),
                             ),
                             11 (!p)                    by NegI(7),
                             12 (p | !p)                by OrI2(11),
                             13 (F)                     by NegE(12, 6),
                         ),
                         14 (p | !p)                    by PbC(5),
                         15 SubProof (
                              16 Assume p,
                              17 (q)                    by ImplyE(2, 16),
                         ),
                         18 SubProof (
                              19 Assume !p,
                              20 (q)                    by ImplyE(4, 19),
                         ),
                         21 (q)                         by OrE(14, 15, 18),
                    ),
                    22 ((!p __>: q) __>: q)                     by ImplyI(3),
                ),
            23 ((p __>: q) __>: ((!p __>: q) __>: q))                     by ImplyI(1)
        )
        //@formatter:on
    )
}

//Suppose we wish to prove the following theorem of propositional logic:

//(p → q) → ((¬p → q) → q)
/*
⊢ (p → q) → ((¬p → q) → q)
{
    1. {
        2. p → q                        assume

        3. {
            4. ¬p → q                   assume

            //Begin LEM proof, p ∨ ¬p
            5. {
                6. ¬ (p ∨ ¬ p)          assume
                7. {
                    8. p                assume
                    9. p ∨ ¬ p          ∨i1 8
                    10. ⊥               ¬e 9 6
                }
                11.  ¬ p                ¬i 7
                12.  p ∨ ¬ p            ∨i2 11
                13.  ⊥                  ¬e 12 6
            }
            14. p ∨ ¬ p                 pbc 5

            //End LEM proof for p ∨ ¬p

            //use OR elimination on p ∨ ¬p, try to reach q
            15. {
                16. p               assume
                17. q               →e 2 16
            }
            18. {
                19. ¬ p             assume
                20. q               →e 4 19
            }
            21. q                   ∨e 14 15 18

            //goal: reach q
        }

        //use →i to conclude (¬p → q) → q
        22. (¬p → q) → q            →i 3

        //goal: reach (¬p → q) → q
    }
    //use →i to conclude (p → q) → ((¬p → q) → q)

    23. (p → q) → ((¬p → q) → q)    →i 1
}
*/


