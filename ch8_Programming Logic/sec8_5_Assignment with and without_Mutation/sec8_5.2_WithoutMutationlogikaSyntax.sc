// #Sireum #Logika
//@Logika: --background save
import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

val x: Z = 4

val y: Z = x + 2

val z: Z = 10 - x

Deduce(
  //@formatter:off

  1 (     x == 4          )   by Premise,     //assignment of unchanged variable
  2 (     y == x + 2      )   by Premise,     //assignment of unchanged variable
  3 (     z == 10 - x     )   by Premise,     //assignment of unchanged variable
  4 (     y == 4 + 2      )   by Subst_<(1, 2),
  5 (     z == 10 - 4     )   by Subst_<(1, 3),
  6 (     y == 6          )   by Algebra*(4),
  7 (     z == 6          )   by Algebra*(5),
  8 (     y == z          )   by Subst_>(7, 6),
  9 (     y == z & y == 6 )   by AndI(8, 6)

  //@formatter:on
)

//now the assert will hold
assert(y == z & y == 6)