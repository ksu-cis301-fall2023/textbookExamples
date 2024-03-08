// #Sireum #Logika
//@Logika: --manual --background save
import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

val x: Z = 6
val y: Z = 6
val z: Z = 4

Deduce(
  //@formatter:off
  1  (x == 6) by Premise,
  2  (y == 6) by Premise,
  3  (z == 4) by Premise,
  4 (  x == y  ) by Algebra*(1,2),
  5 (  y > z  ) by Algebra*(2, 3),
  6 (  x == y & y > z  ) by AndI(4, 5)
  //@formatter:on
)
assert(x == y & y > z)