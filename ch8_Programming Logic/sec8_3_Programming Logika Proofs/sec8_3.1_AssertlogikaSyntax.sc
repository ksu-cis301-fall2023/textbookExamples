// #Sireum #Logika
//@Logika: --background save
import org.sireum._
import org.sireum.justification._

val x: Z = 6
val y: Z = 6
val z: Z = 4
assert(x == y & y > z)

val x: Z = 6
val y: Z = 6
val z: Z = 4
Deduce(
  //@formatter:off
  1  (x == 6) by Premise,
  2  (y == 6) by Premise,
  3  (z == 4) by Premise
  //@formatter:on
)
assert(x == y & y > z)