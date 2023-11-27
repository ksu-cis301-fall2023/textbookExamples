// #Sireum #Logika
//@Logika: --background save
import org.sireum._
import org.sireum.justification._

var x: Z = 6
var y: Z = x

var x: Z = 6
Deduce(
  //@formatter:off
  1  (x == 6) by Premise
  //@formatter:on
)
var y: Z = x
Deduce(
  //@formatter:off
  1  (y == x) by Premise
  //@formatter:on
)
assert(y == 6)

var x: Z = 6
Deduce(
  //@formatter:off
  1  (x == 6) by Premise
  //@formatter:on
)
var y: Z = x
Deduce(
  //@formatter:off
  1  (y == x) by Premise,
  2  (x == 6) by Premise,
  3  (y == 6) by Algebra*(1, 2)
  //@formatter:on
)
assert(y == 6)