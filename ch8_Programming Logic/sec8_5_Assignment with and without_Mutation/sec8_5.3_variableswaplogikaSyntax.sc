// #Sireum #Logika
//@Logika: --background save
import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

var x: Z = Z.read()
var y: Z = Z.read()
val temp: Z = x
x = y
y = temp

var x: Z = Z.read()
var y: Z = Z.read()
val xOrig: Z = x
val yOrig: Z = y
Deduce(
  //@formatter:off
  1  (xOrig == x) by Premise,
  2  (yOrig == y) by Premise
  //@formatter:on
)
val temp: Z = x
x = y
Deduce(
  //@formatter:off
  1  (x == y) by Premise,
  2  (temp == Old(x)) by Premise,
  3  (xOrig == Old(x)) by Premise,
  4  (yOrig == y) by Premise,
  5  (temp == xOrig) by Algebra*(2, 3),
  6  (x == yOrig) by Algebra*(1, 4)
  //@formatter:on
)
y = temp
Deduce(
  //@formatter:off
  1  (y == temp) by Premise,
  2  (temp == xOrig) by Premise,
  3  (yOrig == Old(y)) by Premise,
  4  (y == xOrig) by Algebra*(1, 2),
  5  (x == yOrig) by Premise,
  6  (x == yOrig & y == xOrig) by AndI(5, 4)
  //@formatter:on
)
assert(x == yOrig & y == xOrig)