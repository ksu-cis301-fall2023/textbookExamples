// #Sireum #Logika
//@Logika: --background save
import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

var num: Z = Z.read()
var orig: Z = num
if (num < 0) {
  num = num * -1
}

var num: Z = Z.read()
val orig: Z = num
Deduce(
  //@formatter:off
  1  (orig == num) by Premise,
  2  (num == orig) by Algebra*(1)
  //@formatter:on
)
if (num < 0) {
  num = num * -1
  Deduce(
    //@formatter:off
    1  (Old(num) < 0) by Premise,
    2  (num == Old(num) * -1) by Premise,
    3  (orig == Old(num)) by Premise,
    4  (num >= 0) by Algebra*(1, 2),
    5  (num == -1 * orig) by Algebra*(2, 3)
    //@formatter:on
  )
}
Deduce(
  //@formatter:off
  1  (num >= 0 | !(num < 0)) by Premise,
  2  (num == -1 * orig | num == orig) by Premise,
  3  SubProof(
    4  Assume(num >= 0)
  ),
  5  SubProof(
    6  Assume(!(num < 0)),
    7  (num >= 0) by Algebra*(6)
  ),
  8  (num >= 0) by OrE(1, 3, 5),
  9  (num >= 0 & (num == -1 * orig | num == orig)) by AndI(8, 2)
  //@formatter:on
)
assert(num >= 0 & (num == -1 * orig | num == orig))