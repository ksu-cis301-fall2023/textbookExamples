// #Sireum #Logika
//@Logika: --background save
import org.sireum._
import org.sireum.justification._

var x: Z = 4
x = x + 1

var x: Z = 4
Deduce(
  //@formatter:off
  1  (x == 4) by Premise
  //@formatter:on
)
x = x + 1
Deduce(
  //@formatter:off
  1  (x == x + 1) by Premise,
  2  (x == 4) by Premise
  //@formatter:on
)
assert(x == 5)

var x: Z = 4
Deduce(
  //@formatter:off
  1  (x == 4) by Premise
  //@formatter:on
)
x = x + 1
Deduce(
  //@formatter:off
  1  (x == Old(x) + 1) by Premise,
  2  (Old(x) == 4) by Premise,
  3  (x == 4 + 1) by Subst_<(2, 1),
  4  (x == 5) by Algebra*(3)
  //@formatter:on
)
assert(x == 5)