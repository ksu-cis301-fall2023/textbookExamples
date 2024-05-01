// #Sireum #Logika
//@Logika: --manual --background save
import org.sireum._
import org.sireum.justification._

Deduce(
  //@formatter:off
  1  (2 != 0) by Algebra*(),
  //@formatter:on
)

var x: Z = 10 / 2

var y: Z = Z.read()

Deduce(
  //@formatter:off
  1 ( -3 != 0)  by Algebra*()
  //@formatter:on
)

x = y % -3
