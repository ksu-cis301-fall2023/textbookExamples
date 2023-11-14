// #Sireum #Logika
//@Logika: --background save
import org.sireum._
import org.sireum.justification._

var a: Z = Z.read()
assume(a > 0)
Deduce(
  //@formatter:off
  1  (a > 0) by Premise
  //@formatter:on
)
var a: Z = Z.read()
assume(a != 0)
Deduce(
  //@formatter:off
  1  (a != 0) by Premise
  //@formatter:on
)
var b: Z = 20 / a

var a: Z = Z.read()
var b: Z = 0
if (a != 0) {
  b = 20 / a
}