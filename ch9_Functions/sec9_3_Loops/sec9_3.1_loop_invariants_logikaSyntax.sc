// #Sireum #Logika
//@Logika: --manual --background save
import org.sireum._
import org.sireum.justification._

val x: Z = Z.read()
val y: Z = Z.read()
var sum: Z = 0
var count: Z = 0
Deduce(
  //@formatter:off
  1  (sum == 0) by Premise,
  2  (count == 0) by Premise,
  3  (sum == count * x) by Algebra*(1, 2)
  //@formatter:on
)
while (count != y) {
  Invariant(
    Modifies(sum, count),
    sum == count * x
  )
  Deduce(
    //@formatter:off
    1  (sum == count * x) by Premise
    //@formatter:on
  )
  sum = sum + x
  Deduce(
    //@formatter:off
    1  (sum == Old(sum) + x) by Premise,
    2  (Old(sum) == count * x) by Premise,
    3  (sum == count * x + x) by Algebra*(1, 2)
    //@formatter:on
  )
  count = count + 1
  Deduce(
    //@formatter:off
    1  (count == Old(count) + 1) by Premise,
    2  (sum == Old(count) * x + x) by Premise,
    3  (sum == (count - 1) * x + x) by Algebra*(1, 2),
    4  (sum == count * x - x + x) by Algebra*(3),
    5  (sum == count * x) by Algebra*(4)
    //@formatter:on
  )
}