// #Sireum #Logika
//@Logika: --background save
import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

 def plusOne(n: Z): Z = {
  Contract(
    Requires(
      n >= 0
    ),
    Ensures(
      Res[Z] == n + 1,
      Res[Z] > 0
    )
  )
  val answer: Z = n + 1
  Deduce(
    //@formatter:off
    1  (n >= 0) by Premise,
    2  (answer == n + 1) by Premise,
    3  (answer > 0) by Algebra*(1, 2)
    //@formatter:on
  )
  return answer
}
var x: Z = 5
Deduce(
  //@formatter:off
  1  (x == 5) by Premise,
  2  (x >= 0) by Algebra*(1)
  //@formatter:on
)
var added: Z = plusOne(x)
Deduce(
  //@formatter:off
  1  (x == 5) by Premise,
  2  (added == x + 1) by Premise,
  3  (added > 0) by Premise,
  4  (added == 6) by Algebra*(1, 2),
  5  (added == 6 & added > 0) by AndI(4, 3)
  //@formatter:on
)
assert(added == 6 & added > 0)