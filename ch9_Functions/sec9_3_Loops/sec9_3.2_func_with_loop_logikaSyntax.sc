// #Sireum #Logika
//@Logika: --background save
import org.sireum._
import org.sireum.justification._

 def mult(x: Z, y: Z): Z = {
  Contract(
    Requires(
      y >= 0
    ),
    Ensures(
      Res[Z] == x * y
    )
  )
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
  Deduce(
    //@formatter:off
    1  (!(count != y)) by Premise,
    2  (sum == count * x) by Premise,
    3  (count == y) by Algebra*(1),
    4  (sum == x * y) by Algebra*(2, 3)
    //@formatter:on
  )
  return sum
}
var one: Z = 3
var two: Z = 4
Deduce(
  //@formatter:off
  1  (two == 4) by Premise,
  2  (two >= 0) by Algebra*(1)
  //@formatter:on
)
var answer: Z = mult(one, two)
Deduce(
  //@formatter:off
  1  (one == 3) by Premise,
  2  (two == 4) by Premise,
  3  (answer == one * two) by Premise,
  4  (answer == 12) by Algebra*(1, 2, 3)
  //@formatter:on
)
assert(answer == 12)