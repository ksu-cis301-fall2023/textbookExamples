// #Sireum #Logika
//@Logika: --background save
import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._
import org.sireum.justification.natded.pred._

/* The following should be hand-translated as a @strictpure method (with halt for non-total function):
  def factDef(n: Z): Z
*/
@spec def fOne = Fact(factDef(1) == 1)
@spec def fBig = Fact(∀{ (x: Z) => x > 1 __>: factDef(x) == factDef(x - 1) * x })
 def factorial(n: Z): Z = {
  Contract(
    Requires(
      n >= 1
    ),
    Ensures(
      Res[Z] == factDef(n)
    )
  )
  var i: Z = 1
  var product: Z = 1
  Deduce(
    //@formatter:off
    1  (i == 1) by Premise,
    2  (product == 1) by Premise,
    3  (factDef(1) == 1) by ClaimOf(fOne),
    4  (product == factDef(i)) by Algebra*(1, 2, 3),
    5  (i >= 1) by Algebra*(1)
    //@formatter:on
  )
  while (i != n) {
    Invariant(
      Modifies(i, product),
      product == factDef(i),
      i >= 1
    )
    i = i + 1
    Deduce(
      //@formatter:off
      1  (i == Old(i) + 1) by Premise,
      2  (product == factDef(Old(i))) by Premise,
      3  (product == factDef(i - 1)) by Algebra*(1, 2),
      4  (Old(i) >= 1) by Premise,
      5  (i > 1) by Algebra*(1, 4)
      //@formatter:on
    )
    product = product * i
    Deduce(
      //@formatter:off
      1  (product == Old(product) * i) by Premise,
      2  (Old(product) == factDef(i - 1)) by Premise,
      3  (∀{ (x: Z) => x > 1 __>: factDef(x) == factDef(x - 1) * x }) by ClaimOf(fBig),
      4  (i > 1 __>: factDef(i) == factDef(i - 1) * i) by AllE[T](3),
      5  (i > 1) by Premise,
      6  (factDef(i) == factDef(i - 1) * i) by ImplyE(4, 5),
      7  (product == factDef(i - 1) * i) by Algebra*(1, 2),
      8  (product == factDef(i)) by Algebra*(6, 7),
      9  (i >= 1) by Algebra*(5)
      //@formatter:on
    )
  }
  Deduce(
    //@formatter:off
    1  (product == factDef(i)) by Premise,
    2  (!(i != n)) by Premise,
    3  (i == n) by Algebra*(2),
    4  (product == factDef(n)) by Algebra*(1, 3)
    //@formatter:on
  )
  return product
}
var num: Z = 2
Deduce(
  //@formatter:off
  1  (num == 2) by Premise,
  2  (num >= 1) by Algebra*(1)
  //@formatter:on
)
var answer: Z = factorial(num)
Deduce(
  //@formatter:off
  1  (answer == factDef(num)) by Premise,
  2  (num == 2) by Premise,
  3  (answer == factDef(2)) by Algebra*(1, 2),
  4  (∀{ (x: Z) => x > 1 __>: factDef(x) == factDef(x - 1) * x }) by ClaimOf(fBig),
  5  (2 > 1 __>: factDef(2) == factDef(2 - 1) * 2) by AllE[T](4),
  6  (2 > 1) by Algebra T,
  7  (factDef(2) == factDef(2 - 1) * 2) by ImplyE(5, 6),
  8  (factDef(1) == 1) by ClaimOf(fOne),
  9  (factDef(2) == factDef(1) * 2) by Algebra*(7),
  10  (factDef(2) == 2) by Algebra*(8, 9),
  11  (answer == 2) by Algebra*(1, 2, 10)
  //@formatter:on
)
assert(answer == 2)