// #Sireum #Logika
//@Logika: --manual --background save
import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._
import org.sireum.justification.natded.pred._

/* The following should be hand-translated as a @strictpure method (with halt for non-total function):
  def factDef(n: Z): Z
*/
@spec def factFunction(n: Z): Z = $

@spec def factorialFacts = Fact(
  factFunction(1) == 1,
  ∀((x: Z) => (x > 1) __>: (factFunction(x) == factFunction(x-1)*x))
)


 def factorial(n: Z): Z = {
  Contract(
    Requires(
      n >= 1
    ),
    Ensures(
      Res[Z] == factFunction(n)
    )
  )
  var i: Z = 1
  var product: Z = 1
  Deduce(
    //@formatter:off
    1 (  i == 1                      ) by Premise,
    2 (  product == 1                ) by Premise,
    3 (  factFunction(1) == 1        ) by ClaimOf(factorialFacts _),
    4 (  product == factFunction(i)  ) by Algebra*(1, 2, 3),
    5 (  i >= 1                      ) by Algebra*(1)
    //@formatter:on
  )
  while (i != n) {
    Invariant(
      Modifies(i, product),
      product == factFunction(i),
      i >= 1
    )
    i = i + 1
    Deduce(
      //@formatter:off
      1 (  i == Old(i) + 1                  ) by Premise,
      2 (  product == factFunction(Old(i))  ) by Premise,
      3 (  product == factFunction(i - 1)   ) by Algebra*(1, 2),
      4 (  Old(i) >= 1                      ) by Premise,
      5 (  i > 1                            ) by Algebra*(1, 4)
      //@formatter:on
    )
    product = product * i
    Deduce(
      //@formatter:off
      1 (  product == Old(product) * i                                        ) by Premise,
      2 (  Old(product) == factFunction(i - 1)                                ) by Premise,
      3 (  ∀( (x: Z) => x > 1 __>: factFunction(x) == factFunction(x - 1) * x )  ) by ClaimOf(factorialFacts _),
      4 (  i > 1 __>: factFunction(i) == factFunction(i - 1) * i                 ) by AllE[Z](3),
      5 (  i > 1                                                              ) by Premise,
      6 (  factFunction(i) == factFunction(i - 1) * i                         ) by ImplyE(4, 5),
      7 (  product == factFunction(i - 1) * i                                 ) by Algebra*(1, 2),
      8 (  product == factFunction(i)                                         ) by Algebra*(6, 7),
      9 (  i >= 1                                                             ) by Algebra*(5)
      //@formatter:on
    )
  }
  Deduce(
    //@formatter:off
    1 (  product == factFunction(i)  ) by Premise,
    2 (  !(i != n)                   ) by Premise,
    3 (  i == n                      ) by Algebra*(2),
    4 (  product == factFunction(n)  ) by Algebra*(1, 3)
    //@formatter:on
  )
  return product
}
var num: Z = 2
Deduce(
  //@formatter:off
  1 (  num == 2  ) by Premise,
  2 (  num >= 1  ) by Algebra*(1)
  //@formatter:on
)
var answer: Z = factorial(num)
Deduce(
  //@formatter:off
  1 (  answer == factFunction(num)                                        ) by Premise,
  2 (  num == 2                                                           ) by Premise,
  3 (  answer == factFunction(2)                                          ) by Algebra*(1, 2),
  4 (  ∀( (x: Z) => x > 1 __>: factFunction(x) == factFunction(x - 1) * x )  ) by ClaimOf(factorialFacts _),
  5 (  2 > 1 __>: factFunction(2) == factFunction(2 - 1) * 2                 ) by AllE[Z](4),
  6 (  2 > 1                                                              ) by Algebra*(),
  7 (  factFunction(2) == factFunction(2 - 1) * 2                         ) by ImplyE(5, 6),
  8 (  factFunction(1) == 1                                               ) by ClaimOf(factorialFacts _),
  9 (  factFunction(2) == factFunction(1) * 2                             ) by Algebra*(7),
  10 (  factFunction(2) == 2                                              ) by Algebra*(8, 9),
  11 (  answer == 2                                                       ) by Algebra*(1, 2, 10)
  //@formatter:on
)
assert(answer == 2)