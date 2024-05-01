// #Sireum #Logika
//@Logika: --manual --background save
import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

 def findMax(x: Z, y: Z): Z = {
  Contract(
    Ensures(
      Res[Z] >= x,
      Res[Z] >= y,
      Res[Z] == x | Res[Z] == y
    )
  )
  var max: Z = 0
  Deduce(
    //@formatter:off
    1  (max == 0) by Premise
    //@formatter:on
  )
  if (x > y) {
    Deduce(
      //@formatter:off
      1  (max == 0) by Premise,
      2  (x > y) by Premise
      //@formatter:on
    )
    max = x
    Deduce(
      //@formatter:off
      1  (max == x) by Premise,
      2  (max >= x) by Algebra*(1),
      3  (x > y) by Premise,
      4  (max >= y) by Algebra*(1, 3)
      //@formatter:on
    )
  } else {
    Deduce(
      //@formatter:off
      1  (max == 0) by Premise,
      2  (!(x > y)) by Premise,
      3  (x <= y) by Algebra*(2)
      //@formatter:on
    )
    max = y
    Deduce(
      //@formatter:off
      1  (max == y) by Premise,
      2  (x <= y) by Premise,
      3  (max >= x) by Algebra*(1, 2),
      4  (max >= y) by Algebra*(1)
      //@formatter:on
    )
  }
  Deduce(
    //@formatter:off
    1  (max >= x) by Premise,
    2  (max >= y) by Premise,
    3  (max == x | max == y) by Premise
    //@formatter:on
  )
  return max
}
val num1: Z = 3
val num2: Z = 2
val biggest: Z = findMax(num1, num2)
Deduce(
  //@formatter:off
  1  (biggest >= num1) by Premise,
  2  (biggest >= num2) by Premise,
  3  (biggest == num1 | biggest == num2) by Premise,
  4  (num1 == 3) by Premise,
  5  (num2 == 2) by Premise,
  6  (biggest >= 3) by Algebra*(1, 4),
  7  (biggest >= 2) by Algebra*(2, 5),
  8  (biggest == 3 | biggest == num2) by Subst_<(4, 3),
  9  (biggest == 3 | biggest == 2) by Subst_<(5, 8),
  10  SubProof(
    11  Assume(biggest == 3)
  ),
  12  SubProof(
    13  Assume(biggest == 2),
    14  (!(biggest >= 3)) by Algebra*(13),
    15  (F) by NegE(6, 14),
    16  (biggest == 3) by BottomE(15)
  ),
  17  (biggest == 3) by OrE(9, 10, 12)
  //@formatter:on
)
assert(biggest == 3)