// #Sireum #Logika
//@Logika: --manual --background save
import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._


var x: Z = Z.read()
var y: Z = Z.read()
var max: Z = 0
if (x > y) {
  Deduce(
    //@formatter:off
    2 (  x > y  ) by Premise
    //@formatter:on
  )
  max = x
  Deduce(
    //@formatter:off
    1 (  max == x  ) by Premise,
    2 (  max >= x  ) by Algebra*(1),
    3 (  x > y     ) by Premise,
    4 (  max >= y  ) by Algebra*(1, 3)
    //@formatter:on
  )
} else {
  Deduce(
    //@formatter:off
    2 (  !(x > y)  ) by Premise,
    3 (  x <= y    ) by Algebra*(2)
    //@formatter:on
  )
  max = y
  Deduce(
    //@formatter:off
    1 (  max == y  ) by Premise,
    2 (  x <= y    ) by Premise,
    3 (  max >= x  ) by Algebra*(1, 2),
    4 (  max >= y  ) by Algebra*(1)
    //@formatter:on
  )
}
Deduce(
  1 (  max == x | max == y                            ) by Premise,
  2 (  max >= x                                       ) by Premise,
  3 (  max >= y                                       ) by Premise,
  4 (  max >= x & max >= y                            ) by AndI(2, 3),
  5 (  (max >= x & max >= y) & (max == x | max == y)  ) by AndI(4, 1)
)
assert((max >= x & max >= y) & (max == x | max == y))