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
  var ans: Z = 0
  if (y > 0) {
    Deduce(
      //@formatter:off
      1  (y > 0) by Premise,
      2  (y - 1 >= 0) by Algebra*(1)
      //@formatter:on
    )
    var addRest: Z = mult(x, y - 1)
    Deduce(
      //@formatter:off
      1  (addRest == x * (y - 1)) by Premise,
      2  (addRest == x * y - x) by Algebra*(1)
      //@formatter:on
    )

     ans = x

       Deduce(
            //@formatter:off
            1 (ans == x)           by Premise
            //@formatter:on
       )

    ans = ans + addRest
    Deduce(
      //@formatter:off
      1  (addRest == x * y - x) by Premise,
      2  (ans == Old(ans) + addRest) by Premise,
      3  (Old(ans) == x)              by Premise,
      4  (ans == x + x * y - x) by Algebra*(1, 2, 3),
      5  (ans == x * y) by Algebra*(4)
      //@formatter:on
    )

  } else {
    Deduce(
      //@formatter:off
      1  (!(y > 0)) by Premise,
      2  (y >= 0) by Premise,
      3  (y == 0) by Algebra*(1, 2),
      4  (ans == 0) by Premise,
      5  (ans == x * y) by Algebra*(3, 4)
      //@formatter:on
    )
  }
  Deduce(
    //@formatter:off
    1  (ans == x * y) by Premise
    //@formatter:on
  )
  return ans
}