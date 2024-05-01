// #Sireum #Logika
//@Logika: --manual --background save
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
    ans = mult(x, y - 1)
    Deduce(
      //@formatter:off
      1  (ans == x * (y - 1)) by Premise,
      2  (ans == x * y - x) by Algebra*(1)
      //@formatter:on
    )


    ans = ans + x
    Deduce(
      //@formatter:off
      1  (Old(ans) == x * y - x) by Premise,
      2  (ans == Old(ans) + x) by Premise,
      3  (ans == x + x * y - x) by Algebra*(1, 2),
      4  (ans == x * y) by Algebra*(3)
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

//Suppose we want to test mult as follows:

Deduce(
    1 ( 2 >= 0 )             by Algebra*()     //proves the precondition
)

val times: Z = mult(4, 2)

Deduce(
    1 ( times == 4*2 )         by Premise,     //mult postcondition
    2 ( times == 8 )           by Algebra*(1)   //needed for the assert
)

assert(times == 8)
