// #Sireum #Logika
//@Logika: --manual --background save
import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

def div(a: Z, b: Z) : Z =  {
  Contract(
    Requires(   b != 0  ),
    Ensures(    Res[Z] == a/b   )
  )

  val ans: Z = a/b

  Deduce(
    1 ( b != 0      )   by Premise, //precondition (needed for division)
    2 ( ans == a/b  )   by Premise  //satisifes the postcondition
    //(from the "ans = a/b" assignment)
  )

  return ans
}

val x: Z = 10
val y: Z = 2

Deduce(
  1 ( x == 10     )   by Premise,     //from the "x = 10" assignment
  2 ( y == 2      )   by Premise,     //from the "y = 2" assignment
  3 ( y+1 != 0    )   by Algebra*(2)  //Yes! Satisfies the precondition for our second parameter (y+1)
)

val num: Z = div(x-1, y+1)

Deduce(
  1 ( num == (x-1)/(y+1)  )   by Premise,     //postcondition of div
  2 ( x == 10             )   by Premise,     //previous variable assignment
  3 ( y == 2              )   by Premise,     //previous variable assignment
  4 ( num == 9/3          )   by Algebra*(1,2,3),
5 ( num == 3            )   by Algebra*(4)  //needed for assert
)
assert(num == 3)