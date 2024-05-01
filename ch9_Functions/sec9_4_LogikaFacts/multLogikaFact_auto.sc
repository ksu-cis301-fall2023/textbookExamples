// #Sireum #Logika
//@Logika: --manual --background save
import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._
import org.sireum.justification.natded.pred._

@spec def multFunction(m: Z, n: Z): Z = $

@spec def multFacts = Fact(
  ∀((x: Z) => multFunction(x, 0) == 0 ),
  ∀((x: Z) => ∀((y: Z) => (y > 1) __>: (multFunction(x, y) == multFunction(x,y-1))))
)

def mult(num1: Z, num2: Z): Z = {
  Contract(
    Requires(
      num2 >= 1
    ),
    Ensures(
      Res[Z] == multFunction(num1, num2)
    )
  )

  var answer: Z = 0
  var cur: Z = 0

  Deduce(
    1 (answer == 0) by Premise,
    2 (cur == 0)  by Premise,
    3 (∀((x: Z) => multFunction(x, 0) == 0 )) by ClaimOf(multFacts _),
    4 (multFunction(num1, 0) == 0) by AllE[Z](3),
    5 (answer == multFunction(num1, cur)) by Algebra*(1,2,4)
  )

  while (cur != num2) {
    Invariant(
      Modifies(cur, answer),
      answer == multFunction(num1, cur),
      cur >= 0
    )
    cur = cur + 1
    answer = answer + num1
  }

  return answer
}


