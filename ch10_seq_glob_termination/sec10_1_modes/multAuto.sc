// #Sireum #Logika
//@Logika: --background save
import org.sireum._

def mult(m: Z, n: Z): Z = {
  Contract(
    Requires(m >= 0 & n >= 0),
    Ensures(Res[Z] == m * n)
  )

  var r: Z = 0
  var i: Z = 0

  while (i != n) {
    Invariant(
      Modifies(r, i),
      r == m * i
    )

    r = r + m
    i = i + 1
  }

  return r
}

//////////// Test code //////////////

var one: Z = 3
var two: Z = 4

var answer: Z = mult(one, two)
assert(answer == 12)