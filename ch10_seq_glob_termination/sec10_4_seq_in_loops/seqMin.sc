// #Sireum #Logika
//@Logika: --background save
import org.sireum._

def min(list: ZS): Z = {
  Contract(
    Requires (list.size >= 1),
    Ensures(
      ∀ (0 until list.size)(x => (Res[Z] <= list(x))),
      ∃ (0 until list.size)(x => (Res[Z] == list(x)))
    )
  )
    var small: Z = list(0)
    var i: Z = 1

    while (i < list.size) {
      Invariant(
        Modifies(i, small),
        i >= 1,
        i <= list.size,
        ∀ (0 until i)(x => (small <= list(x))),
        ∃ (0 until i)(x => (small == list(x)))
      )

      if (list(i) < small) {
        small = list(i)
      }

      i = i + 1
    }

    return small
}

////////////// Calling code ///////////////////

var test: ZS = ZS(8,1,0,10,9,2,0)
var testMin: Z = min(test)

assert(testMin == 0)
