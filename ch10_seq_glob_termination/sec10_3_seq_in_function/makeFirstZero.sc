// #Sireum #Logika
//@Logika: --background save
import org.sireum._

def makeFirstZero(seq: ZS): Unit = {  // Unit is like void in Java
  Contract(
    Requires(
      seq.size > 0
    ),
    Modifies(seq),           // documents a is modified
    Ensures(
      // note: In(a) is the value of a at procedure entry point
      seq(0) == 0,
      ∀ (1 until seq.size)(x => ( seq(x) == In(seq)(x)))
    )
  )
  seq(0) = 0
}

//////////////// Test code //////////////

var nums: ZS = ZS(1,2,3)
makeFirstZero(nums)

assert(nums == ZS(0,2,3))