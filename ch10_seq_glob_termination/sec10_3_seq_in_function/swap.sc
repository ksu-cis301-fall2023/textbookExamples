// #Sireum #Logika
//@Logika: --background save
import org.sireum._

// Given a sequence and two indices,
// swap the elements at the given indices.
def swap(list: ZS, pos1: Z, pos2: Z): Unit = {  // Unit is like void in Java
  Contract(
    Requires(
      0 <= pos1 & pos1 < list.size, // i is a valid index
      0 <= pos2 & pos2 < list.size  // j is a valid index
    ),
    Modifies(list),           // documents a is modified
    Ensures(
      // note: In(a) is the value of a at procedure entry point
      list(pos1) == In(list)(pos2),
      list(pos2) == In(list)(pos1),
      list.size == In(list).size,
      ∀ (0 until list.size)(x => (x != pos1 & x != pos2 __>: list(x) == In(list)(x)))
    )
  )
  val temp: Z = list(pos1)
  list(pos1) = list(pos2)
  list(pos2) = temp
}

//////////////// Test code //////////////

var testList: ZS = ZS(1,2,3,4)
swap(testList,0,3)

//the values in positions 0 and 3 should be swapped
//all other elements should be the same
assert(testList == ZS(4,2,3,1))