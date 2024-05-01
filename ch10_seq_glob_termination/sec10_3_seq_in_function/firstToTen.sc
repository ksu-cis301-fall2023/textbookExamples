// #Sireum #Logika
//@Logika: --background save
import org.sireum._

def firstToTen(a: ZS): Unit = {  // Unit is like void in Java
  Contract(
    Requires(
      a.size > 0
    ),
    Modifies(a),           // documents a is modified
    Ensures(
      // note: In(a) is the value of a at procedure entry point
      a.size == In(a).size,
      a ≡ In(a)(0 ~> 10) // sequence update notation
    )
  )
  a(0) = 10
}