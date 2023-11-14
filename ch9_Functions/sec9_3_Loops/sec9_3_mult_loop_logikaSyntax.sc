// #Sireum #Logika
//@Logika: --background save
import org.sireum._

val x: Z = Z.read()
val y: Z = Z.read()
var sum: Z = 0
var count: Z = 0
while (count != y) {
  sum = sum + x
  count = count + 1
}

val x: Z = Z.read()
val y: Z = Z.read()
var sum: Z = 0
var count: Z = 0
while (count != y) {
  Invariant(
    Modifies(sum, count),
    sum == count * x
  )
  sum = sum + x
  count = count + 1
}