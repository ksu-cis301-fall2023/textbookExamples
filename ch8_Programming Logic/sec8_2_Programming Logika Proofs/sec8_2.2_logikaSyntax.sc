// #Sireum #Logika
//@Logika: --background save
import org.sireum._

val num: Z = Z.prompt("Enter a number: ")
if (num > 0) {
  println(num, " is positive")
} else {
  println(num, " is negative (or zero)")
}