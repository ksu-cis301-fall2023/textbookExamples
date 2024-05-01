// #Sireum #Logika
//@Logika: --manual --background save
import org.sireum._
import org.sireum.justification._

var num: Z = Z.prompt("Enter positive number: ")
assume(num > 0)
val orig: Z = num
num = num * 2
Deduce(
  //@formatter:off
  1  (num == Old(num) * 2) by Premise,
  2  (orig == Old(num)) by Premise,
  3  (num == orig * 2) by Algebra*(1, 2),
  4  (2 != 0) by Algebra*(),
  5  (num % 2 == 0) by Algebra*(1)
  //@formatter:on
)
assert(num % 2 == 0)
num = num + 2
Deduce(
  //@formatter:off
  1  (num == Old(num) + 2) by Premise,
  2  (Old(num) % 2 == 0) by Premise,
  3  (num % 2 == 0) by Algebra*(1, 2),
  4  (Old(num) == orig * 2) by Premise,
  5  (num - 2 == orig * 2) by Algebra*(1, 4)
  //@formatter:on
)
assert(num % 2 == 0)
num = num / 2 - 1
Deduce(
  //@formatter:off
  1  (num == Old(num) / 2 - 1) by Premise,
  2  (Old(num) - 2 == orig * 2) by Premise,
  3  (Old(num) == orig * 2 + 2) by Algebra*(2),
  4  (num == (orig * 2 + 2) / 2 - 1) by Algebra*(1, 3),
  5  (num == orig + 1 - 1) by Algebra*(4),
  6  (num == orig) by Algebra*(5)
  //@formatter:on
)
assert(num == orig)

if (num == orig) {
  num = 2
}
else if (num < orig) {
  num = 4
}