// #Sireum #Logika
//@Logika: --background save
import org.sireum._

 def sumSequence(seq: ZS): Z = {
  var sum: Z = 0
  var i: Z = 0
  while (i < seq.size) {
    sum = sum + seq(i)
    i = i + 1
  }
  return sum
}
val list: ZS = ZS(1, 2, 3, 4)
val total: Z = sumSequence(list)
println("Sum of elements:", total)