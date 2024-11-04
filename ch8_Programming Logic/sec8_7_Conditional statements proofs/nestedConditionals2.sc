// #Sireum #Logika
//@Logika: --manual --background disabled
import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

var numWheels: Z = Z.read()
var numBikes: Z = Z.read()
var numCars: Z = Z.read()

val oldBikes: Z = numBikes
val oldCars: Z = numCars

//INVARIANT: numWheels == 2*numBikes + 4*numCars
assume(numWheels == numBikes*2 + numCars*4)

var addVehicle: Z = Z.prompt("Enter 1 to add a bike, and 2 to add a car: ")

if (addVehicle == 1) {
  numBikes = numBikes + 1

  Deduce(
    1 ( numWheels == Old(numBikes)*2 + numCars*4 ) by Premise,
    2 ( numBikes == Old(numBikes) + 1 ) by Premise,
    3 ( numWheels == numBikes*2 - 2 + numCars*4 ) by Algebra*(1, 2),
    4 ( oldBikes == Old(numBikes) ) by Premise,
    5 ( numBikes == oldBikes + 1 ) by Algebra*(2, 4)
  )

  numWheels = numWheels + 2

  Deduce(
    1 ( Old(numWheels) == numBikes*2 - 2 + numCars*4 ) by Premise,
    2 ( numWheels == Old(numWheels) + 2 ) by Premise,
    3 ( numWheels == numBikes*2 + numCars*4 ) by Algebra*(1, 2),
    4 ( addVehicle == 1) by Premise,
    5 ( numBikes == oldBikes + 1 ) by Premise,
    6 ( addVehicle != 2 ) by Algebra*(4),
    7 ( addVehicle != 2 | numCars == oldCars + 1 ) by OrI1(6)
  )

} else {
  if (addVehicle == 2) {
    numCars = numCars + 1

    Deduce(
      1 ( numWheels == numBikes*2 + Old(numCars)*4 ) by Premise,
      2 ( numCars == Old(numCars) + 1 ) by Premise,
      3 ( numWheels == numBikes*2 + numCars*4 - 4) by Algebra*(1, 2),
      4 ( oldCars == Old(numCars) ) by Premise,
      5 ( numCars == oldCars + 1 ) by Algebra*(2, 4)
    )

    numWheels = numWheels + 4

    Deduce(
      1 ( addVehicle == 2 ) by Premise,
      2 ( numWheels == Old(numWheels) + 4 ) by Premise,
      3 ( Old(numWheels) == numBikes*2 + numCars*4 - 4 ) by Premise,
      4 ( numWheels == numBikes*2 + numCars*4 ) by Algebra*(2, 3),
      5 ( numCars == oldCars + 1 ) by Premise,
      6 ( addVehicle != 1 ) by Algebra*(1),
      7 ( addVehicle != 1 | numBikes == oldBikes + 1 ) by OrI1(6)
    )
  } else {
    println("Error: input should be 1 or 2")

    Deduce(
      1 ( !(addVehicle == 1) ) by Premise,
      2 ( !(addVehicle == 2) ) by Premise,
      3 ( numWheels == numBikes*2 + numCars* 4 ) by Premise,
      4 ( oldCars == numCars ) by Premise,
      5 ( oldBikes == numBikes ) by Premise,
      6 ( addVehicle != 1 ) by Algebra*(1),
      7 ( addVehicle != 2 ) by Algebra*(2)
    )
  }

  Deduce(
    1 ( numWheels == numBikes*2 + numCars*4 ) by Premise,
    2 ( addVehicle != 1 ) by Premise,
    3 ( numCars == oldCars + 1 | addVehicle!= 2) by Premise,
    4 ( addVehicle != 1 | numBikes == oldBikes + 1 ) by OrI1(2),
    5 SubProof(
      6 Assume(numCars == oldCars + 1),
      7 ( addVehicle != 2 | numCars == oldCars + 1 ) by OrI2(6)
    ),
    8 SubProof(
      9 Assume(addVehicle!= 2),
      10 (addVehicle != 2 | numCars == oldCars + 1) by OrI1(9)
    ),
    11 (addVehicle != 2 | numCars == oldCars + 1) by OrE(3, 5, 8)
  )
}

Deduce(
  1 ( numWheels == numBikes*2 + numCars*4 ) by Premise,
  2 ( addVehicle != 2 | numCars == oldCars + 1 ) by Premise,
  3 ( numBikes == oldBikes + 1 | addVehicle != 1 ) by Premise,
  4 ( addVehicle != 1 | numBikes == oldBikes + 1 ) by Premise,
  5 ( addVehicle != 2 | numCars == oldCars + 1 ) by Premise
)

//invariant still holds
assert(numWheels == numBikes*2 + numCars*4)

//either they didn't select to add a bike, or I now have one more bike
assert(addVehicle != 1 | numBikes == oldBikes + 1)

//either they didn't select to add a car, or I now have one more car
assert(addVehicle != 2 | numCars == oldCars + 1)
