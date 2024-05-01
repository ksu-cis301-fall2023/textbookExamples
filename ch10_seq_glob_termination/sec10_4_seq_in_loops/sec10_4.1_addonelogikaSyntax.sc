// #Sireum #Logika
//@Logika: --background save
import org.sireum._

def addOne(list: ZS): Unit = {
    Contract(
        Modifies(list),
        Ensures(
            ∀ (0 until list.size)(x => (list(x) == In(list)(x) + 1))
        )
    )

    var i: Z = 0
    while (i < list.size) {
        Invariant(
            Modifies(i, list),
            i >= 0,
            i <= list.size,
            list.size == In(list).size,
            ∀ (0 until i)(x => (list(x) == In(list)(x) + 1)),
            ∀ (i until list.size)(x => (list(x) == In(list)(x)))
        )


        list(i) = list(i) + 1
        i = i + 1
    }
}

////////////// Calling code ///////////////////

var test: ZS = ZS(1,2,3,4)
addOne(test)

assert(test == ZS(2,3,4,5))
