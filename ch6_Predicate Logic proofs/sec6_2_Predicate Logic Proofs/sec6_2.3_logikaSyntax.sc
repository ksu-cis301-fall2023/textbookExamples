// #Sireum #Logika
//@Logika: --manual --background save
import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._
import org.sireum.justification.natded.pred._

@pure def sequent[T](x: T, Bunny: T => B @pure, Fluffy: T => B @pure, Fast: T => B @pure): Unit = {
  Deduce((∀{ (x: T) => (Bunny(x) __>: Fluffy(x)) }, ∃{ (x: T) => (Fast(x) & Bunny(x)) })  ⊢  (∃{ (x: T) => (Fast(x) & Fluffy(x)) }) Proof(
    //@formatter:off
    1  (∀{ (x: T) => (Bunny(x) __>: Fluffy(x)) }) by Premise,
    2  (∃{ (x: T) => (Fast(x) & Bunny(x)) }) by Premise,
    3  Let { (thumper: T) => SubProof(
      4  Assume(Fast(thumper) & Bunny(thumper)),
      5  (Fast(thumper)) by AndE1(4),
      6  (Bunny(thumper)) by AndE2(4),
      7  (Bunny(thumper) __>: Fluffy(thumper)) by AllE[T](1),
      8  (Fluffy(thumper)) by ImplyE(7, 6),
      9  (Fast(thumper) & Fluffy(thumper)) by AndI(5, 8),
      10  (∃{ (x: T) => (Fast(x) & Fluffy(x)) }) by ExistsI[T](9)
    )},
    11  (∃{ (x: T) => (Fast(x) & Fluffy(x)) }) by ExistsE[T](2, 3)
    //@formatter:on
  ))
}