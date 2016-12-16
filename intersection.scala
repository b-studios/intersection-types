import shapeless._
import ops.hlist._
import shapeless.test.illTyped

/**
 * Using HLists as flat representation of intersection types.
 *
 *
 * ==Overview==
 * A value of the intersection type `A & B` can be used both as
 * a value of type `A` as well as a value of type `B`. Given the
 * two functions
 *
 * {{{
 *   def f(x: Int): String = x.toString
 *   def g(x: Boolean): String = if (x) "hello" else "world"
 * }}}
 *
 * a value `foo: Int & Boolean` can be passed to both functions
 * `f` and `g`. Using Scala's intersection types, which are
 * backed by Java interfaces / classes we cannot obtain a
 * value of type `Int with Boolean`. In addition, given an
 * integer and a boolean, we cannot create such a value at runtime.
 *
 * This library allows to do both by representing a value which
 * is of type `Int` and of type `Boolean` as the type-level list
 * `Int :: Boolean :: HNil`. Merging an integer with a boolean
 * value simply amounts to storing them in a (h)list.
 *
 * ==Usage==
 * Since we use the hlist implementation of shapeless as backing data structure
 * you need to also include shapeless as dependency and import the hlist
 * operations:
 *
 * {{{
 *   import shapeless._
 *   import ops.hlist._
 * }}}
 *
 * Now, given two values of intersection types we can apply merge them
 * to obtain the intersection:
 *
 * {{{
 *   val x: Int :: HNil = 42 :: HNil
 *   val y: Boolean :: HNil = false :: HNil
 *
 *   val both: Int :: Boolean :: HNil = x & y
 *
 *   println(f(both.select[Int]) + " " + g(both.select[Boolean]))
 * }}}
 *
 * As you notice, the projection into the intersection type has to be
 * explicitly selected at the moment. The same is true for subtyping
 * relationships between intersection types:
 *
 * {{{
 *   val y2: Boolean :: HNil = subsume[Boolean :: HNil, Int :: Boolean :: HNil](both)
 * }}}
 *
 * We hope to work around this issue in future releases.
 *
 * ==Implementation==
 * The implementation keeps the invariant, that a type may only occur once
 * in an intersection (also see wellformedness, [[WF]]). Also the order
 * of elements in the HLists can be arbitrary, effectively
 * implementing type level sets.
 *
 * ''Design decision'': Right now, only HLists that contain at least one element are
 * considered a wellformed intersection type. The alternative would be to also
 * allow for empty intersections (see code which is commented out).
 *
 * We also don't account for subtypes, yet. So if `B <: A` and we have a list
 * of type `L = B :: HNil`, we cannot select an `A` from it.
 * This is a consequence of Selector being defined invariant in shapeless.
 */
package object intersection {

  // Some aliases for more inference-rule looking implicits
  private type ∉[T, L <: HList] = FilterNot.Aux[L, T, L]
  private type ∈[T, L <: HList] = Selector[L, T]

  /**
   * Typeclass witnessing the fact that L is a wellformed intersection type.
   */
  sealed trait WF[L <: HList]
  object WF {

    private def witness[L <: HList]: WF[L] = new WF[L] {}

//    implicit val wfNil:
//
//    //  --------
//        WF[HNil]   = witness

    implicit def wfSingleton[H]:

    //      -------------
            WF[H :: HNil]       = witness

    implicit def wfCons[H, L <: HList](implicit

          r: H ∉ L, wf: WF[L]
      //  -------------------
    ):         WF[H :: L]       = witness
  }

  /**
   * Typeclass witnessing the fact that the intersection type L1 is a subtype of L2.
   * We also write: L1 ≺ L2
   *
   * Note that also users can define instances of Selector and Subtype to synthesize
   * components of the intersection type from other existing components.
   *
   * Note: Right now, we don't require L1 or L2 to be WF.
   */
  sealed trait Subtype[L1 <: HList, L2 <: HList] {
    def apply(l: L2): L1
  }
  type ≺[L1 <: HList, L2 <: HList] = Subtype[L1, L2]

  trait LowPrioSubtype {
    implicit def mergeLeft[L1 <: HList, L2 <: HList](implicit m: Merge[L1, L2]): L1 ≺ m.Out = m.left
  }
  object Subtype extends LowPrioSubtype {

    def witness[L1 <: HList, L2 <: HList](f: L2 => L1) = new Subtype[L1, L2] {
      def apply(l: L2) = f(l)
    }

//    implicit def nilSubtype[L2 <: HList]:
//
//    //  -----------
//        HNil ≺ L2   = witness(_ => HNil)

    implicit def singletonSubtype[H, L2 <: HList](implicit

             in:  H ∈ L2
      //    ----------------
    ):      (H :: HNil) ≺ L2         = witness(l2 => in(l2) :: HNil)

    implicit def consSubtype[H, L1 <: HList, L2 <: HList](implicit

          in: H ∈ L2, sub: L1 ≺ L2
      //  ------------------------
    ):         (H :: L1) ≺ L2        = witness(l2 => in(l2) :: sub(l2))


    implicit def mergeRight[L1 <: HList, L2 <: HList](implicit m: Merge[L1, L2]): L2 ≺ m.Out = m.right
  }

  // Right now, applying subsumption implicitly does not work. But making subsumption implicit
  // also doesn't break anything right now, so let's keep it enabled.
  implicit def subsume[L1 <: HList, L2 <: HList](l2: L2)(implicit s: L1 ≺ L2): L1 = s(l2)
  implicit class SubtypeOps[L1 <: HList](self: L1) {
    def coerce[L2 <: HList](implicit s: L2 ≺ L1): L2 = s(self)
  }

  sealed trait Merge[L1 <: HList, L2 <: HList] {
    type Out <: HList
    def apply(l1: L1, l2: L2): Out
    def left: L1 ≺ Out
    def right: L2 ≺ Out
  }

  object Merge {
    type Aux[L1 <: HList, L2 <: HList, Out0 <: HList] = Merge[L1, L2] { type Out = Out0 }

    def apply[L1 <: HList, L2 <: HList](l1: L1, l2: L2)(implicit m: Merge[L1, L2]): m.Out = m(l1, l2)

//    implicit def nilMerge[L <: HList]:
//
//    //  ---------------------
//        Merge.Aux[HNil, L, L]
//
//      = new Merge[HNil, L] {
//        type Out = L
//        def apply(l1: HNil, l2: L): Out = l2
//
//        override def left = HNil
//      }

    implicit def singletonMerge[H, L <: HList](implicit

      notIn: H ∉ L
      //  -------------------------------
    ):    Merge.Aux[H :: HNil, L, H :: L]

    = new Merge[H :: HNil, L] {
      type Out = H :: L
      def apply(l1: H :: HNil, l2: L): Out = l1.head :: l2
      def left: (H :: HNil) ≺ Out = Subtype.witness(o => o.head :: HNil)
      def right: L ≺ Out          = Subtype.witness(o => o.tail)
    }

    // The simplest merge, forbid double occurrences
    implicit def consMergeProhibitive[H, L1 <: HList, L2 <: HList](implicit

      wf1: WF[H :: L1], wf2: WF[L2], notIn: H ∉ L2, m: Merge[L1, L2]
      //  --------------------------------------------------------------
    ):                 Merge.Aux[H :: L1, L2, H :: m.Out]

    = new Merge[H :: L1, L2] {
      type Out = H :: m.Out
      def apply(l1: H :: L1, l2: L2): Out = l1.head :: m(l1.tail, l2)
      def left: (H :: L1) ≺ (H :: m.Out) = Subtype.witness(o => o.head :: m.left(o.tail))
      def right: L2       ≺ (H :: m.Out) = Subtype.witness(o => m.right(o.tail))
    }

  }
  implicit class MergeOps[L1 <: HList](self: L1) {
    def &[L2 <: HList](other: L2)(implicit m: Merge[L1, L2]): m.Out = m(self, other)
  }


  private object wellformedTests {

    def wellformed[T <: HList](implicit w: WF[T]): Unit = ()

    //  wellformed[ HNil ]
    wellformed[ Int :: HNil ]
    wellformed[ String :: Int :: HNil ]
    wellformed[ Boolean :: String :: Int :: HNil ]

    illTyped("wellformed[Int :: String :: Int :: HNil]")
    illTyped("wellformed[Int :: Int :: HNil]")
    illTyped("wellformed[Int :: Unit :: Int :: Unit :: HNil]")
  }

  private object subtypeTests {

    def subtype[L1 <: HList, L2 <: HList](implicit w: Subtype[L1, L2]): Unit = ()

    subtype[
      Int :: HNil,
      String :: Int :: Boolean :: HNil]

    // user defined rule: If an HasEval is in a list, then also an Int is in the list
    trait HasEval { def eval: Int }
    implicit def hasEvalInL[L <: HList](implicit in: HasEval ∈ L): Int ∈ L
    = new Selector[L, Int] {
      def apply(l: L): Int = in(l).eval
    }

    subtype[
      Int :: HNil,
      String :: HasEval :: Boolean :: HNil]

    // Order independent
    subtype[
      Boolean :: String :: HNil,
      String :: Int :: Boolean :: HNil]
  }

  object mergeTests {

    implicitly[Merge.Aux[
      Int :: HNil,
      String :: HNil,
      Int :: String :: HNil]]

    type L1   = Int  :: Boolean :: HNil
    type L2   = Unit :: String  :: HNil
    type L1L2 = Int  :: Boolean :: Unit :: String :: HNil
    implicitly[Merge.Aux[L1, L2, L1L2]]
    implicitly[L1 ≺ L1L2]
    implicitly[L2 ≺ L1L2]

    val l12 : L1L2 = ???

    // I don't why subsume is not inserted here automatically.
    // TODO check with dotty or newer compiler versions
    val l1: L2 = subsume[L2, L1L2](l12)

    trait A
    trait B extends A

    // this is different than in most other intersection types:

    // (1) intersection types are not covariant.
    illTyped { "implicitly[A ∈ (B :: HNil)]" }

    // (2) hence merging related but unequal types succeeds.
    implicitly[Merge.Aux[A :: HNil, B :: HNil, A :: B :: HNil]]
    illTyped { "implicitly[Merge[A :: HNil, A :: HNil]]" }

    illTyped { "implicitly[Merge[Int :: String :: HNil, String :: HNil]]" }
    illTyped { "implicitly[Merge[Int :: String :: HNil, Boolean :: String :: HNil]]" }

    val merged = (42 :: HNil) & ("hello world" :: true :: HNil)
    val str = merged.select[String]

    // autocoercion does not work, right now.
    val l = merged.coerce[Int :: Boolean :: HNil]

    def f(x: Int): String = x.toString
    def g(x: Boolean): String = if (x) "hello" else "world"

    val x: Int :: HNil    = 42
    val y: Boolean :: HNil = false

    val both: Int :: Boolean :: HNil = x & y
    val y2: Boolean :: HNil = subsume[Boolean :: HNil, Int :: Boolean :: HNil](both)

    println(f(both.select[Int]) + " " + g(both.select[Boolean]))


  }

}