


package ap.theories.algebra;

import ap.basetypes.IdealInt
import ap.parser._
import ap.types.Sort
import ap.util.Debug

trait Semigroup {

  /**
   * Domain of the semigroup
   */
  val dom : Sort

  /**
   * Binary operation of the semigroup
   */
  def op(s : ITerm, t : ITerm) : ITerm

  /**
   * <code>num * s</code>, for <code>n > 0</code>
   */
  def times(num : IdealInt, s : ITerm) : ITerm = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(Debug.AC_ALGEBRA, num > 0)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    var powers = s
    var res : ITerm = null
    var c = num

    while (c.signum > 0) {
      val (div, mod) = c /% IdealInt(2)

      if (!mod.isZero)
        res = if (res == null) powers else op(res, powers)

      powers = op(powers, powers)
      c = div
    }

    res
  }

}

trait Abelian extends Semigroup

trait Monoid extends Semigroup {

  /**
   * The neutral element of this monoid
   */
  def zero : ITerm

  /**
   * <code>num * s</code>, for <code>n >= 0</code>
   */
  override def times(num : IdealInt, s : ITerm) : ITerm = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(Debug.AC_ALGEBRA, num >= 0)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    if (num.isZero)
      zero
    else
      super.times(num, s)
  }
}

trait Group extends Monoid {

  /**
   * Inverse elements
   */
  def minus(s : ITerm) : ITerm

  /**
   * <code>num * s</code>
   */
  override def times(num : IdealInt, s : ITerm) : ITerm =
    num.signum match {
      case -1 => minus(super.times(-num, s))
      case 0  => zero
      case 1  => super.times(num, s)
    }

}

trait Ring {

  /**
   * Domain of the ring
   */
  val dom : Sort

  /**
   * The zero element of this ring
   */
  def zero : ITerm

  /**
   * The one element of this ring
   */
  def one : ITerm

  /**
   * Ring addition
   */
  def plus(s : ITerm, t : ITerm) : ITerm

  /**
   * Additive inverses
   */
  def minus(s : ITerm) : ITerm

  /**
   * Ring multiplication
   */
  def mul(s : ITerm, t : ITerm) : ITerm

  /**
   * Addition gives rise to an Abelian group
   */
  def additiveGroup : Group with Abelian = new Group with Abelian {
    val dom = Ring.this.dom
    def zero = Ring.this.zero
    def op(s : ITerm, t : ITerm) = plus(s, t)
    def minus(s : ITerm) = Ring.this.minus(s)
  }

  /**
   * Multiplication gives rise to a monoid
   */
  def multiplicativeMonoid : Monoid = new Monoid {
    val dom = Ring.this.dom
    def zero = Ring.this.one
    def op(s : ITerm, t : ITerm) = mul(s, t)
  }

}
