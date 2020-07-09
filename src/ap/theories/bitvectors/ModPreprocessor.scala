/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2017-2020 Philipp Ruemmer <ph_r@gmx.net>
 *               2019      Peter Backeman <peter@backeman.se>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 2.1 of the License, or
 * (at your option) any later version.
 *
 * Princess is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with Princess.  If not, see <http://www.gnu.org/licenses/>.
 */

package ap.theories.bitvectors

import ap.theories._

import ap.parser._
import ap.basetypes.IdealInt
import ap.parameters.{Param, ReducerSettings}
import ap.types.{Sort, SortedIFunction, SortedPredicate}
import ap.terfor.{TermOrder, TerForConvenience}
import ap.terfor.preds.Predicate
import ap.terfor.conjunctions.{Conjunction, ReduceWithConjunction}
import ap.terfor.linearcombination.LinearCombination0
import ap.terfor.substitutions.VariableShiftSubst
import ap.util.Debug

import scala.collection.immutable.VectorBuilder
import scala.collection.mutable.ArrayBuffer

/**
 * Pre-processing of formulas
 */
object ModPreprocessor {

  private val AC = Debug.AC_MODULO_ARITHMETIC

  import ModuloArithmetic._

  case class VisitorArg(modN : Option[IdealInt],
                        boundVarRanges : List[(Option[IdealInt],
                                               Option[IdealInt])],
                        underQuantifier : Boolean) {
    import IExpression._

    def setMod(n : IdealInt) =
      copy(modN = Some(n), underQuantifier = false)

    def addMod(n : IdealInt) = modN match {
      case Some(oldN) if (oldN divides n) =>
        this.notUnderQuantifier
      case _ =>
        this.setMod(n)
    }

    def multMod(factor : IdealInt, localMod : IdealInt) = modN match {
      case Some(oldN) => {
        val prod = oldN * factor
        if (prod divides localMod)
          setMod(prod)
        else
          setMod(localMod)
      }
      case None =>
        setMod(localMod)
    }

    def divideMod(divisor : IdealInt) = modN match {
      case Some(oldN) => {
        val g = oldN gcd divisor
        if (g > IdealInt.ONE)
          setMod(oldN / g)
        else
          this.notUnderQuantifier
      }
      case _ =>
        this.notUnderQuantifier
    }

    def noMod =
      if (modN.isDefined || underQuantifier)
        copy(modN = None, underQuantifier = false)
      else
        this

    def pushVar =
      copy(boundVarRanges = (None, None) :: boundVarRanges,
           underQuantifier = true)

    def notUnderQuantifier =
      if (underQuantifier)
        copy(underQuantifier = false)
      else
        this

    def collectVariableRanges(f : IFormula) = {
      var ranges = boundVarRanges

      def collectRanges(f : IFormula, neg : Boolean) : Unit = f match {
        case INot(subF) =>
          collectRanges(subF, !neg)
        case Conj(left, right) if !neg => {
          collectRanges(left, neg)
          collectRanges(right, neg)
        }
        case Disj(left, right) if neg => {
          collectRanges(left, neg)
          collectRanges(right, neg)
        }
        case Geq(IVariable(ind), IIntLit(value)) if !neg => {
          val (oldL, oldU) =
            ranges(ind)
          ranges =
            ranges.updated(ind, (Some((oldL getOrElse value) max value), oldU))
        }
        case Geq(IIntLit(value), IVariable(ind)) if !neg => {
          val (oldL, oldU) =
            ranges(ind)
          ranges =
            ranges.updated(ind, (oldL, Some((oldU getOrElse value) min value)))
        }
        case _ =>
          // nothing
      }

      collectRanges(f, false)
      copy(boundVarRanges = ranges, underQuantifier = false)
    }
  }

  //////////////////////////////////////////////////////////////////////////////
 
  object VisitorRes {

    def apply(const : IdealInt) : VisitorRes =
      VisitorRes(IIntLit(const), const, const)

    def apply(e : IExpression) : VisitorRes =
      VisitorRes(e, null, null)

    def update(t : IExpression, subres : Seq[VisitorRes]) : VisitorRes = {
      if (subres.isEmpty)
        deriveBounds(t, subres)
      else
        deriveBounds(t update (subres map (_.res)), subres)
    }

    def deriveBounds(t : IExpression,
                     subres : Seq[VisitorRes]) : VisitorRes = t match {
      case _ : IFormula =>
        VisitorRes(t, null, null)

      case IIntLit(value) =>
        VisitorRes(t, value, value)

      case _ : IPlus => {
        val Seq(VisitorRes(_, lb1, ub1), VisitorRes(_, lb2, ub2)) = subres
        val newLB = if (lb1 == null || lb2 == null) null else (lb1 + lb2)
        val newUB = if (ub1 == null || ub2 == null) null else (ub1 + ub2)
        VisitorRes(t, newLB, newUB)
      }

      case ITimes(coeff, _) => {
        val Seq(VisitorRes(_, lb, ub)) = subres
        if (coeff.signum >= 0)
          VisitorRes(t,
                     if (lb == null) null else (lb * coeff),
                     if (ub == null) null else (ub * coeff))
        else
          VisitorRes(t,
                     if (ub == null) null else (ub * coeff),
                     if (lb == null) null else (lb * coeff))
      }

      case _ : ITermITE => {
        val Seq(_, VisitorRes(_, lb1, ub1), VisitorRes(_, lb2, ub2)) = subres
        val newLB = if (lb1 == null || lb2 == null) null else (lb1 min lb2)
        val newUB = if (ub1 == null || ub2 == null) null else (ub1 max ub2)
        VisitorRes(t, newLB, newUB)
      }

      case IFunApp(MulTheory.Mul(), _) => {
        val Seq(VisitorRes(_, lb1, ub1), VisitorRes(_, lb2, ub2)) = subres
        if (lb1 == null || lb2 == null || ub1 == null || ub2 == null) {
          VisitorRes(t, null, null)
        } else {
          val p1 = lb1 * lb2
          val p2 = lb1 * ub2
          val p3 = ub1 * lb2
          val p4 = ub1 * ub2
          VisitorRes(t, p1 min p2 min p3 min p4, p1 max p2 max p3 max p4)
        }
      }

      case _ : IConstant |
           _ : IFunApp => (Sort sortOf t.asInstanceOf[ITerm]) match {
        case ModSort(lower, upper) =>
          VisitorRes(t, lower, upper)
        case Sort.Interval(lower, upper) =>
          VisitorRes(t, lower getOrElse null, upper getOrElse null)
        case _ =>
          VisitorRes(t, null, null)
      }

      case _ =>
        VisitorRes(t, null, null)
    }
  }

  case class VisitorRes(res : IExpression,
                        lowerBound : IdealInt,   // maybe null
                        upperBound : IdealInt) { // maybe null
    import IExpression._

    def resTerm = res.asInstanceOf[ITerm]

    def modCast(lower : IdealInt, upper : IdealInt,
                ctxt : VisitorArg) : VisitorRes =
      modCastHelp(lower, upper, ctxt) match {
        case null =>
          VisitorRes(mod_cast(lower, upper, resTerm), lower, upper)
        case res =>
          res
      }

    def modCastPow2(bits : Int, ctxt : VisitorArg) : VisitorRes =
      modCast(IdealInt.ZERO, pow2MinusOne(bits), ctxt)

    def modCastSignedPow2(bits : Int, ctxt : VisitorArg) : VisitorRes = {
      val ModSort(lower, upper) = SignedBVSort(bits)
      modCast(lower, upper, ctxt)
    }

    def modCastHelp(lower : IdealInt, upper : IdealInt,
                    ctxt : VisitorArg) : VisitorRes = {
      val modulus = upper - lower + IdealInt.ONE
      ctxt.modN match {
        case Some(n) if (n divides modulus) =>
          this
        case _ =>
          if (lowerBound == null || upperBound == null) {
            null // mod_cast is needed!
          } else {
            val lowerFactor = (lowerBound - lower) / modulus
            val upperFactor = -((upper - upperBound) / modulus)
            if (lowerFactor == upperFactor) {
              if (lowerFactor.isZero) {
                this
              } else {
                val corr = lowerFactor * modulus
                if (isConstant)
                  VisitorRes(lowerBound - corr)
                else
                  VisitorRes(resTerm - corr, lowerBound - corr, upperBound - corr)
              }
            } else {
              null // mod_cast is needed!
            }
          }
      }
    }

    def isConstant : Boolean =
      lowerBound != null && upperBound != null && lowerBound == upperBound

    def +(that : VisitorRes) : VisitorRes =
      VisitorRes.deriveBounds(IPlus(this.resTerm, that.resTerm),
                              List(this, that))

    def +(num : IdealInt) : VisitorRes =
      if (num.isZero)
        this
      else
        this + VisitorRes(num, num, num)

    def *(coeff : IdealInt) : VisitorRes =
      if (coeff.isOne)
        this
      else
        VisitorRes.deriveBounds(ITimes(coeff, resTerm), List(this))

    def *(that : VisitorRes) : VisitorRes =
      VisitorRes.deriveBounds(IFunApp(MultTheory.mul,
                                      List(this.resTerm, that.resTerm)),
                              List(this, that))

    def eDiv(divisor : IdealInt) : VisitorRes = {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertPre(AC, divisor.signum > 0)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      VisitorRes(MultTheory.eDiv(resTerm, divisor),
                 lowerBound match {
                   case null               => null
                   case b if b.signum <= 0 => b / divisor
                   case _                  => IdealInt.ZERO
                 },
                 upperBound match {
                   case null               => null
                   case b if b.signum >= 0 => b / divisor
                   case _                  => IdealInt.ZERO
                 })
    }

    def lowerBoundOrElse(that : IdealInt) : IdealInt = lowerBound match {
      case null => that
      case b    => b
    }

    def lowerBoundMin(minimum : IdealInt) : IdealInt = lowerBound match {
      case null => minimum
      case b    => b max minimum
    }

    def upperBoundOrElse(that : IdealInt) : IdealInt = upperBound match {
      case null => that
      case b    => b
    }

    def upperBoundMax(maximum : IdealInt) : IdealInt = upperBound match {
      case null => maximum
      case b    => b min maximum
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * First-level preprocessor:
   * Visitor that translates bit-vector operations to a basic set of operations
   * (mod_cast, ...) and simplifies.
   */
  object Preproc extends CollectingVisitor[VisitorArg, VisitorRes] {
    import IExpression._

    override def preVisit(t : IExpression,
                          ctxt : VisitorArg) : PreVisitResult = t match {
      case _ : IQuantified | _ : IEpsilon =>
        UniSubArgs(ctxt.pushVar)
      case Conj(left, _) if ctxt.underQuantifier =>
        SubArgs(List(ctxt.notUnderQuantifier,
                     ctxt collectVariableRanges left))
      case Disj(left, _) if ctxt.underQuantifier =>
        SubArgs(List(ctxt.notUnderQuantifier,
                     ctxt collectVariableRanges ~left))

      case IFunApp(`mod_cast`, Seq(IIntLit(lower), IIntLit(upper), _)) =>
        SubArgs(List(ctxt.noMod, ctxt.noMod,
                     ctxt addMod (upper - lower + IdealInt.ONE)))

      case IFunApp(`l_shift_cast`, Seq(IIntLit(lower), IIntLit(upper), _*)) =>
        SubArgs(List(ctxt.noMod, ctxt.noMod,
                     ctxt addMod (upper - lower + IdealInt.ONE),
                     ctxt.noMod))

      case IFunApp(`bv_extract`,
                   Seq(IIntLit(IdealInt(begin)), IIntLit(IdealInt(end)), _*)) =>
        SubArgs(List(ctxt.noMod, ctxt.noMod,
                     ctxt.multMod(pow2(end), pow2(begin + 1))))

      case IFunApp(`bv_neg` | `bv_add` | `bv_sub` | `bv_mul`,
                   Seq(IIntLit(IdealInt(n)), _*)) =>
        // TODO: handle bit-width argument correctly
        UniSubArgs(ctxt addMod pow2(n))

      case IFunApp(`bv_shl`,
                   Seq(IIntLit(IdealInt(n)), _*)) =>
        SubArgs(List(ctxt.noMod, ctxt addMod pow2(n), ctxt.noMod))

      case IAtom(`bv_slt` | `bv_sle`,
                 Seq(IIntLit(IdealInt(n)), _*)) =>
        UniSubArgs(ctxt addMod pow2(n))

      case _ : IPlus | IFunApp(MulTheory.Mul(), _) => // IMPROVE
        UniSubArgs(ctxt.notUnderQuantifier)
      case ITimes(coeff, _) =>
        UniSubArgs(ctxt divideMod coeff)

      case _ : ITermITE =>
        SubArgs(List(ctxt.noMod,
                     ctxt.notUnderQuantifier, ctxt.notUnderQuantifier))

      case _ =>
        UniSubArgs(ctxt.noMod)
    }

    def doExtract(start : Int, end : Int, arg : ITerm, argBits : Int) : ITerm =
      if (start == argBits - 1 && end == 0) {
        arg
      } else arg match {
        // TODO: simplify nested extracts, shifts, etc.
        case IIntLit(argVal) =>
          evalExtract(start, end, argVal)
        case arg =>
          IFunApp(bv_extract, Vector(start, end, arg))
      }

    ////////////////////////////////////////////////////////////////////////////

    def constantBVSHL(bits : Int, arg : VisitorRes,
                      shift : IdealInt) : VisitorRes =
      shift match {
        case IdealInt.ZERO =>
          arg
        case shift if shift.signum < 0 =>
          throw new Exception("negative shift")
        case IdealInt(shift) if shift < bits => {
          val sort =
            UnsignedBVSort(bits)
          val res =
            sort.eps(eqZero(doExtract(shift - 1, 0, v(0), bits)) &
                     (doExtract(bits - 1, shift, v(0), bits) ===
                      doExtract(bits - shift - 1, 0,
                                VariableShiftVisitor(arg.resTerm, 0, 1), bits)))

          val f1 = pow2(bits - shift)
          val f2 = pow2(shift)
          VisitorRes(
            res,
            (arg.lowerBoundMin(IdealInt.ZERO) % f1) * f2,
            (arg.upperBoundMax(pow2MinusOne(bits+1)) % f1) * f2)
        }
        case _ =>
          VisitorRes(IdealInt.ZERO)
      }

    def constantBVLSHR(bits : Int, arg : VisitorRes,
                       shift : IdealInt) : VisitorRes =
      shift match {
        case IdealInt.ZERO =>
          arg
        case shift if shift.signum < 0 =>
          throw new Exception("negative shift")
        case IdealInt(shift) if shift < bits => {
          val divisor = pow2(shift)
          VisitorRes(
            doExtract(bits-1, shift, arg.resTerm, bits),
            arg.lowerBoundMin(IdealInt.ZERO) / divisor,
            arg.upperBoundMax(pow2MinusOne(bits+1)) / divisor)
        }
        case _ =>
          VisitorRes(IdealInt.ZERO)
      }

    def boundsBVASHR(bits : Int, arg : VisitorRes,
                     shift : IdealInt) : (IdealInt, IdealInt) = {
      val divisor =   pow2(shift)
      val threshold = pow2(bits - 1)
      val pow2bits =  pow2(bits)

      if (arg.upperBound != null && arg.upperBound < threshold) {
        (arg.lowerBoundMin(IdealInt.ZERO) / divisor,
         arg.upperBound / divisor)
      } else if (arg.lowerBound != null && arg.lowerBound >= threshold) {
        ((arg.lowerBound - pow2bits) / divisor +
           pow2bits,
         (arg.upperBoundMax(pow2MinusOne(bits+1)) - pow2bits) / divisor +
           pow2bits)
      } else {
        (IdealInt.ZERO, pow2MinusOne(bits+1))
      }
    }

    def constantBVASHR(bits : Int, arg : VisitorRes,
                       shift : IdealInt) : VisitorRes =
      shift match {
        case IdealInt.ZERO =>
          arg
        case shift if shift.signum < 0 =>
          throw new Exception("negative shift")
        case IdealInt(shift) if shift < bits => {
          val sort =
            UnsignedBVSort(bits)
          val res =
            sort.eps(ex(geqZero(v(0)) & (v(0) <= 1) &
                        and(for (n <- (bits - shift - 1) to (bits - 1))
                            yield (doExtract(n, n, v(1), bits) === v(0))) &
                        (doExtract(bits - shift - 1, 0, v(1), bits) ===
                         doExtract(bits - 1, shift,
                                   VariableShiftVisitor(arg.resTerm, 0, 2),
                                   bits))))
          val (lb, ub) =
            boundsBVASHR(bits, arg, shift)
          VisitorRes(res, lb, ub)
        }
        case _ => {
          val sort =
            UnsignedBVSort(bits)
          val res =
            sort.eps(ex(geqZero(v(0)) & (v(0) <= 1) &
                        and(for (n <- 0 to (bits - 1))
                            yield (doExtract(n, n, v(1), bits) === v(0))) &
                        (doExtract(bits - 1, bits - 1,
                                   VariableShiftVisitor(arg.resTerm, 0, 2),
                                   bits) === v(0))))
          val (lb, ub) =
            boundsBVASHR(bits, arg, shift)
          VisitorRes(res, lb, ub)
        }
      }

    ////////////////////////////////////////////////////////////////////////////

    def postVisit(t : IExpression,
                  ctxt : VisitorArg, subres : Seq[VisitorRes]) : VisitorRes =
      t match {
        case IFunApp(`mod_cast`, Seq(IIntLit(lower), IIntLit(upper), _)) =>
          subres.last.modCastHelp(lower, upper, ctxt) match {
            case null => VisitorRes.update(t, subres)
            case res  => res
          }

        case IFunApp(`bv_extract`, Seq(IIntLit(IdealInt(start)),
                                       IIntLit(IdealInt(end)), _*)) =>
          if (subres(2).isConstant)
            VisitorRes(evalExtract(start, end, subres(2).lowerBound))
          else
            VisitorRes.update(t, subres)

        case IFunApp(`bv_concat`, Seq(IIntLit(IdealInt(bits1)),
                                      IIntLit(IdealInt(bits2)), _*)) =>
          if (subres(2).isConstant && subres(3).isConstant) {
            VisitorRes(subres(2).lowerBound * pow2(bits2) +
                       subres(3).lowerBound)
          } else {
            val sort = UnsignedBVSort(bits1+bits2)

            // We create a new variable v(0) which is existentially
            // quantified, representing the result of the concat

            val bv1lhs = bv_extract(bits1+bits2-1, bits2, v(0))
            val bv1rhs = VariableShiftVisitor(subres(2).resTerm, 0, 1)
            val bv1 = (bv1lhs === bv1rhs)

            val bv2lhs = bv_extract(bits2-1, 0, v(0))
            val bv2rhs = VariableShiftVisitor(subres(3).resTerm, 0, 1)
            val bv2 = (bv2lhs === bv2rhs)

            val res = sort.eps(bv1 & bv2)

            VisitorRes(res,
                       (subres(2).lowerBoundOrElse(IdealInt.ZERO) * pow2(bits2)) +
                         subres(3).lowerBoundOrElse(IdealInt.ZERO),
                       (subres(2).upperBoundOrElse(pow2(bits1)) * pow2(bits2)) +
                         subres(3).upperBoundOrElse(pow2(bits2)))
          }

        case IFunApp(`bv_not`, Seq(IIntLit(IdealInt(bits)), _)) =>
          if (subres(1).isConstant) {
            VisitorRes(pow2MinusOne(bits) - subres(1).lowerBound)
          } else {
            val sort = UnsignedBVSort(bits)

            val rawArg = subres(1).resTerm
            val simple = isSimpleTerm(rawArg)

            val (arg, resTerm) =
              if (simple)
                (VariableShiftVisitor(rawArg, 0, 1), v(0))
              else
                (v(0), v(1))

            val resultDef =
              and(for (i <- 0 until bits) yield {
                eqZero(doExtract(i, i, arg, bits) +
                       doExtract(i, i, resTerm, bits) +
                       IdealInt.MINUS_ONE)
              })

            val res =
              if (simple)
                sort.eps(resultDef)
              else
                sort.eps(ex(v(0) === VariableShiftVisitor(rawArg, 0, 2) &
                            resultDef))

            VisitorRes(res,
                       sort.upper - (subres(1) upperBoundMax sort.upper),
                       sort.upper - (subres(1) lowerBoundMin IdealInt.ZERO))
          }

        case IFunApp(`bv_neg`, Seq(IIntLit(IdealInt(bits)), _)) =>
          (subres.last * IdealInt.MINUS_ONE).modCastPow2(bits, ctxt)

        case IFunApp(`bv_add`, Seq(IIntLit(IdealInt(bits)), _*)) =>
          (subres(1) + subres(2)).modCastPow2(bits, ctxt)

        case IFunApp(`bv_sub`, Seq(IIntLit(IdealInt(bits)), _*)) =>
          (subres(1) + (subres(2) * IdealInt.MINUS_ONE)).modCastPow2(bits, ctxt)

        ////////////////////////////////////////////////////////////////////////

        case IFunApp(`bv_mul`, Seq(IIntLit(IdealInt(bits)), _*)) =>
          (subres(1).isConstant, subres(2).isConstant) match {
            case (true, true) =>
              VisitorRes(subres(1).lowerBound *
                         subres(2).lowerBound).modCastPow2(bits, ctxt)
            case (true, false) =>
              (subres(2) * subres(1).lowerBound).modCastPow2(bits, ctxt)
            case (false, true) =>
              (subres(1) * subres(2).lowerBound).modCastPow2(bits, ctxt)
            case (false, false) =>
              (subres(1) * subres(2)).modCastPow2(bits, ctxt)
          }

        // TODO: move this clause to the multiplication theory?
        case IFunApp(MulTheory.Mul(), Seq(IIntLit(IdealInt(bits)), _*)) =>
          (subres(1).isConstant, subres(2).isConstant) match {
            case (true, true) =>
              VisitorRes(subres(1).lowerBound *
                         subres(2).lowerBound).modCastPow2(bits, ctxt)
            case (true, false) =>
              subres(2) * subres(1).lowerBound
            case (false, true) =>
              subres(1) * subres(2).lowerBound
            case (false, false) =>
              VisitorRes.update(t, subres)
          }

        ////////////////////////////////////////////////////////////////////////

        case IFunApp(`l_shift_cast`, Seq(IIntLit(lower), IIntLit(upper), _*)) =>
          if (subres(3).isConstant) {
            ModSort(lower, upper) match {
              case UnsignedBVSort(bits) =>
                constantBVSHL(bits, subres(2), subres(3).lowerBound)
              // signed arithmetic?
              case sort =>
                (subres(2) * pow2(subres(3).lowerBound max IdealInt.ZERO))
                  .modCast(lower, upper, ctxt)
            }
          } else {
            VisitorRes.update(t, subres)
          }

        case IFunApp(`r_shift_cast`, Seq(IIntLit(lower), IIntLit(upper), _*)) =>
          if (subres(3).isConstant) {
            ModSort(lower, upper) match {
              case UnsignedBVSort(bits) =>
                constantBVLSHR(bits, subres(2), subres(3).lowerBound)
              // signed arithmetic?
              case sort => {
                val denom = pow2(subres(3).lowerBound max IdealInt.ZERO)
                subres(2).eDiv(denom).modCast(lower, upper, ctxt)
              }
            }
          } else {
            VisitorRes.update(t, subres)
          }

        ////////////////////////////////////////////////////////////////////////

        case IFunApp(`bv_shl`, Seq(IIntLit(IdealInt(bits)), _*)) =>
          if (subres(2).isConstant) {
            constantBVSHL(bits, subres(1), subres(2).lowerBound)
//          (subres(1) * pow2(subres(2).lowerBound.intValueSafe))
//            .modCastPow2(bits, ctxt)
          } else {
            val upper = pow2MinusOne(bits)
            VisitorRes(l_shift_cast(IdealInt.ZERO, upper,
                                    subres(1).resTerm, subres(2).resTerm),
                       IdealInt.ZERO, upper)
          }

        case IFunApp(`bv_lshr`, Seq(IIntLit(IdealInt(bits)), _*)) =>
          if (subres(2).isConstant) {
            constantBVLSHR(bits, subres(1), subres(2).lowerBound)
          } else {
            val upper = pow2MinusOne(bits)
            VisitorRes(r_shift_cast(IdealInt.ZERO, upper,
                                    subres(1).resTerm, subres(2).resTerm),
                       IdealInt.ZERO, upper)
          }

        case IFunApp(`bv_ashr`, Seq(IIntLit(IdealInt(bits)), _*)) =>
          if (subres(2).isConstant) {
            constantBVASHR(bits, subres(1), subres(2).lowerBound)
          } else {
            val ModSort(lower, upper) = SignedBVSort(bits)
            VisitorRes(r_shift_cast(
                         lower, upper,
                         subres(1).modCastSignedPow2(bits, ctxt.noMod).resTerm,
                         subres(2).resTerm),
                       lower, upper).modCastPow2(bits, ctxt)
          }

        ////////////////////////////////////////////////////////////////////////

        case IFunApp(`bv_and`, Seq(IIntLit(IdealInt(bits)), _*)) => {
          val sort = UnsignedBVSort(bits)

          def oneConstant(arg : VisitorRes, pattern : IdealInt) : VisitorRes =
            runlengths(pattern) match {
              case Seq(_) => {
                //-BEGIN-ASSERTION-/////////////////////////////////////////////
                // Pattern must be constantly zero
                Debug.assertInt(AC, pattern.isZero)
                //-END-ASSERTION-///////////////////////////////////////////////
                VisitorRes(IdealInt.ZERO)
              }
              case Seq(0, length) => {
                // pattern starting with a single block of ones
                VisitorRes(
                  doExtract(length - 1, 0, arg.resTerm, bits),
                  IdealInt.ZERO, pattern)
              }

              case preLens => {
                // multiple blocks of zeros, handle using an epsilon term
                val lens = completedRunlengths(preLens, bits)

                var offset : Int = 0
                var bit = true
                
                val resultDef =
                  and(for (len <- lens) yield {
                        bit = !bit
                        if (len > 0) {
                          offset = offset + len
                          doExtract(offset-1, (offset-len), v(1), bits) === 
                          (if (bit)
                             doExtract(offset-1, (offset-len), v(0), bits)
                           else
                             i(0))
                        } else {
                          i(true)
                        }
                      })
                
                val res =
                  sort.eps(
                    ex(v(0) === VariableShiftVisitor(arg.resTerm, 0, 2) &
                       resultDef))

                VisitorRes(res, IdealInt.ZERO, pattern)
              }
            }

          (subres(1).isConstant, subres(2).isConstant) match {
            case (true, true) =>
              VisitorRes(subres(1).lowerBound & subres(2).lowerBound)
            case (true, false) =>
              oneConstant(subres(2), subres(1).lowerBound)
            case (false, true) =>
              oneConstant(subres(1), subres(2).lowerBound)

            case (false, false) => {
              val resultDef = 
                and(for (i <- 0 until bits) yield{
                  val res = doExtract(i, i, v(2), bits)
                  val lhs = doExtract(i, i, v(1), bits)
                  val rhs = doExtract(i, i, v(0), bits)
                  (res <= lhs) & (res <= rhs) & (res >= lhs + rhs - 1)
                })
              val res =
                sort.eps(ex(ex(
                  v(1) === VariableShiftVisitor(subres(1).resTerm, 0, 3) &
                  v(0) === VariableShiftVisitor(subres(2).resTerm, 0, 3) &
                  resultDef)))
              VisitorRes(res,
                         IdealInt.ZERO,
                         (subres(1) upperBoundMax sort.upper) min
                           (subres(2) upperBoundMax sort.upper))
            }

          }
        }

        ////////////////////////////////////////////////////////////////////////

        case IFunApp(`bv_or`, Seq(IIntLit(IdealInt(bits)), _*)) => {
          val sort = UnsignedBVSort(bits)

          def oneConstant(arg : VisitorRes, pattern : IdealInt) : VisitorRes =
            runlengths(pattern) match {
              case Seq(_) => {
                //-BEGIN-ASSERTION-/////////////////////////////////////////////
                // Pattern must be constantly zero
                Debug.assertInt(AC, pattern.isZero)
                //-END-ASSERTION-///////////////////////////////////////////////
                arg
              }
              case Seq(offset, length) if offset + length == bits => {
                // pattern ending with a single block of ones
                VisitorRes(
                  doExtract(offset-1, 0, arg.resTerm, bits) + pattern,
                  pattern, pow2MinusOne(bits))
              }
              
              case preLens => {
                // multiple blocks of zeros, handle using an epsilon term
                val lens = completedRunlengths(preLens, bits)

                var offset : Int = 0
                var bit = true

                val resultDef =
                  and(for (len <- lens) yield {
                        bit = !bit
                        if (len > 0) {
                          offset = offset + len
                          doExtract(offset-1, offset-len, v(1), bits) ===
                          (if (bit)
                             i(pow2MinusOne(len))
                           else
                             doExtract(offset-1, offset - len, v(0), bits))
                        } else {
                          i(true)
                        }
                      })
                
                val res =
                  sort.eps(
                    ex(v(0) === VariableShiftVisitor(arg.resTerm, 0, 2) &
                       resultDef))

                VisitorRes(res, pattern, pow2MinusOne(bits))
              }
            }

          (subres(1).isConstant, subres(2).isConstant) match {
            case (true, true) =>
              VisitorRes(subres(1).lowerBound | subres(2).lowerBound)
            case (true, false) =>
              oneConstant(subres(2), subres(1).lowerBound)
            case (false, true) =>
              oneConstant(subres(1), subres(2).lowerBound)

            case (false, false) => {
              val resultDef = 
                and(for (i <- 0 until bits) yield{
                  val res = doExtract(i, i, v(2), bits)
                  val lhs = doExtract(i, i, v(1), bits)
                  val rhs = doExtract(i, i, v(0), bits)
                  (res >= lhs) & (res >= rhs) & (res <= lhs + rhs)
                })
              val res =
                sort.eps(ex(ex(
                    v(1) === VariableShiftVisitor(subres(1).resTerm, 0, 3) &
                    v(0) === VariableShiftVisitor(subres(2).resTerm, 0, 3) &
                    resultDef)))
    
              VisitorRes(res,
                         (subres(1) lowerBoundMin IdealInt.ZERO) max
                           (subres(2) lowerBoundMin IdealInt.ZERO),
                         sort.upper)
            }

          }
        }

        ////////////////////////////////////////////////////////////////////////

        case IFunApp(`bv_xor`, Seq(IIntLit(IdealInt(bits)), _*)) => {
          val sort = UnsignedBVSort(bits)
          val resultDef = 
            and(for (i <- 0 until bits) yield{
              val res = doExtract(i, i, v(2), bits)
              val lhs = doExtract(i, i, v(1), bits)
              val rhs = doExtract(i, i, v(0), bits)
              mod_cast(0, 1, lhs+rhs) === res
            })
          val res =
            sort.eps(ex(ex(
                v(1) === VariableShiftVisitor(subres(1).resTerm, 0, 3) &
                v(0) === VariableShiftVisitor(subres(2).resTerm, 0, 3) &
                resultDef)))
          VisitorRes(res, IdealInt.ZERO, sort.upper)
        }

        ////////////////////////////////////////////////////////////////////////

        case IFunApp(`bv_comp`, Seq(IIntLit(IdealInt(bits)), _*)) =>
          if (subres(1).isConstant && subres(2).isConstant) {
            VisitorRes(if (subres(1).lowerBound == subres(2).lowerBound)
                         IdealInt.ONE
                       else
                         IdealInt.ZERO)
          } else {
            // could be optimised further: handle cases where the bounds imply
            // that the terms have different values
            VisitorRes(ite(subres(1).resTerm === subres(2).resTerm,
                           IdealInt.ONE, IdealInt.ZERO),
                       IdealInt.ZERO, IdealInt.ONE)
          }

        ////////////////////////////////////////////////////////////////////////

        // TODO: special treatment for constant denominators?
        case IFunApp(`bv_udiv`, Seq(IIntLit(IdealInt(bits)), _*)) => {
          val ModSort(lower, upper) = UnsignedBVSort(bits)
          VisitorRes(ite(subres(2).resTerm === 0,
                         upper,
                         MultTheory.eDiv(subres(1).resTerm, subres(2).resTerm)),
                     lower, upper)
        }
        // TODO: special treatment for constant denominators?
        case IFunApp(`bv_urem`, Seq(IIntLit(IdealInt(bits)), _*)) => {
          VisitorRes(ite(subres(2).resTerm === 0,
                         subres(1).resTerm,
                         MultTheory.eMod(subres(1).resTerm, subres(2).resTerm)),
                     IdealInt.ZERO, subres(1).upperBound)
        }

        ////////////////////////////////////////////////////////////////////////

        case IFunApp(`bv_sdiv`, Seq(IIntLit(IdealInt(bits)), _*)) => {
          val sort = UnsignedBVSort(bits)
          val ModSort(_, unsUpper) = sort
          val ModSort(sLower, sUpper) = SignedBVSort(bits)

          val modulus = sort.modulus

/*
          val num = subres(1).resTerm
          val negNum = -num + modulus
          val denom = subres(2).resTerm
          val negDenom = -denom + modulus
          val v0Denom = MultTheory.mult(v(0), denom)
          val v0NegDenom = MultTheory.mult(v(0), negDenom)

          val res = VisitorRes(
            eps(((denom === 0) &
                   (v(0) === ite(num > sUpper, IdealInt.ONE, unsUpper))) |
                ((num <= sUpper) & (denom > 0) & (denom <= sUpper) &
                   (v0Denom <= num) & (v0Denom > num - denom)) |
                ((num > sUpper) & (denom > 0) & (denom <= sUpper) &
                   (-v0Denom <= negNum) & (-v0Denom > negNum - denom)) |
                ((num <= sUpper) & (denom > sUpper) &
                   (-v0Denom <= num) & (-v0Denom > num - negDenom)) |
                ((num > sUpper) & (denom > sUpper) &
                   (v0NegDenom <= negNum) & (v0NegDenom > negNum - negDenom))))
*/

          val resVar = v(3)

          val (num, numDef) =
            VariableShiftVisitor(subres(1).resTerm, 0, 4) match {
              case SimpleTerm(rawNum) => (rawNum, i(true))
              case rawNum             => (v(0), v(0) === rawNum)
            }

          val negNum = -num + modulus

          val (denom, denomDef) =
            VariableShiftVisitor(subres(2).resTerm, 0, 4) match {
              case SimpleTerm(rawDenom) => (rawDenom, i(true))
              case rawDenom             => (v(1), v(1) === rawDenom)
            }

          val negDenom = -denom + modulus

          val (timesDenom, timesDenomDef) =
            MultTheory.mult(resVar, denom) match {
              case SimpleTerm(t) => (t, i(true))
              case t             => (v(2), v(2) === t)
            }

          val negTimesDenom = -timesDenom + (resVar * modulus)

          val VisitorRes(_, denomLower, denomUpper) = subres(2)
          val denomMightBeZero =
            denomLower == null || denomLower.signum <= 0
          val denomMightBePositive =
            !(denomLower != null && denomLower > sUpper ||
              denomUpper != null && denomUpper.signum <= 0)
          val denomMightBeNegative =
            denomUpper == null || denomUpper > sUpper

          val res = VisitorRes(
            eps(ex(ex(ex(
                numDef &&& denomDef &&& timesDenomDef &&&
                ((if (denomMightBeZero)
                    (denom === 0) &
                      (resVar === ite(num > sUpper, IdealInt.ONE, unsUpper))
                  else
                    i(false)) |||
                 (if (denomMightBePositive)
                    ((num <= sUpper) & (denom > 0) & (denom <= sUpper) &
                       (timesDenom <= num) &
                       (timesDenom > num - denom)) |
                    ((num > sUpper) & (denom > 0) & (denom <= sUpper) &
                       (-timesDenom <= negNum) &
                       (-timesDenom > negNum - denom))
                  else
                    i(false)) |||
                 (if (denomMightBeNegative)
                    ((num <= sUpper) & (denom > sUpper) &
                       (-timesDenom <= num) &
                       (-timesDenom > num - negDenom)) |
                    ((num > sUpper) & (denom > sUpper) &
                       (negTimesDenom <= negNum) &
                       (negTimesDenom > negNum - negDenom))
                  else
                    i(false))))))),
            sLower, unsUpper)

          res.modCastPow2(bits, ctxt)
        }

/*
        case IFunApp(`bv_sdiv`, Seq(IIntLit(IdealInt(bits)), _*)) => {
          val ModSort(lower, upper) = UnsignedBVSort(bits)
          val noModCtxt = ctxt.noMod
          val numMod = subres(1).modCastSignedPow2(bits, noModCtxt).resTerm
          val divTerm =
            MultTheory.tDiv(
                  numMod,
                  subres(2).modCastSignedPow2(bits, noModCtxt).resTerm)
          VisitorRes(
            ite(subres(2).resTerm === 0,
                ite(numMod < 0, IdealInt.ONE, upper),
                VisitorRes(divTerm).modCastPow2(bits, ctxt).resTerm),
            lower, upper)
        }
*/

        ////////////////////////////////////////////////////////////////////////

        // TODO: better treatment of constant denominators?
        case IFunApp(`bv_srem`, Seq(IIntLit(IdealInt(bits)), _*)) => {
          val noModCtxt = ctxt.noMod
          val ModSort(lower, upper) = SignedBVSort(bits)

          if (subres(2).isConstant && subres(2).lowerBound.isZero)
            subres(1).modCastPow2(bits, ctxt)
          else
            VisitorRes(
              ite(subres(2).resTerm === 0,
                  subres(1).modCastSignedPow2(bits, noModCtxt).resTerm,
                  MultTheory.tMod(
                    subres(1).modCastSignedPow2(bits, noModCtxt).resTerm,
                    subres(2).modCastSignedPow2(bits, noModCtxt).resTerm)),
              lower, upper).modCastPow2(bits, ctxt)
        }

        ////////////////////////////////////////////////////////////////////////

        case IFunApp(`bv_smod`, Seq(IIntLit(IdealInt(bits)), _*)) => {
          val sort = UnsignedBVSort(bits)
          val ModSort(_, unsUpper) = sort
          val ModSort(sLower, sUpper) = SignedBVSort(bits)

          val modulus = sort.modulus

          val (num, numDef) =
            VariableShiftVisitor(subres(1).resTerm, 0, 5) match {
              case SimpleTerm(rawNum) => (rawNum, i(true))
              case rawNum             => (v(0), v(0) === rawNum)
            }

          val (denom, denomDef) =
            VariableShiftVisitor(subres(2).resTerm, 0, 5) match {
              case SimpleTerm(rawDenom) => (rawDenom, i(true))
              case rawDenom             => (v(1), v(1) === rawDenom)
            }

          val strideVar = v(3)
          val resVar = v(4)

          val (multPos, multPosDef) =
            MultTheory.mult(strideVar, denom) match {
              case SimpleTerm(t) => (t, i(true))
              case t             => (v(2), v(2) === t)
            }

          val multNeg = -multPos + (strideVar * modulus)

          val VisitorRes(_, denomLower, denomUpper) = subres(2)
          val denomMightBeZero =
            denomLower == null || denomLower.signum <= 0
          val denomMightBePositive =
            !(denomLower != null && denomLower > sUpper ||
              denomUpper != null && denomUpper.signum <= 0)
          val denomMightBeNegative =
            denomUpper == null || denomUpper > sUpper

          val res = VisitorRes(
            eps(ex(ex(ex(ex(
              numDef &&& denomDef &&& multPosDef &&&
              ((if (denomMightBeZero)
                  denom === 0 & resVar === num
                else
                  i(false)) |||
               (if (denomMightBePositive)
                  (num <= sUpper & denom > 0 & denom <= sUpper &
                   num === multPos + resVar &
                   resVar >= 0 & resVar < denom) |
                  (num > sUpper & denom > 0 & denom <= sUpper &
                   -num + modulus === multPos - resVar + denom &
                   resVar >= 0 & resVar < denom)
                else
                  i(false)) |||
               (if (denomMightBeNegative)
                  (num <= sUpper & denom > sUpper &
                   num === multNeg + resVar &
                   resVar <= 0 & resVar > denom - modulus) |
                  (num > sUpper & denom > sUpper &
                   -num + modulus === multNeg - resVar &
                   resVar <= 0 & resVar > denom - modulus)
                else
                  i(false)))
            ))))),
            sLower, sUpper)

          res.modCastPow2(bits, ctxt)
        }

        ////////////////////////////////////////////////////////////////////////

        case IAtom(`bv_ult`, _) =>
          if (subres(1).isConstant && subres(2).isConstant)
            VisitorRes(subres(1).lowerBound < subres(2).lowerBound)
          else
            VisitorRes(subres(1).resTerm < subres(2).resTerm)
 
        case IAtom(`bv_ule`, _) =>
          if (subres(1).isConstant && subres(2).isConstant)
            VisitorRes(subres(1).lowerBound <= subres(2).lowerBound)
          else
            VisitorRes(subres(1).resTerm <= subres(2).resTerm)

        case IAtom(`bv_slt`, Seq(IIntLit(IdealInt(bits)), _*)) =>
          if (subres(2).isConstant &&
              subres(2).modCastSignedPow2(bits, ctxt).lowerBound.isZero) {
            val ModSort(_, mid) = SignedBVSort(bits)
            VisitorRes(subres(1).modCastPow2(bits, ctxt).resTerm > mid)
          } else if (subres(1).isConstant &&
                     subres(1).modCastSignedPow2(bits, ctxt)
                              .lowerBound.isMinusOne) {
            val ModSort(_, mid) = SignedBVSort(bits)
            VisitorRes(subres(2).modCastPow2(bits, ctxt).resTerm <= mid)
          } else {
            VisitorRes(subres(1).modCastSignedPow2(bits, ctxt).resTerm <
                       subres(2).modCastSignedPow2(bits, ctxt).resTerm)
          }

        case IAtom(`bv_sle`, Seq(IIntLit(IdealInt(bits)), _*)) =>
          if (subres(2).isConstant &&
              subres(2).modCastSignedPow2(bits, ctxt).lowerBound.isMinusOne) {
            val ModSort(_, mid) = SignedBVSort(bits)
            VisitorRes(subres(1).modCastPow2(bits, ctxt).resTerm > mid)
          } else if (subres(1).isConstant &&
                     subres(1).modCastSignedPow2(bits, ctxt)
                              .lowerBound.isZero) {
            val ModSort(_, mid) = SignedBVSort(bits)
            VisitorRes(subres(2).modCastPow2(bits, ctxt).resTerm <= mid)
          } else {
            VisitorRes(subres(1).modCastSignedPow2(bits, ctxt).resTerm <=
                       subres(2).modCastSignedPow2(bits, ctxt).resTerm)
          }

        case t =>
          VisitorRes.update(t, subres)
      }
  }

  /**
   * Run-length encoding of a number, starting with the number of
   * least-significant zeroes.
   */
  private def runlengths(v : IdealInt) : Seq[Int] = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC, v.signum >= 0)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    val two = IdealInt(2)
    val res = new VectorBuilder[Int]

    var curBit = IdealInt.ZERO
    var curNum = 0

    var rem = v

    while (!rem.isZero) {
      val (newRem, bit) = rem /% two
      if (bit == curBit) {
        curNum = curNum + 1
      } else {
        res += curNum
        curNum = 1
        curBit = bit
      }

      rem = newRem
    }

    res += curNum
    res.result
  }

  private def completedRunlengths(lens : Seq[Int],
                                  totalLen : Int) : Seq[Int] = {
    val lensSum = lens.sum
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC, lensSum <= totalLen)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    if (lensSum < totalLen)
      lens ++ List(totalLen - lensSum)
    else
      lens
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Second-level preprocessor, on internal formulas
   */
  protected[bitvectors]
    def preprocess(f : Conjunction, order : TermOrder) : Conjunction = {
    implicit val o = order
    import TerForConvenience._

//    println("init: " + f)

    val after1 = Theory.rewritePreds(f, order) { (a, negated) =>
      a.pred match {
        case BVPred(`bv_concat` |
                    `bv_not` | `bv_neg` | `bv_add` | `bv_sub` | `bv_mul` |
                    `bv_udiv` | `bv_urem` |
                    `bv_sdiv` | `bv_srem` | `bv_srem` |
                    `bv_shl`) =>
          throw new Exception("unexpected function " + a.pred)

        case `bv_ult` | `bv_ule` | `bv_slt` | `bv_sle` =>
          throw new Exception("unexpected predicate " + a.pred)

        case `_bv_extract` if ModuloArithmetic.directlyEncodeExtract => {
          val bits1 =
            a(0).asInstanceOf[LinearCombination0].constant.intValueSafe -
            a(1).asInstanceOf[LinearCombination0].constant.intValueSafe + 1
          val bits2 =
            a(1).asInstanceOf[LinearCombination0].constant.intValueSafe

          val castSort = UnsignedBVSort(bits1 + bits2)
          val remSort =  UnsignedBVSort(bits2)

          val subst = VariableShiftSubst(0, 1, order)
          val pred = _mod_cast(List(l(0), l(castSort.upper),
                                    subst(a(2)),
                                    subst(a(3))*remSort.modulus + v(0)))

          if (negated)
            existsSorted(List(remSort), pred)
          else
            // forall int v0, BV[bits2] v1.
            //   mod_cast(a(3), v0) => a(4)*modulus + v1 != v0
            // <=>
            // forall int v0, BV[bits2] v1.
            //   mod_cast(a(3), a(4)*modulus + v0) => v1 != v0
            // <=>
            // forall int v0.
            //   mod_cast(a(3), a(4)*modulus + v0) => v0 \not\in BV[bits2]
            forall(pred ==>
                     Conjunction.negate(remSort membershipConstraint v(0),
                                        order))
        }

        case `_mod_cast` | `_l_shift_cast` | `_r_shift_cast` | `_bv_extract` =>
          a

        case BVPred(_) => {
          Console.err.println("Warning: don't know how to handle " + a)
          Incompleteness.set
          a
        }

        case _ =>
          a
      }
    }

    val reducerSettings =
      Param.REDUCER_PLUGIN       .set(
      Param.FUNCTIONAL_PREDICATES.set(ReducerSettings.DEFAULT,
                                      functionalPredicates),
                                      reducerPlugin)

//    println("after1: " + after1)
    
    val after2 = ReduceWithConjunction(Conjunction.TRUE,
                                       order,
                                       reducerSettings)(after1)

//    println("after2: " + after2)

    after2
  }  

  private object BVPred {
    val reverseMapping =
      (for ((a, b) <- functionPredicateMapping.iterator) yield (b, a)).toMap
    def unapply(p : Predicate) : Option[IFunction] = reverseMapping get p
  }

}
