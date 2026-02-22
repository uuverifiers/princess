/**
 * Shared SMT helper types that are independent from concrete frontends.
 */
package ap.parser

object SMTSupport {

  import IExpression.{Sort => TSort}
  import SMTTypes._

  def toNormalBool(s : TSort) : TSort = s match {
    case TSort.MultipleValueBool => TSort.Bool
    case other                   => other
  }

  case class SMTFunctionType(arguments : List[SMTType],
                             result : SMTType)

  val SMTBoolVariableType : SMTFunctionType =
    SMTFunctionType(List(), SMTBool)
}
