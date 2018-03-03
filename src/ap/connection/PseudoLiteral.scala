package ap.connection;

import ap.terfor.preds.{PredConj}



class PseudoLiteral (val funs : List[FunEquation], val lit : Node)  {

  // object LiteralType extends Enumeration {
  //   type LiteralType = Value
  //   // val Equality,NegEquality,Predicate = Value
  //   val Equality,Predicate = Value    
  // }

  def nodes : List[Node] = {
    lit match {
      case True => funs
      case l => l :: funs
    }
  }

  override def toString = {
    "(" + funs.mkString("^") + "::" + lit + ")"
  }

}
