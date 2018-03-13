package ap.connection;

import ap.terfor.conjunctions.{Conjunction}
import ap.terfor.preds.{Atom, PredConj}
import ap.connection.connection.BREUOrder
import ap.terfor.arithconj.ArithConj
import ap.terfor.linearcombination.LinearCombination

object PseudoClause {

  abstract class tmpList {
    val depth : Int = 
      this match {
        case list(l) => l.map(_.depth).max + 1
        case leaf(_) => 0
      }

    def tryPrint(negated : Boolean) : String = {
      this match {
        case leaf(s) if (negated) => "(-" + s + ")"
        case leaf(s) => "(" + s + ")"          
        case list(l) if (negated) =>  "(" + l.map(_.tryPrint(!negated)).mkString(" v ") + ")"
        case list(l) =>  "(" + l.map(_.tryPrint(!negated)).mkString(" ^ ") + ")"          
      }
    }
  }

  case class list(val l : List[tmpList]) extends tmpList {
    override def toString() = {
      l.mkString("[", ",", "]")
    }
  }
  // case class leaf(val lit : PseudoLiteral) extends tmpList;
  case class leaf(val lit : String) extends tmpList {
    override def toString() = {
      lit
    }
  }

  def predToLit(atom : Atom, negated : Boolean) : tmpList = {
    leaf(atom.toString)
  }


  def arithToLit(lc : LinearCombination, negated : Boolean) : tmpList = {
    leaf(lc.toString)
  }
  def conjunctionToList(conj : Conjunction, negated : Boolean) : list = {
    println("conjunctionToList(" + conj + ", " + negated + ")")

    // PredConjs should be returned as top-level literals
    val posPredLits = conj.predConj.positiveLits.map(predToLit(_, negated)).toList
    val negPredLits = conj.predConj.negativeLits.map(predToLit(_, !negated)).toList    

    // ArithConjs should be returned as top-level literals
    val posArithLits = conj.arithConj.positiveEqs.map(arithToLit(_, negated)).toList
    val negArithLits = conj.arithConj.negativeEqs.map(arithToLit(_, negated)).toList    

    // NegatedConjs should be returned sa Lists of something

    val negatedLits = 
      for (nc <- conj.negatedConjs.toList) yield {
        conjunctionToList(nc, !negated)
      }

    list(posPredLits ++ negPredLits ++ posArithLits ++ negArithLits ++ negatedLits)
  }




  def fromConjunction(conj : Conjunction) : (PseudoClause, BREUOrder) = {
    val res = conjunctionToList(conj, false)
    println(conj)
    println("\t" + res)
    println("\t" + res.depth)
    println("===" + res.tryPrint(false))
    if (res.depth > 3)
      println("TODEEP")
    (new PseudoClause(List()), List())
  }
}



class PseudoClause(val pseudoLiterals : Seq[PseudoLiteral]) {
  override def toString = {
    pseudoLiterals.mkString(" v ")
  }

  def head : PseudoLiteral = pseudoLiterals.head
  def isUnit : Boolean = pseudoLiterals.length == 1
  val length = pseudoLiterals.length
}
