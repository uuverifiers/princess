package ap.connection;

import ap.connection.connection.{OrderNode, BREUOrder}
import ap.terfor.ConstantTerm
import ap.util.Debug
import scala.collection.mutable.ListBuffer

// TODO: Maybe store how branch was closed?
class ConnectionBranch(val nodes : List[Node], val open : Boolean, val order : BREUOrder) {

  override def toString = {
    val nodeString =
      for (n <- nodes.reverse) yield {
        n match {
          case Literal(formula) => formula
          case FunEquation(eq) => eq
          case NegFunEquation(eq) => eq
          case Equation(lhs, rhs) => lhs + " = " + rhs
          case NegEquation(lhs, rhs) => lhs + " != " + rhs
        }
      }

    if (open) {
        "||\t (---) " + nodeString
    } else {
        "||\t (XXX) " + nodeString
    }
  }

  def isOpen = open

  def close() = new ConnectionBranch(nodes, false, order)

  // TODO: Extra order, yuck...
  def extend(newOrderNode : OrderNode, extraOrder : BREUOrder) = {
    val (newNodes, newOrder) = newOrderNode
    // TODO: Correct combination order?
    val mergeOrder = newOrder ++ extraOrder ++ order
    new ConnectionBranch(newNodes ++ nodes, open, mergeOrder)
  }

  def depth = (for (n <- nodes if n.isLiteral) yield 1).sum

  def length = nodes.length

  def apply(idx : Int) = nodes(idx)

  // DONE
  def extractEquations : List[Equation] = {
    
    def extractEquationsAux(nodes : List[Node]) : List[Equation] = {
      if (nodes.isEmpty)
        List()
      else
        nodes.head match {
          case Equation(lhs, rhs) => Equation(lhs, rhs) :: extractEquationsAux(nodes.tail)
          case _ => extractEquationsAux(nodes.tail)
        }
    }
    extractEquationsAux(nodes)
  }

  def extractFunEquations : List[FunEquation] = {
    def extractFunEquationsAux(nodes : List[Node]) : List[FunEquation] = {
      if (nodes.isEmpty)
        List()
      else
        nodes.head match {
          case FunEquation(eq) => FunEquation(eq) :: extractFunEquationsAux(nodes.tail)
          case _ => extractFunEquationsAux(nodes.tail)
        }
    }
    extractFunEquationsAux(nodes)
  }

  def extractNegEquations : List[NegEquation] = {
    def extractNegEquationsAux(nodes : List[Node]) : List[NegEquation] = {
      if (nodes.isEmpty)
        List()
      else
        nodes.head match {
          case NegEquation(t1, t2) => NegEquation(t1, t2) :: extractNegEquationsAux(nodes.tail)
          case _ => extractNegEquationsAux(nodes.tail)
        }
    }
    extractNegEquationsAux(nodes)
  }

  def extractNegFunEquations : List[NegFunEquation] = {
    def extractNegFunEquationsAux(nodes : List[Node]) : List[NegFunEquation] = {
      if (nodes.isEmpty)
        List()
      else
        nodes.head match {
          case NegFunEquation(eq) => NegFunEquation(eq) :: extractNegFunEquationsAux(nodes.tail)
          case _ => extractNegFunEquationsAux(nodes.tail)
        }
    }
    extractNegFunEquationsAux(nodes)
  }


  // DONE
  def extractLiterals : List[Literal] = {
    def extractLiteralsAux(nodes : List[Node]) : List[Literal] = {
      if (nodes.isEmpty)
        List()
      else
        nodes.head match {
          case Literal(f) => Literal(f) :: extractLiteralsAux(nodes.tail)
          case _ => extractLiteralsAux(nodes.tail)
        }
    }
    extractLiteralsAux(nodes)
  }

  // TODO: Maybe convert to val?
  def findConnections : List[Connection] = {
    var connections = ListBuffer() : ListBuffer[Connection]

    for (i <- 0 until nodes.length;
      j <- i + 1 until nodes.length;
      if (nodes(i).structuralUnifiable(nodes(j))))
    yield connections += ConnectionCompLits(i, j)

    for (n <- nodes) {
      n match {
        case NegEquation(_, _) => connections += ConnectionNegEq(nodes indexOf n)
        case _ => ()
      }
    }

    connections.toList
  }

  // Returns true if pred1 and pred2 can be unified, given the equations and order
  def structuralUnifiable(node1 : Literal, node2 : Literal) : Boolean = {
    (node1, node2) match {
      case (Literal(pred1), Literal(pred2)) => {
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
        Debug.assertInt(ConnectionProver.AC, pred1.isLiteral && pred2.isLiteral)
        //-END-ASSERTION-//////////////////////////////////////////////////////////

        // Two cases, either pred1 and !pred2 or !pred1 and pred2
        if (!((pred1.negativeLits.length == 1 && pred2.positiveLits.length == 1) ||
          (pred2.negativeLits.length == 1 && pred1.positiveLits.length == 1))) {
          return false
        }

        // println("\tNegation-compatible")
        // They have to share predicate symbol
        val pred1atom = (pred1.negativeLits ++ pred1.positiveLits).head
        val pred2atom = (pred2.negativeLits ++ pred2.positiveLits).head

        if (pred1atom.pred != pred2atom.pred)
          return false

        true
      }
      case _ => false
    }
  }


  // DONE!
  // Checks whether the branch can be closed structurally
  // (i.e., contains predicates of opposite polarity or inequalites)
  def structuralClosable : Boolean = findConnections.length > 0
}
