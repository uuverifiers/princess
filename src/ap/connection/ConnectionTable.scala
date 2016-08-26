package ap.connection;

import ap.terfor.ConstantTerm
import ap.terfor.preds.Predicate
import ap.util.{Debug, Timeout}
import ap.parameters.{GoalSettings, Param}
import ap.connection.connection._

// TODO branches should probably be private
class ConnectionTable(val branches : Seq[ConnectionBranch], preSettings : GoalSettings) {

  // TODO: Make nicer?
  var nextPredicate = 0

  override def toString =  branches.mkString("\n")
  def width = branches.length
  def isOpen = branches.find(_.isOpen).isDefined

  // Extend branch branchIdx with clause(idx) and add new branches to the right
  def extendBranch(branchIdx : Int, orderClause : OrderClause, idx : Int, newOrder : BREUOrder) = {
    val preBranches = branches.take(branchIdx)
    val postBranches = branches.drop(branchIdx + 1)
    val newBranches = for (c <- orderClause) yield branches(branchIdx).extend(c, newOrder)
    new ConnectionTable(preBranches ++ (newBranches(idx) :: newBranches.filter(_ != newBranches(idx)))  ++ postBranches, preSettings)
  }

  def close(idx : Int) = {
    val newBranches =
      for (i <- 0 until branches.length) yield {
        if (i == idx) {
          branches(i).close()
        } else {
          branches(i)
        }
      }
    new ConnectionTable(newBranches, preSettings)
  }


  def unifyBranches() 
      : (Boolean, Option[Map[ConstantTerm, ConstantTerm]]) = {
    val ccuSolver = new ccu.LazySolver[ConstantTerm, Predicate](
      () => Timeout.check,
      Param.CLAUSIFIER_TIMEOUT(preSettings))

    // println("branches: \n" + branches.mkString("\n"))

    val problem = branchToBreu(ccuSolver)

    // println("problem: " + problem)

    val result = problem.solve
    if (result == ccu.Result.SAT)
      (true, Some(problem.getModel))
    else
      (false, None)
  }

  def closable : Boolean = {
    for (b <- branches)
      if (!b.isOpen && !b.structuralClosable)
        return false

    val (closed, _) = unifyBranches()
    closed
  }

  def firstOpen = {
    val first = branches.find(_.isOpen)
    val idx = if (!first.isEmpty) (branches indexOf first.get) else -1
    (first, idx)
  }

  def combineOrders(orders : Seq[BREUOrder]) = {
    val maps = orders.map(orderToMap)
    val keys : Set[ConstantTerm] = (for (m <- maps) yield m.keys).foldLeft(Set() : Set[ConstantTerm])(_ ++ _)
    val domains = 
      for (k <- keys) yield {
        val allVals : Set[ConstantTerm] = (for (m <- maps) yield { m.getOrElse(k, Set() : Set[ConstantTerm]) }).foldLeft(Set() : Set[ConstantTerm])(_ ++ _)
        (k -> allVals)
      }
    domains
  }

  def orderToMap(order : BREUOrder) = {
      val domain = scala.collection.mutable.Map() : scala.collection.mutable.Map[ConstantTerm,Set[ConstantTerm]]
      for ((t, uni) <- order.reverse) {
        domain += (t -> Set(t))
        if (uni) {
          for (k <- domain.keys) {
            domain += (t -> (domain(t) + k))
          }
        }
      }
    domain
  }


  // Converts a pc representing a conjunction to a triple
  // DONE!
  def convertFunEquation(funEq : FunEquation) = {
    val pc = funEq.eq
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(ConnectionProver.AC, pc.isLiteral && pc.positiveLits.length == 1)
    //-END-ASSERTION-//////////////////////////////////////////////////////////
    val atom = pc.positiveLits(0)
    val fun = atom.pred
    val args = atom.take(atom.length-1).map(x => x.lastTerm.constants.head)
    val res = atom(atom.length-1).lastTerm.constants.head
    (fun, args.toList, res)
  }


  def convertNegFunEquation(negFunEq : NegFunEquation) = {
    val pc = negFunEq.eq
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(ConnectionProver.AC, pc.isLiteral && pc.positiveLits.length == 1)
    //-END-ASSERTION-//////////////////////////////////////////////////////////
    val atom = pc.positiveLits(0)
    val fun = atom.pred
    val args = atom.take(atom.length-1).map(x => x.lastTerm.constants.head)
    val res = atom(atom.length-1).lastTerm.constants.head
    (fun, args.toList, res)
  }


  def convertEquation(eq : Equation) = {
    eq match {
      case Equation(lhs, rhs) => {
        val p = new Predicate("DummyPredicate" + nextPredicate, 0)
        nextPredicate += 1
        List((p, List(), lhs), (p, List(), rhs))
      }
    }
  }

  def branchToBreu(ccuSolver : ccu.CCUSolver[ConstantTerm, Predicate])
      : ccu.CCUInstance[ConstantTerm, Predicate]  = {
    val selected = (for (i <- branches.indices if !branches(i).isOpen) yield i).toList

    // We need to keep track of domains
    val domains = combineOrders(for (s <- selected) yield branches(s).order)

    val subProblems =
      for (i <- selected) yield {
        val branch = branches(i)
        if (!branch.structuralClosable) {
          throw new Exception("Trying to create BREU-problem from structural open branch!")
        } else {
          val nodes = branch.nodes

          val funEqs = branch.extractFunEquations.map(convertFunEquation(_))
          val eqs = branch.extractEquations.map(convertEquation(_)).flatten
          val negFunEqs = branch.extractNegFunEquations.map(convertNegFunEquation(_))
          
          //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
          Debug.assertInt(ConnectionProver.AC, negFunEqs.length == 0)
          //-END-ASSERTION-//////////////////////////////////////////////////////////

          // println("BRANCH: " + branch)
          // println("\tfunEqs: " + funEqs)
          // println("\teqs: " + eqs)
          // println("\tnegFunEqs: " + negFunEqs)

          val connections = branch.findConnections

          val argGoals : List[List[(ConstantTerm, ConstantTerm)]] =
            for (c <- connections) yield {
              c match {
                case ConnectionNegEq(node) => {
                  (nodes(node)) match {
                    case (NegEquation(t1, t2)) => {
                      List((t1, t2))
                    }
                    case _ => throw new Exception("ConnectionNegEq is pointing wrong!")
                  }
                }
                case ConnectionCompLits(node1, node2) => {
                  (nodes(node1), nodes(node2)) match {
                    case (Literal(pred1), Literal(pred2)) => {
                      val pred1atom = (pred1.negativeLits ++ pred1.positiveLits).head
                      val pred2atom = (pred2.negativeLits ++ pred2.positiveLits).head

                      for ((arg1, arg2) <- (pred1atom zip pred2atom).toList) yield {
                        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
                        Debug.assertPre(ConnectionProver.AC, arg1.termIterator.size == 1 && arg2.termIterator.size == 1)
                        //-END-ASSERTION-//////////////////////////////////////////////////////////
                        // println("\t" + arg1 + "\t?=\t" + arg2)
                        // println("\t" + arg1.getClass + " \t?=\t" + arg2.getClass)
                        (arg1.lastTerm.constants.head, arg2.lastTerm.constants.head)
                      }
                    }
                    case _ => throw new Exception("ConncetionCompLits is pointing wrong!")
                  }
                }
              }
            }
          (argGoals.toList, funEqs ++ eqs, negFunEqs)
        }
      }
    ccuSolver.createProblem(domains.toMap, subProblems.map(_._1), subProblems.map(_._2), subProblems.map(_._3))
  }
}
