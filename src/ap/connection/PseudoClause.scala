package ap.connection;

class PseudoClause(val pseudoLiterals : Seq[PseudoLiteral]) {
  override def toString = {
    pseudoLiterals.mkString(" v ")
  }

  def head : PseudoLiteral = pseudoLiterals.head
  def isUnit : Boolean = pseudoLiterals.length == 1
  val length = pseudoLiterals.length
}
