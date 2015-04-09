import org.scalatest._

class TableSolverSpec extends FlatSpec with Matchers {

  def dummy() = ()

  "A TableSolver" should "create without problem" in {
    val solver = new ccu.TableSolver(dummy, 1000000)
  }

  "A TableSolver" should "create problem with BREUInterface" in {
    val solver = new ccu.TableSolver(dummy, 1000000)
    val problem = new ccu.SimpleBREUProblem("test.txt")
    val instance = solver.createInstance(problem)
    val result = instance.solve
    assert(result == ccu.Result.SAT)
  }

  // it should "throw NoProblemCreated if an empty problem is solved" in {
  //   a [IndexOutOfBoundsException] should be thrownBy {
  //     val solver = new ccu.TableSolver(dummy, 1000000)
  //     // solver.solve
  //   }
  // }
}
