import org.scalatest._

class SimpleBREUProblemSpec extends FlatSpec with Matchers {

  def dummy() = ()

  "A SimpleBREUProblem" should "load file without problem" in {
    val solver = new ccu.TableSolver(dummy, 1000000)
    val instance = solver.createInstanceFromFile("test.breu")
    println(instance)
    instance.solve

  }

  // it should "throw FileNotFoundException if file is not found" in {
  //   a [java.io.FileNotFoundException] should be thrownBy {
  //     val problem = new ccu.SimpleBREUProblem("asd")
  //   }
  // }
}
