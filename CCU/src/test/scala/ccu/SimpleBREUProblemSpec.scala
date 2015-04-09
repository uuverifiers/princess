import org.scalatest._

class SimpleBREUProblemSpec extends FlatSpec with Matchers {

  "A SimpleBREUProblem" should "load file without problem" in {
    val problem = new ccu.SimpleBREUProblem("test.txt")
  }

  it should "throw FileNotFoundException if file is not found" in {
    a [java.io.FileNotFoundException] should be thrownBy {
      val problem = new ccu.SimpleBREUProblem("asd")
    }
  }
}
