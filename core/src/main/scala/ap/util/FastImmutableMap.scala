package ap.util

object FastImmutableMap {
  def apply[A, B](m : Map[A, B]) = new FastImmutableMap(m)
  def empty[A, B] = new FastImmutableMap[A, B](Map())
  
  private val AccessBound = 1000
}

/**
 * A double-backed map class that initially stores its elements in a
 * <code>scala.collection.immutable.Map</code>, but copies all data to a
 * <code>scala.collection.mutable.HashMap</code> when many accesses are taking
 * place (since the mutable map enables faster access than the immutable map).
 */
class FastImmutableMap[A, B] private (immMap : Map[A, B])
      extends Map[A, B] {

  import FastImmutableMap.AccessBound

  override def empty = new FastImmutableMap[A, B](Map())

  private var mMap : scala.collection.mutable.HashMap[A, B] = null
  
  private var accessNum = 0

  private def createMMap : Unit = {
    val mm = new scala.collection.mutable.HashMap[A, B]
    mm ++= immMap
    mMap = mm
  }
  
  def get(t : A) : Option[B] = if (mMap == null) {
    accessNum = accessNum + 1
    if (accessNum > AccessBound) {
      createMMap
      mMap get t
    } else {
      immMap get t
    }
  } else {
    mMap get t
  }
  
  override def apply(t : A) : B = if (mMap == null) {
    accessNum = accessNum + 1
    if (accessNum > AccessBound) {
      createMMap
      mMap(t)
    } else {
      immMap(t)
    }
  } else {
    mMap(t)
  }
  
  override def size : Int = immMap.size
  
  def iterator : Iterator[(A, B)] = immMap.iterator
  
  def + [B1 >: B](kv: (A, B1)) =
    new FastImmutableMap(immMap + kv)
  override def ++[B1 >: B](xs: scala.collection.GenTraversableOnce[(A, B1)]) =
    new FastImmutableMap(immMap ++ xs)

  def -(key: A) =
    new FastImmutableMap(immMap - key)

  override def foreach[U](f: ((A, B)) => U): Unit = immMap foreach f

}
