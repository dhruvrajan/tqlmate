package stainless

package object lang {
  def decreases(r1: Any): Unit = ()
  def decreases(r1: Any, r2: Any): Unit = ()
  def unfold[T](call: T): Unit = ()

  implicit class BooleanDecorations(val underlying: Boolean) extends AnyVal {
    def holds: Boolean = {
      require(underlying)
      underlying
    }
    def ==>(that: => Boolean): Boolean = if (underlying) that else true
  }
}
