package stainless.lang

object StaticChecks {
  implicit class Ensuring[A](val x: A) extends AnyVal {
    def ensuring(cond: A => Boolean): A = x
    def ensuring(cond: A => Boolean, msg: => String): A = x
  }

  def require(pred: => Boolean): Unit = ()
  def require(pred: => Boolean, msg: => String): Unit = ()
  def assert(pred: => Boolean): Unit = ()
  def assert(pred: => Boolean, msg: => String): Unit = ()
}
