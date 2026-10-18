package stainless.lang

sealed abstract class Option[T] {
  def isEmpty: Boolean = this match {
    case None() => true
    case Some(_) => false
  }
  def isDefined: Boolean = !isEmpty
  def get: T = this match {
    case Some(x) => x
    case None() => throw new NoSuchElementException("None.get")
  }
}

final case class Some[T](v: T) extends Option[T]
final case class None[T]() extends Option[T]
