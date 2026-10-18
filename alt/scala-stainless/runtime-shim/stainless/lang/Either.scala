package stainless.lang

sealed abstract class Either[A, B] {
  def isLeft: Boolean = this match {
    case Left(_) => true
    case Right(_) => false
  }
  def isRight: Boolean = !isLeft
}

final case class Left[A, B](a: A) extends Either[A, B]
final case class Right[A, B](b: B) extends Either[A, B]
