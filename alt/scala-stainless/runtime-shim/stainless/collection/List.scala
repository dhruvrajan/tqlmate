package stainless.collection

/** Runtime stand-in for Stainless `List` (Cons / Nil). */
sealed abstract class List[+T] {
  def isEmpty: Boolean = this match {
    case Nil() => true
    case Cons(_, _) => false
  }

  def size: BigInt = this match {
    case Nil() => BigInt(0)
    case Cons(_, t) => BigInt(1) + t.size
  }

  def length: BigInt = size

  def head: T = this match {
    case Cons(h, _) => h
    case Nil() => throw new NoSuchElementException("head of empty list")
  }

  def tail: List[T] = this match {
    case Cons(_, t) => t
    case Nil() => throw new NoSuchElementException("tail of empty list")
  }

  def ::[U >: T](elem: U): List[U] = Cons(elem, this)

  def :+[U >: T](elem: U): List[U] = this match {
    case Nil() => Cons(elem, Nil())
    case Cons(h, t) => Cons(h, t :+ elem)
  }

  def ++[U >: T](that: List[U]): List[U] = this match {
    case Nil() => that
    case Cons(h, t) => Cons(h, t ++ that)
  }

  def reverse: List[T] = {
    def go(xs: List[T], acc: List[T]): List[T] = xs match {
      case Nil() => acc
      case Cons(h, t) => go(t, Cons(h, acc))
    }
    go(this, Nil())
  }

  def contains[U >: T](v: U): Boolean = this match {
    case Nil() => false
    case Cons(h, t) => h == v || t.contains(v)
  }

  def map[R](f: T => R): List[R] = this match {
    case Nil() => Nil()
    case Cons(h, t) => Cons(f(h), t.map(f))
  }

  def filter(p: T => Boolean): List[T] = this match {
    case Nil() => Nil()
    case Cons(h, t) => if (p(h)) Cons(h, t.filter(p)) else t.filter(p)
  }

  def foldLeft[R](z: R)(f: (R, T) => R): R = this match {
    case Nil() => z
    case Cons(h, t) => t.foldLeft(f(z, h))(f)
  }

  def toScala: scala.collection.immutable.List[T] = this match {
    case Nil() => scala.Nil
    case Cons(h, t) => h :: t.toScala
  }
}

final case class Cons[+T](h: T, t: List[T]) extends List[T]
final case class Nil[+T]() extends List[T]

object List {
  def empty[T]: List[T] = Nil()

  def apply[T](elems: T*): List[T] =
    elems.foldRight(empty[T])((e, acc) => Cons(e, acc))

  def fromScala[A](list: scala.collection.immutable.List[A]): List[A] =
    list.foldRight(empty[A])(Cons(_, _))
}
