package tqlmate.core

import stainless.collection._
import stainless.lang._
import stainless.lang.StaticChecks._

/**
 * Digit-only version identifiers as lists of ASCII code points.
 *
 * Stainless models `String` thinly; list-of-`BigInt` codes admit inductive proofs
 * for lexicographic order and membership matching `src/pure.rs` / Verus.
 */
object Codes {

  type Code = BigInt
  type Codes = List[Code]

  def isAsciiDigit(c: Code): Boolean = c >= 48 && c <= 57

  def isAsciiWs(c: Code): Boolean =
    c == 32 || c == 9 || c == 10 || c == 13

  def isAsciiAlnum(c: Code): Boolean =
    isAsciiDigit(c) ||
      (c >= 65 && c <= 90) ||
      (c >= 97 && c <= 122)

  def asciiLower(c: Code): Code = {
    if (c >= 65 && c <= 90) c + 32 else c
  }

  def allDigits(cs: Codes): Boolean = {
    decreases(cs)
    cs match {
      case Nil() => true
      case Cons(h, t) => isAsciiDigit(h) && allDigits(t)
    }
  }

  def nonEmptyDigits(cs: Codes): Boolean =
    cs != Nil[Code]() && allDigits(cs)

  def bodyIsEmpty(cs: Codes): Boolean = {
    decreases(cs)
    cs match {
      case Nil() => true
      case Cons(h, t) => isAsciiWs(h) && bodyIsEmpty(t)
    }
  }

  /** Lexicographic order on code lists (same as digit-string `<` for equal-length versions). */
  def codesLt(a: Codes, b: Codes): Boolean = {
    decreases(a, b)
    (a, b) match {
      case (Nil(), Nil()) => false
      case (Nil(), Cons(_, _)) => true
      case (Cons(_, _), Nil()) => false
      case (Cons(ha, ta), Cons(hb, tb)) =>
        if (ha < hb) true
        else if (ha > hb) false
        else codesLt(ta, tb)
    }
  }

  def codesEq(a: Codes, b: Codes): Boolean = {
    decreases(a, b)
    (a, b) match {
      case (Nil(), Nil()) => true
      case (Cons(ha, ta), Cons(hb, tb)) => ha == hb && codesEq(ta, tb)
      case _ => false
    }
  }.ensuring(res => res == (a == b))
}
