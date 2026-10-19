package tqlmate.bridge

import stainless.collection.{Cons, List, Nil}
import tqlmate.core.Codes.{Code, Codes}
import tqlmate.core.Pure

/** Convert between JVM `String` and the verified `List[BigInt]` code representation. */
object Codec {

  def toCodes(s: String): Codes = {
    val buf = scala.collection.mutable.ListBuffer.empty[Code]
    var i = 0
    while (i < s.length) {
      val cp = s.codePointAt(i)
      buf += BigInt(cp)
      i += Character.charCount(cp)
    }
    List.fromScala(buf.toList)
  }

  def fromCodes(cs: Codes): String = {
    val sb = new java.lang.StringBuilder
    def go(xs: Codes): Unit = xs match {
      case Nil() => ()
      case Cons(h, t) =>
        sb.appendCodePoint(h.intValue)
        go(t)
    }
    go(cs)
    sb.toString
  }

  def version(s: String): Pure.Version = Pure.Version(toCodes(s))

  def versionStr(v: Pure.Version): String = fromCodes(v.codes)

  def versions(ss: Seq[String]): List[Pure.Version] =
    List.fromScala(ss.map(version).toList)

  def versionsScala(vs: List[Pure.Version]): Seq[String] =
    vs.toScala.map(versionStr)

  def spec(version: String, name: String, up: String, down: String): Pure.MigrationSpec =
    Pure.MigrationSpec(
      Pure.Version(toCodes(version)),
      toCodes(name),
      toCodes(up),
      toCodes(down)
    )

  def specs(files: Seq[(String, String, String, String)]): List[Pure.MigrationSpec] =
    List.fromScala(files.map { case (v, n, u, d) => spec(v, n, u, d) }.toList)
}
