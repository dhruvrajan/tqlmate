package tqlmate.cli

import java.nio.file.{Files, Path}
import java.time.Instant
import java.time.ZoneOffset
import java.time.format.DateTimeFormatter
import scala.jdk.CollectionConverters._
import scala.util.matching.Regex

final case class MigrationFile(
  version: String,
  name: String,
  path: Path,
  up: String,
  down: String
) {
  def label: String = s"${version}_$name"
}

object MigrationFiles {
  private val VersionName: Regex = """^(\d+)_(.+)\.tql$""".r

  def parseVersionName(filename: String): Either[String, (String, String)] =
    filename match {
      case VersionName(v, name) if name.nonEmpty => Right((v, name))
      case _ if !filename.endsWith(".tql") => Left(s"migration must end in .tql: $filename")
      case _ => Left(s"expected VERSION_name.tql: $filename")
    }

  def splitUpDown(text: String): Either[String, (String, String)] = {
    var section: Option[String] = None
    val up = new StringBuilder
    val down = new StringBuilder
    var saw = false
    for (raw <- text.split("\n", -1)) {
      val line = if (raw.endsWith("\r")) raw.dropRight(1) else raw
      migrationMarker(line) match {
        case Some(m) =>
          section = Some(m)
          saw = true
        case None =>
          section match {
            case Some("up") =>
              up.append(line); up.append('\n')
            case Some("down") =>
              down.append(line); down.append('\n')
            case _ => ()
          }
      }
    }
    if (!saw && up.isEmpty && down.isEmpty) Left("missing -- migrate:up / -- migrate:down markers")
    else Right((up.toString.trim, down.toString.trim))
  }

  private def migrationMarker(line: String): Option[String] = {
    val t = line.trim
    if (!t.startsWith("--")) return None
    val marker = t.stripPrefix("--").trim.toLowerCase
    if (marker == "migrate:up") Some("up")
    else if (marker == "migrate:down") Some("down")
    else None
  }

  def parseFile(path: Path): Either[String, MigrationFile] = {
    val filename = path.getFileName.toString
    for {
      vn <- parseVersionName(filename)
      text = Files.readString(path)
      ud <- splitUpDown(text)
    } yield MigrationFile(vn._1, vn._2, path, ud._1, ud._2)
  }

  def list(dir: Path): Either[String, Seq[MigrationFile]] = {
    if (!Files.exists(dir)) return Right(Seq.empty)
    val files = Files.list(dir).iterator().asScala.toSeq
      .filter(p => p.getFileName.toString.endsWith(".tql"))
    val parsed = files.map(parseFile)
    parsed.collectFirst { case Left(e) => e } match {
      case Some(err) => Left(err)
      case None =>
        val ok = parsed.collect { case Right(f) => f }.sortBy(_.version)
        ok.sliding(2).collectFirst {
          case Seq(a, b) if a.version == b.version =>
            s"duplicate version ${a.version}"
        } match {
          case Some(err) => Left(err)
          case None => Right(ok)
        }
    }
  }

  def slugify(name: String): String = {
    val sb = new StringBuilder
    for (c <- name) {
      if (c.isLetterOrDigit) sb.append(c.toLower)
      else if (sb.isEmpty || sb.last != '_') sb.append('_')
    }
    val t = sb.toString.dropWhile(_ == '_').reverse.dropWhile(_ == '_').reverse
    if (t.isEmpty) "migration" else t
  }

  def template: String = "-- migrate:up\n\n\n-- migrate:down\n\n"

  def newPath(dir: Path, name: String): Path = {
    val ts = DateTimeFormatter
      .ofPattern("yyyyMMddHHmmss")
      .withZone(ZoneOffset.UTC)
      .format(Instant.now())
    dir.resolve(s"${ts}_${slugify(name)}.tql")
  }
}
