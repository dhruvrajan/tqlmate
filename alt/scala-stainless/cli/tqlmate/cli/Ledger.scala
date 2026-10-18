package tqlmate.cli

import com.typedb.driver.api.Driver
import com.typedb.driver.api.Transaction
import com.typedb.driver.api.concept.Concept

import java.time.Instant
import java.time.ZoneOffset
import java.time.format.DateTimeFormatter
import scala.io.Source
import scala.jdk.CollectionConverters._
import scala.jdk.OptionConverters._

object Ledger {
  val Entity = "_tqlmate_schema_migration"
  val AttrVersion = "_tqlmate_version"
  val AttrAppliedAt = "_tqlmate_applied_at"
  val LedgerInitVersion = "00000000000001"
  val LedgerVersionLen = 14
  val LedgerVersionPrefix = "00000000"

  def isLedgerVersion(v: String): Boolean =
    v.length == LedgerVersionLen &&
      v.startsWith(LedgerVersionPrefix) &&
      v.forall(_.isDigit)

  def shippedMigrations(): Seq[MigrationFile] = {
    val filename = "00000000000001_ledger_init.tql"
    val stream = Option(getClass.getResourceAsStream(s"/ledger/$filename"))
      .getOrElse(sys.error(s"missing resource ledger/$filename"))
    val text = Source.fromInputStream(stream, "UTF-8").mkString
    stream.close()
    val (version, name) = MigrationFiles.parseVersionName(filename) match {
      case Right(x) => x
      case Left(e) => sys.error(e)
    }
    val (up, down) = MigrationFiles.splitUpDown(text) match {
      case Right(x) => x
      case Left(e) => sys.error(e)
    }
    Seq(
      MigrationFile(
        version,
        name,
        java.nio.file.Path.of(s"embedded:$filename"),
        up,
        down
      )
    )
  }

  def recordInsert(version: String, appliedAt: String): String =
    s"""insert $$_ isa $Entity, has $AttrVersion "$version", has $AttrAppliedAt $appliedAt;"""

  def recordDelete(version: String): String =
    s"""match $$m isa $Entity, has $AttrVersion "$version"; delete $$m;"""

  def schemaQueries(driver: Driver, database: String, queries: Seq[String]): Unit = {
    val tx = driver.transaction(database, Transaction.Type.SCHEMA)
    try {
      for (q <- queries) {
        val trimmed = q.trim
        if (trimmed.nonEmpty) {
          tx.query(trimmed).resolve()
        }
      }
      tx.commit()
    } catch {
      case e: Throwable =>
        try tx.close()
        catch { case _: Throwable => () }
        throw e
    }
  }

  def allAppliedVersions(driver: Driver, database: String): Seq[String] = {
    val tx = driver.transaction(database, Transaction.Type.READ)
    try {
      val answer = tx.query(s"match $$m isa $Entity, has $AttrVersion $$v;").resolve()
      if (!answer.isConceptRows) {
        tx.close()
        return Seq.empty
      }
      val rows = answer.asConceptRows()
      val versions = rows.asScala.flatMap { row =>
        row.get("v").asScala.flatMap((c: Concept) => c.tryGetString().asScala)
      }.toSeq.sorted
      tx.close()
      versions
    } catch {
      case _: Throwable =>
        try tx.close()
        catch { case _: Throwable => () }
        Seq.empty
    }
  }

  def appliedVersions(driver: Driver, database: String): Seq[String] =
    allAppliedVersions(driver, database).filterNot(isLedgerVersion)

  def ensure(driver: Driver, database: String): Unit = {
    val shipped = shippedMigrations()
    val appliedOpt =
      try Some(allAppliedVersions(driver, database))
      catch { case _: Throwable => None }
    val appliedSet = appliedOpt.map(_.toSet).getOrElse(Set.empty[String])
    for (m <- shipped if !appliedSet.contains(m.version)) {
      if (appliedOpt.isEmpty) {
        applyLedgerUp(driver, database, m)
      } else if (m.version == LedgerInitVersion) {
        stamp(driver, database, m.version)
      } else {
        applyLedgerUp(driver, database, m)
      }
    }
  }

  def nowStamp: String =
    DateTimeFormatter
      .ofPattern("yyyy-MM-dd'T'HH:mm:ss")
      .withZone(ZoneOffset.UTC)
      .format(Instant.now())

  private def applyLedgerUp(driver: Driver, database: String, m: MigrationFile): Unit =
    schemaQueries(driver, database, Seq(m.up, recordInsert(m.version, nowStamp)))

  private def stamp(driver: Driver, database: String, version: String): Unit =
    schemaQueries(driver, database, Seq(recordInsert(version, nowStamp)))

  def dumpHeader(applied: Seq[String], files: Seq[MigrationFile]): String = {
    val sb = new StringBuilder("-- Schema dumped by tqlmate\n-- Applied migrations:\n")
    if (applied.isEmpty) sb.append("--   (none)\n")
    else
      for (v <- applied) {
        val label = files.find(_.version == v).map(_.label).getOrElse(v)
        sb.append(s"--   $label\n")
      }
    sb.append('\n')
    sb.toString
  }

  def stripDumpHeader(text: String): String = {
    val lines = text.split("\n", -1)
    var started = false
    val out = new StringBuilder
    var first = true
    for (line <- lines) {
      if (!started) {
        val t = line.trim
        if (t.isEmpty || t.startsWith("--")) ()
        else started = true
      }
      if (started) {
        if (!first) out.append('\n')
        out.append(line)
        first = false
      }
    }
    out.toString
  }
}
