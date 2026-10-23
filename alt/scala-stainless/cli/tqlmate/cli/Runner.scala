package tqlmate.cli

import com.typedb.driver.TypeDB
import com.typedb.driver.api.{Credentials, Driver, DriverOptions, DriverTlsConfig}
import tqlmate.bridge.{BridgeOp, BridgePlanError, PlanBridge}

import java.nio.file.{Files, Path}
import java.time.Duration
import scala.util.control.NonFatal

final case class Opts(
  url: Option[TypeDbUrl],
  migrationsDir: Path,
  schemaFile: Path,
  strict: Boolean,
  verbose: Boolean,
  waitTimeout: Option[Duration],
  waitInterval: Duration
)

final class Runner(opts: Opts) {
  private var driver: Option[Driver] = None

  private def url: TypeDbUrl =
    opts.url.getOrElse(sys.error("TypeDB URL required for this command"))

  private def connect(): Driver = {
    if (driver.isEmpty) {
      opts.waitTimeout.foreach(t =>
        RunnerHelpers.waitForServer(url, t, opts.waitInterval, opts.verbose)
      )
      driver = Some(RunnerHelpers.openDriver(url))
    }
    driver.get
  }

  def close(): Unit = {
    driver.foreach(_.close())
    driver = None
  }

  def newMigration(name: String): Path = {
    Files.createDirectories(opts.migrationsDir)
    val path = MigrationFiles.newPath(opts.migrationsDir, name)
    Files.writeString(path, MigrationFiles.template)
    println(s"Created: $path")
    path
  }

  def create(): Unit = {
    val d = connect()
    val name = url.database
    if (d.databases().contains(name)) {
      if (opts.verbose) System.err.println(s"database already exists: $name")
    } else {
      d.databases().create(name)
      println(s"Created: $name")
    }
  }

  def drop(): Unit = {
    val d = connect()
    val name = url.database
    if (!d.databases().contains(name)) {
      if (opts.verbose) System.err.println(s"database does not exist: $name")
    } else {
      d.databases().get(name).delete()
      println(s"Dropped: $name")
    }
  }

  def migrate(): Unit = {
    val d = connect()
    val db = url.database
    if (!d.databases().contains(db))
      throw new RuntimeException(s"database does not exist: $db")
    Ledger.ensure(d, db)
    val files = MigrationFiles.list(opts.migrationsDir).fold(e => throw new RuntimeException(e), identity)
    val applied = Ledger.appliedVersions(d, db)
    val specs = files.map(f => PlanBridge.FileSpec(f.version, f.name, f.up, f.down))
    PlanBridge.planMigrate(specs, applied, opts.strict) match {
      case Left(err) => throw new RuntimeException(formatPlanError(err))
      case Right(plan) if plan.isEmpty =>
        if (opts.verbose) System.err.println("Migrations: nothing to apply")
      case Right(plan) =>
        executePlan(d, db, files, plan)
    }
  }

  def rollback(): Unit = {
    val d = connect()
    val db = url.database
    Ledger.ensure(d, db)
    val files = MigrationFiles.list(opts.migrationsDir).fold(e => throw new RuntimeException(e), identity)
    val applied = Ledger.appliedVersions(d, db)
    val specs = files.map(f => PlanBridge.FileSpec(f.version, f.name, f.up, f.down))
    PlanBridge.planRollback(specs, applied) match {
      case Left(err) => throw new RuntimeException(formatPlanError(err))
      case Right(plan) if plan.isEmpty =>
        if (opts.verbose) System.err.println("Rollback: nothing to roll back")
      case Right(plan) =>
        executePlan(d, db, files, plan)
    }
  }

  def status(quiet: Boolean): Boolean = {
    val d = connect()
    val db = url.database
    val applied =
      if (d.databases().contains(db)) Ledger.appliedVersions(d, db) else Seq.empty
    val files = MigrationFiles.list(opts.migrationsDir).fold(e => throw new RuntimeException(e), identity)
    if (opts.strict) {
      val specs = files.map(f => PlanBridge.FileSpec(f.version, f.name, f.up, f.down))
      PlanBridge.planMigrate(specs, applied, strict = true) match {
        case Left(BridgePlanError.StrictOrder(p, a)) =>
          throw new RuntimeException(s"strict order: pending $p < applied $a")
        case Left(err) => throw new RuntimeException(formatPlanError(err))
        case Right(_) => ()
      }
    }
    var pending = false
    if (!quiet) {
      if (files.isEmpty) println("No migrations found.")
      for (f <- files) {
        val mark = if (applied.contains(f.version)) "[X]" else { pending = true; "[ ]" }
        println(s"$mark ${f.label}")
      }
    } else {
      pending = files.exists(f => !applied.contains(f.version))
    }
    pending
  }

  def dump(): Unit = {
    val d = connect()
    val dbName = url.database
    val schema = d.databases().get(dbName).schema()
    val applied =
      try Ledger.appliedVersions(d, dbName)
      catch { case NonFatal(_) => Seq.empty }
    val files = MigrationFiles.list(opts.migrationsDir).fold(e => throw new RuntimeException(e), identity)
    Option(opts.schemaFile.getParent).foreach(Files.createDirectories(_))
    val out = Ledger.dumpHeader(applied, files) + schema.trim + "\n"
    Files.writeString(opts.schemaFile, out)
    println(s"Wrote: ${opts.schemaFile}")
  }

  def load(): Unit = {
    val text = Files.readString(opts.schemaFile)
    val body = Ledger.stripDumpHeader(text).trim
    if (body.isEmpty) throw new RuntimeException("empty schema file")
    val d = connect()
    val db = url.database
    if (!d.databases().contains(db)) d.databases().create(db)
    Ledger.schemaQueries(d, db, Seq(body))
    println(s"Loaded: ${opts.schemaFile}")
  }

  def waitCmd(timeout: Duration): Unit =
    RunnerHelpers.waitForServer(url, timeout, opts.waitInterval, opts.verbose)

  def up(): Unit = {
    create()
    migrate()
  }

  private def executePlan(
    d: Driver,
    db: String,
    files: Seq[MigrationFile],
    plan: Seq[BridgeOp]
  ): Unit = {
    for (op <- plan) op match {
      case BridgeOp.ApplyUp(version, up, record) =>
        if (up.trim.isEmpty) throw new RuntimeException(s"empty up for $version")
        if (opts.verbose) System.err.println(s"-> up $version")
        if (record) {
          val insert = Ledger.recordInsert(version, Ledger.nowStamp)
          Ledger.schemaQueries(d, db, Seq(up, insert))
          val label = files.find(_.version == version).map(_.label).getOrElse(version)
          println(s"Applied: $label")
        } else {
          Ledger.schemaQueries(d, db, Seq(up))
        }
      case BridgeOp.ApplyDown(version, down, delete) =>
        if (down.trim.isEmpty) throw new RuntimeException(s"empty down for $version")
        if (opts.verbose) System.err.println(s"-> down $version")
        if (delete) {
          val del = Ledger.recordDelete(version)
          Ledger.schemaQueries(d, db, Seq(down, del))
          val label = files.find(_.version == version).map(_.label).getOrElse(version)
          println(s"Rolled back: $label")
        } else {
          Ledger.schemaQueries(d, db, Seq(down))
        }
    }
  }

  private def formatPlanError(err: BridgePlanError): String = err match {
    case BridgePlanError.EmptyUp(v) => s"empty migrate:up for $v"
    case BridgePlanError.EmptyDown(v, n) => s"empty migrate:down for ${v}_$n"
    case BridgePlanError.MissingFile(v) => s"missing migration file for $v"
    case BridgePlanError.StrictOrder(p, a) => s"strict order: pending $p < applied $a"
  }
}

object RunnerHelpers {
  def openDriver(url: TypeDbUrl): Driver = {
    val creds = new Credentials(url.username, url.password)
    val tls =
      if (url.tls) DriverTlsConfig.enabledWithNativeRootCA()
      else DriverTlsConfig.disabled()
    TypeDB.driver(url.address, creds, new DriverOptions(tls))
  }

  def waitForServer(
    url: TypeDbUrl,
    timeout: Duration,
    interval: Duration,
    verbose: Boolean
  ): Unit = {
    val start = System.nanoTime()
    val iv = if (interval.isZero) Duration.ofSeconds(1) else interval
    while (true) {
      try {
        val d = openDriver(url)
        d.close()
        if (verbose) System.err.println(s"TypeDB available at ${url.address}")
        return
      } catch {
        case NonFatal(e) =>
          val elapsed = Duration.ofNanos(System.nanoTime() - start)
          if (elapsed.compareTo(timeout) >= 0)
            throw new RuntimeException(
              s"wait timeout for ${url.address}: ${e.getMessage}",
              e
            )
          if (verbose) System.err.println(s"waiting for TypeDB at ${url.address} ($e)")
          Thread.sleep(iv.toMillis)
      }
    }
  }
}
