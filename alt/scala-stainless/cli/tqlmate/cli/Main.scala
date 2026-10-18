package tqlmate.cli

import java.nio.file.Path
import java.time.Duration

object Main {

  sealed trait Command
  object Command {
    case class New(name: String) extends Command
    case object Up extends Command
    case object Create extends Command
    case object Drop extends Command
    case object Migrate extends Command
    case object Rollback extends Command
    case class Status(exitCode: Boolean, quiet: Boolean) extends Command
    case object Dump extends Command
    case object Load extends Command
    case class Wait(timeout: Long) extends Command
  }

  final case class Cli(
    url: Option[String],
    migrationsDir: Option[Path],
    schemaFile: Option[Path],
    waitSecs: Option[Long],
    waitInterval: Long,
    strict: Boolean,
    verbose: Boolean,
    command: Command
  )

  def main(args: Array[String]): Unit = {
    try {
      val code = run(args)
      System.exit(code)
    } catch {
      case e: Throwable =>
        val msg = Option(e.getMessage).orElse(Option(e.getCause).map(_.getMessage)).getOrElse(e.toString)
        System.err.println(s"Error: $msg")
        if (sys.env.contains("TQLMATE_TRACE")) e.printStackTrace(System.err)
        System.exit(1)
    }
  }

  def run(args: Array[String]): Int = {
    val cli = parseArgs(args.toList)
    val url = cli.command match {
      case Command.New(_) => None
      case _ =>
        Some(TypeDbUrl.resolve(cli.url).fold(e => throw new RuntimeException(e), identity))
    }
    val opts = Opts(
      url = url,
      migrationsDir = cli.migrationsDir.getOrElse(
        Path.of(sys.env.getOrElse("TQLMATE_MIGRATIONS_DIR", "db/migrations"))
      ),
      schemaFile = cli.schemaFile.getOrElse(
        Path.of(sys.env.getOrElse("TQLMATE_SCHEMA_FILE", "db/schema.tql"))
      ),
      strict = cli.strict,
      verbose = cli.verbose,
      waitTimeout = cli.waitSecs.map(Duration.ofSeconds),
      waitInterval = Duration.ofSeconds(cli.waitInterval)
    )
    val runner = new Runner(opts)
    try {
      cli.command match {
        case Command.New(name) => runner.newMigration(name)
        case Command.Up => runner.up()
        case Command.Create => runner.create()
        case Command.Drop => runner.drop()
        case Command.Migrate => runner.migrate()
        case Command.Rollback => runner.rollback()
        case Command.Status(exitCode, quiet) =>
          val pending = runner.status(quiet)
          if (exitCode && pending) return 1
        case Command.Dump => runner.dump()
        case Command.Load => runner.load()
        case Command.Wait(timeout) =>
          val secs = cli.waitSecs.getOrElse(timeout)
          runner.waitCmd(Duration.ofSeconds(secs))
      }
      0
    } finally {
      runner.close()
    }
  }

  def parseArgs(args: List[String]): Cli = {
    var url: Option[String] = None
    var migrationsDir: Option[Path] = None
    var schemaFile: Option[Path] = None
    var waitSecs: Option[Long] = None
    var waitInterval: Long = 1L
    var strict = sys.env.get("TQLMATE_STRICT").exists(v => v == "1" || v.equalsIgnoreCase("true"))
    var verbose = false
    var rest = args

    def takeValue(flag: String, xs: List[String]): (String, List[String]) = xs match {
      case v :: tail => (v, tail)
      case Nil => throw new RuntimeException(s"missing value for $flag")
    }

    while (rest.nonEmpty && rest.head.startsWith("-")) {
      rest match {
        case ("-u" | "--url") :: xs =>
          val (v, t) = takeValue("--url", xs); url = Some(v); rest = t
        case ("-d" | "--migrations-dir") :: xs =>
          val (v, t) = takeValue("--migrations-dir", xs)
          migrationsDir = Some(Path.of(v)); rest = t
        case "--schema-file" :: xs =>
          val (v, t) = takeValue("--schema-file", xs)
          schemaFile = Some(Path.of(v)); rest = t
        case "--wait" :: xs =>
          val (v, t) = takeValue("--wait", xs)
          waitSecs = Some(v.toLong); rest = t
        case "--wait-interval" :: xs =>
          val (v, t) = takeValue("--wait-interval", xs)
          waitInterval = v.toLong; rest = t
        case "--strict" :: xs =>
          strict = true; rest = xs
        case ("-v" | "--verbose") :: xs =>
          verbose = true; rest = xs
        case ("-h" | "--help") :: _ =>
          printHelp(); System.exit(0); ???
        case other :: _ =>
          throw new RuntimeException(s"unknown option: $other")
        case Nil => ()
      }
    }

    val command = rest match {
      case "new" :: name :: Nil => Command.New(name)
      case "up" :: Nil => Command.Up
      case "create" :: Nil => Command.Create
      case "drop" :: Nil => Command.Drop
      case "migrate" :: Nil => Command.Migrate
      case ("rollback" | "down") :: Nil => Command.Rollback
      case "status" :: xs =>
        var exitCode = false
        var quiet = false
        var s = xs
        while (s.nonEmpty) s match {
          case "--exit-code" :: t => exitCode = true; s = t
          case "--quiet" :: t => quiet = true; s = t
          case other :: _ => throw new RuntimeException(s"unknown status flag: $other")
          case Nil => ()
        }
        Command.Status(exitCode, quiet)
      case "dump" :: Nil => Command.Dump
      case "load" :: Nil => Command.Load
      case "wait" :: xs =>
        var timeout = 60L
        var s = xs
        while (s.nonEmpty) s match {
          case "--timeout" :: v :: t => timeout = v.toLong; s = t
          case other :: _ => throw new RuntimeException(s"unknown wait flag: $other")
          case Nil => ()
        }
        Command.Wait(timeout)
      case Nil =>
        printHelp(); throw new RuntimeException("missing command")
      case other =>
        throw new RuntimeException(s"unknown command: ${other.mkString(" ")}")
    }

    Cli(url, migrationsDir, schemaFile, waitSecs, waitInterval, strict, verbose, command)
  }

  def printHelp(): Unit = {
    println(
      """tqlmate-scala — TypeDB 3.x migration CLI (Scala + Stainless prototype)
        |
        |Usage: tqlmate-scala [options] <command>
        |
        |Commands:
        |  new <name>     Create a timestamped migration
        |  up             Create database + migrate
        |  create / drop  Create or delete the database
        |  migrate        Apply pending migrations
        |  rollback|down  Roll back latest applied migration
        |  status         List applied / pending (--exit-code, --quiet)
        |  dump / load    Dump or load schema file
        |  wait           Block until TypeDB accepts connections
        |
        |Options:
        |  -u, --url URL
        |  -d, --migrations-dir DIR
        |      --schema-file PATH
        |      --wait SECS
        |      --wait-interval SECS
        |      --strict
        |  -v, --verbose
        |""".stripMargin
    )
  }
}
