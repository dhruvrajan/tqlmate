package tqlmate.cli

final case class TypeDbUrl(
  username: String,
  password: String,
  host: String,
  port: Int,
  database: String,
  tls: Boolean
) {
  def address: String = s"$host:$port"
}

object TypeDbUrl {
  val DefaultUsername = "admin"
  val DefaultPassword = "password"

  def parse(raw: String): Either[String, TypeDbUrl] = {
    if (!raw.startsWith("typedb://")) Left(s"URL must start with typedb://: $raw")
    else {
      val rest = raw.stripPrefix("typedb://")
      val authParsed: Either[String, (String, String, String)] =
        rest.lastIndexOf('@') match {
          case -1 => Right((DefaultUsername, DefaultPassword, rest))
          case at =>
            val auth = rest.substring(0, at)
            val after = rest.substring(at + 1)
            auth.split(":", 2) match {
              case Array(u, p) => Right((percentDecode(u), percentDecode(p), after))
              case _ => Left("URL auth must be user:pass")
            }
        }
      authParsed.flatMap { case (username, password, afterAuth) =>
        val slash = afterAuth.indexOf('/')
        if (slash < 0) Left("URL must include /database")
        else {
          val hostport = afterAuth.substring(0, slash)
          val pathQuery = afterAuth.substring(slash + 1)
          val q = pathQuery.indexOf('?')
          val (path, query) =
            if (q < 0) (pathQuery, "")
            else (pathQuery.substring(0, q), pathQuery.substring(q + 1))
          val hostPortParsed: Either[String, (String, Int)] =
            hostport.lastIndexOf(':') match {
              case -1 => Right((hostport, 1729))
              case i =>
                hostport.substring(i + 1).toIntOption match {
                  case Some(p) => Right((hostport.substring(0, i), p))
                  case None => Left(s"bad port: ${hostport.substring(i + 1)}")
                }
            }
          hostPortParsed.flatMap { case (host, port) =>
            val database = path.stripPrefix("/").stripSuffix("/")
            if (database.isEmpty) Left("database name required")
            else {
              var tls = false
              for (pair <- query.split('&') if pair.nonEmpty) {
                val parts = pair.split("=", 2)
                val k = parts(0)
                val v = if (parts.length > 1) parts(1) else ""
                if (k == "tls") tls = Set("true", "1", "yes").contains(v)
              }
              Right(TypeDbUrl(username, password, host, port, database, tls))
            }
          }
        }
      }
    }
  }

  def resolve(cliUrl: Option[String]): Either[String, TypeDbUrl] = {
    val raw = cliUrl
      .orElse(sys.env.get("TYPEDB_URL"))
      .orElse(sys.env.get("DATABASE_URL"))
      .getOrElse("typedb://admin:password@localhost:1729/typedb")
    parse(raw)
  }

  private def percentDecode(s: String): String = {
    val sb = new StringBuilder
    var i = 0
    while (i < s.length) {
      s.charAt(i) match {
        case '%' if i + 2 < s.length =>
          sb.append(Integer.parseInt(s.substring(i + 1, i + 3), 16).toChar)
          i += 3
        case '+' =>
          sb.append(' ')
          i += 1
        case c =>
          sb.append(c)
          i += 1
      }
    }
    sb.toString
  }
}
