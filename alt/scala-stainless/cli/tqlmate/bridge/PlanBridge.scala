package tqlmate.bridge

import stainless.collection.{Cons, List, Nil}
import stainless.lang.{Left, Right}
import tqlmate.core.Pure
import tqlmate.core.Pure._

sealed trait BridgeOp
object BridgeOp {
  case class ApplyUp(version: String, up: String) extends BridgeOp
  case class ApplyDown(version: String, down: String) extends BridgeOp
}

sealed trait BridgePlanError
object BridgePlanError {
  case class EmptyUp(version: String) extends BridgePlanError
  case class EmptyDown(version: String, name: String) extends BridgePlanError
  case class MissingFile(version: String) extends BridgePlanError
  case class StrictOrder(pending: String, appliedUpTo: String) extends BridgePlanError
}

/** Thin String-facing wrapper around the verified Pure planner. */
object PlanBridge {

  case class FileSpec(version: String, name: String, up: String, down: String)

  def planMigrate(
    files: Seq[FileSpec],
    applied: Seq[String],
    strict: Boolean
  ): Either[BridgePlanError, Seq[BridgeOp]] = {
    val specs = Codec.specs(files.map(f => (f.version, f.name, f.up, f.down)))
    val apps = Codec.versions(applied)
    Pure.planMigrate(specs, apps, strict) match {
      case Left(e) => scala.Left(mapErr(e))
      case Right(plan) => scala.Right(toOps(plan))
    }
  }

  def planRollback(
    files: Seq[FileSpec],
    applied: Seq[String]
  ): Either[BridgePlanError, Seq[BridgeOp]] = {
    val specs = Codec.specs(files.map(f => (f.version, f.name, f.up, f.down)))
    val apps = Codec.versions(applied)
    Pure.planRollback(specs, apps) match {
      case Left(e) => scala.Left(mapErr(e))
      case Right(plan) => scala.Right(toOps(plan))
    }
  }

  def abstractRun(applied: Seq[String], plan: Seq[BridgeOp]): Either[String, Seq[String]] = {
    val state = State(Codec.versions(applied))
    val ops = fromOps(plan)
    Pure.run(state, ops) match {
      case Left(e) => scala.Left(e.toString)
      case Right(s) => scala.Right(Codec.versionsScala(s.applied))
    }
  }

  private def toOps(plan: List[Op]): Seq[BridgeOp] = plan.toScala.map {
    case ApplyUp(v, up) => BridgeOp.ApplyUp(Codec.versionStr(v), Codec.fromCodes(up))
    case ApplyDown(v, down) => BridgeOp.ApplyDown(Codec.versionStr(v), Codec.fromCodes(down))
  }

  private def fromOps(plan: Seq[BridgeOp]): List[Op] =
    List.fromScala(plan.map {
      case BridgeOp.ApplyUp(v, up) => ApplyUp(Codec.version(v), Codec.toCodes(up))
      case BridgeOp.ApplyDown(v, down) => ApplyDown(Codec.version(v), Codec.toCodes(down))
    }.toList)

  private def mapErr(e: PlanError): BridgePlanError = e match {
    case PlanEmptyUp(v) => BridgePlanError.EmptyUp(Codec.versionStr(v))
    case PlanEmptyDown(v, name) =>
      BridgePlanError.EmptyDown(Codec.versionStr(v), Codec.fromCodes(name))
    case MissingFile(v) => BridgePlanError.MissingFile(Codec.versionStr(v))
    case StrictOrder(p, a) =>
      BridgePlanError.StrictOrder(Codec.versionStr(p), Codec.versionStr(a))
  }
}
