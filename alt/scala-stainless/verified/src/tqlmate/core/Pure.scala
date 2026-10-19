package tqlmate.core

import stainless.annotation._
import stainless.collection._
import stainless.lang._
import stainless.lang.StaticChecks._

import Codes._

/**
 * Pure migrate / rollback plan + abstract interpreter.
 *
 * Mirrors `src/pure.rs` / `verification/verus` decision core. TypeDB I/O is outside
 * this module (trusted effect boundary).
 */
object Pure {

  case class Version(codes: Codes)

  case class MigrationSpec(
    version: Version,
    name: Codes,
    up: Codes,
    down: Codes
  )

  sealed abstract class Op
  case class ApplyUp(version: Version, up: Codes) extends Op
  case class ApplyDown(version: Version, down: Codes) extends Op

  case class State(applied: List[Version])

  sealed abstract class StepError
  case class EmptyUp(version: Version) extends StepError
  case class EmptyDown(version: Version) extends StepError

  sealed abstract class PlanError
  case class PlanEmptyUp(version: Version) extends PlanError
  case class PlanEmptyDown(version: Version, name: Codes) extends PlanError
  case class MissingFile(version: Version) extends PlanError
  case class StrictOrder(pending: Version, appliedUpTo: Version) extends PlanError

  def versionEq(a: Version, b: Version): Boolean =
    codesEq(a.codes, b.codes)

  def versionLt(a: Version, b: Version): Boolean =
    codesLt(a.codes, b.codes)

  def versionIn(applied: List[Version], v: Version): Boolean = {
    decreases(applied)
    applied match {
      case Nil() => false
      case Cons(h, t) => versionEq(h, v) || versionIn(t, v)
    }
  }

  def lastOf(xs: List[Version]): Version = {
    require(xs != Nil[Version]())
    decreases(xs)
    xs match {
      case Cons(h, Nil()) => h
      case Cons(_, t) => lastOf(t)
      case Nil() => Version(Nil[Code]())
    }
  }

  def initOf(xs: List[Version]): List[Version] = {
    require(xs != Nil[Version]())
    decreases(xs)
    xs match {
      case Cons(_, Nil()) => Nil[Version]()
      case Cons(h, t) => Cons(h, initOf(t))
      case Nil() => Nil[Version]()
    }
  }.ensuring(res => res.size == xs.size - 1)

  /** Spec / executable remove-last-match (end-recursive), matching Verus. */
  def removeLastMatchingSpec(applied: List[Version], v: Version): List[Version] = {
    decreases(applied.size)
    applied match {
      case Nil() => Nil[Version]()
      case Cons(_, _) =>
        val last = lastOf(applied)
        val pref = initOf(applied)
        // initOf ensures pref.size == applied.size - 1
        if (versionEq(last, v)) pref
        else removeLastMatchingSpec(pref, v) :+ last
    }
  }

  def removeLastMatching(applied: List[Version], v: Version): List[Version] =
    removeLastMatchingSpec(applied, v)

  def step(state: State, op: Op): Either[StepError, State] = {
    op match {
      case ApplyUp(version, up) =>
        if (bodyIsEmpty(up)) {
          Left[StepError, State](EmptyUp(version))
        } else {
          Right[StepError, State](State(state.applied :+ version))
        }
      case ApplyDown(version, down) =>
        if (bodyIsEmpty(down)) {
          Left[StepError, State](EmptyDown(version))
        } else {
          Right[StepError, State](
            State(removeLastMatching(state.applied, version))
          )
        }
    }
  }.ensuring(res => stepPost(state, op, res))

  def stepPost(state: State, op: Op, res: Either[StepError, State]): Boolean = {
    op match {
      case ApplyUp(version, up) =>
        if (bodyIsEmpty(up)) {
          res match {
            case Left(EmptyUp(ev)) => versionEq(ev, version)
            case _ => false
          }
        } else {
          res match {
            case Right(s) => s.applied == (state.applied :+ version)
            case _ => false
          }
        }
      case ApplyDown(version, down) =>
        if (bodyIsEmpty(down)) {
          res match {
            case Left(EmptyDown(ev)) => versionEq(ev, version)
            case _ => false
          }
        } else {
          res match {
            case Right(s) =>
              s.applied == removeLastMatchingSpec(state.applied, version)
            case _ => false
          }
        }
    }
  }

  def run(state: State, plan: List[Op]): Either[StepError, State] = {
    decreases(plan)
    plan match {
      case Nil() =>
        Right[StepError, State](state)
      case Cons(op, rest) =>
        step(state, op) match {
          case Left(e) => Left[StepError, State](e)
          case Right(next) => run(next, rest)
        }
    }
  }.ensuring(res =>
    (plan == Nil[Op]()) ==> (
      res match {
        case Right(s) => s == state
        case _ => false
      }
    )
  )

  def pendingSpecs(files: List[MigrationSpec], applied: List[Version]): List[MigrationSpec] = {
    decreases(files)
    files match {
      case Nil() => Nil[MigrationSpec]()
      case Cons(f, rest) =>
        if (!versionIn(applied, f.version)) {
          Cons(f, pendingSpecs(rest, applied))
        } else {
          pendingSpecs(rest, applied)
        }
    }
  }.ensuring(res =>
    ((files == Nil[MigrationSpec]()) ==> (res == Nil[MigrationSpec]())) &&
      pendingAllNotApplied(res, applied)
  )

  def pendingAllNotApplied(pending: List[MigrationSpec], applied: List[Version]): Boolean = {
    decreases(pending)
    pending match {
      case Nil() => true
      case Cons(f, rest) =>
        !versionIn(applied, f.version) && pendingAllNotApplied(rest, applied)
    }
  }

  def planUpsFromPending(pending: List[MigrationSpec]): Either[PlanError, List[Op]] = {
    decreases(pending)
    pending match {
      case Nil() => Right[PlanError, List[Op]](Nil[Op]())
      case Cons(f, rest) =>
        if (bodyIsEmpty(f.up)) {
          Left[PlanError, List[Op]](PlanEmptyUp(f.version))
        } else {
          planUpsFromPending(rest) match {
            case Left(e) => Left[PlanError, List[Op]](e)
            case Right(tail) =>
              Right[PlanError, List[Op]](Cons(ApplyUp(f.version, f.up), tail))
          }
        }
    }
  }.ensuring(res =>
    (pending == Nil[MigrationSpec]()) ==> (
      res match {
        case Right(p) => p == Nil[Op]()
        case _ => false
      }
    )
  )

  def maxVersion(applied: List[Version]): Option[Version] = {
    decreases(applied)
    applied match {
      case Nil() => None[Version]()
      case Cons(h, Nil()) => Some(h)
      case Cons(h, t) =>
        maxVersion(t) match {
          case None() => Some(h)
          case Some(best) =>
            if (versionLt(h, best)) Some(best) else Some(h)
        }
    }
  }.ensuring(res =>
    ((applied == Nil[Version]()) ==> (res == None[Version]())) &&
      ((applied != Nil[Version]()) ==> res.isDefined)
  )

  def checkStrictOrder(
    files: List[MigrationSpec],
    applied: List[Version]
  ): Either[PlanError, Unit] = {
    decreases(files)
    maxVersion(applied) match {
      case None() => Right[PlanError, Unit](())
      case Some(max) =>
        files match {
          case Nil() => Right[PlanError, Unit](())
          case Cons(f, rest) =>
            if (!versionIn(applied, f.version) && versionLt(f.version, max)) {
              Left[PlanError, Unit](StrictOrder(f.version, max))
            } else {
              checkStrictOrder(rest, applied)
            }
        }
    }
  }

  def planMigrate(
    files: List[MigrationSpec],
    applied: List[Version],
    strict: Boolean
  ): Either[PlanError, List[Op]] = {
    if (strict) {
      checkStrictOrder(files, applied) match {
        case Left(e) => Left[PlanError, List[Op]](e)
        case Right(_) =>
          planUpsFromPending(pendingSpecs(files, applied))
      }
    } else {
      planUpsFromPending(pendingSpecs(files, applied))
    }
  }.ensuring(res =>
    (!strict && files == Nil[MigrationSpec]()) ==> (
      res match {
        case Right(p) => p == Nil[Op]()
        case _ => false
      }
    )
  )

  def findSpec(files: List[MigrationSpec], v: Version): Option[MigrationSpec] = {
    decreases(files)
    files match {
      case Nil() => None[MigrationSpec]()
      case Cons(f, rest) =>
        if (versionEq(f.version, v)) Some(f) else findSpec(rest, v)
    }
  }

  def planRollback(
    files: List[MigrationSpec],
    applied: List[Version]
  ): Either[PlanError, List[Op]] = {
    applied match {
      case Nil() =>
        Right[PlanError, List[Op]](Nil[Op]())
      case Cons(_, _) =>
        val version = lastOf(applied)
        findSpec(files, version) match {
          case None() =>
            Left[PlanError, List[Op]](MissingFile(version))
          case Some(m) =>
            if (bodyIsEmpty(m.down)) {
              Left[PlanError, List[Op]](PlanEmptyDown(m.version, m.name))
            } else {
              Right[PlanError, List[Op]](
                Cons(ApplyDown(m.version, m.down), Nil[Op]())
              )
            }
        }
    }
  }.ensuring(res =>
    (applied == Nil[Version]()) ==> (
      res match {
        case Right(p) => p == Nil[Op]()
        case _ => false
      }
    )
  )
}
