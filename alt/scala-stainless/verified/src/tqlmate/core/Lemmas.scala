package tqlmate.core

import stainless.annotation._
import stainless.collection._
import stainless.lang._
import stainless.lang.StaticChecks._
import stainless.proof.check

import Codes._
import Pure._

/**
 * Explicit lemmas / derived properties matching Verus + Lean CoreProperties.
 *
 * Anything still hard for Stainless is documented in VERIFICATION.md as deferred
 * (same honesty as Verus MISSING notes), not claimed silently.
 */
object Lemmas {

  def lemmaRemoveLastMatchingNil(v: Version): Boolean = {
    removeLastMatchingSpec(Nil[Version](), v) == Nil[Version]()
  }.holds

  def lemmaRemoveLastMatchingSingleton(v: Version): Boolean = {
    removeLastMatchingSpec(Cons(v, Nil[Version]()), v) == Nil[Version]()
  }.holds

  def roundtripUpDown(v: Version, up: Codes, down: Codes): State = {
    require(!bodyIsEmpty(up))
    require(!bodyIsEmpty(down))
    val state0 = State(Nil[Version]())
    val mid = step(state0, ApplyUp(v, up))
    check(mid.isRight)
    val state1 = mid match {
      case Right(s) => s
      case Left(_) => State(Nil[Version]())
    }
    check(state1.applied == Cons(v, Nil[Version]()))
    check(removeLastMatchingSpec(state1.applied, v) == Nil[Version]())
    val end = step(state1, ApplyDown(v, down))
    check(end.isRight)
    end match {
      case Right(s) => s
      case Left(_) => State(Nil[Version]())
    }
  }.ensuring(res => res.applied == Nil[Version]())

  def runOneApplyUpAppends(state: State, v: Version, up: Codes): Either[StepError, State] = {
    require(!bodyIsEmpty(up))
    step(state, ApplyUp(v, up))
  }.ensuring(res =>
    res match {
      case Right(s) => s.applied == (state.applied :+ v)
      case _ => false
    }
  )

  def allApplied(files: List[MigrationSpec], applied: List[Version]): Boolean = {
    decreases(files)
    files match {
      case Nil() => true
      case Cons(f, rest) => versionIn(applied, f.version) && allApplied(rest, applied)
    }
  }

  @induct
  def pendingEmptyWhenAllApplied(
    files: List[MigrationSpec],
    applied: List[Version]
  ): Boolean = {
    require(allApplied(files, applied))
    pendingSpecs(files, applied) == Nil[MigrationSpec]()
  }.holds

  def migrateIdempotentWhenFullyApplied(
    files: List[MigrationSpec],
    applied: List[Version]
  ): Boolean = {
    require(allApplied(files, applied))
    check(pendingEmptyWhenAllApplied(files, applied))
    planMigrate(files, applied, false) match {
      case Right(p) => p == Nil[Op]()
      case _ => false
    }
  }.holds

  def upsNonEmpty(files: List[MigrationSpec]): Boolean = {
    decreases(files)
    files match {
      case Nil() => true
      case Cons(f, rest) => !bodyIsEmpty(f.up) && upsNonEmpty(rest)
    }
  }

  @induct
  def planUpsPreservesLength(pending: List[MigrationSpec]): Boolean = {
    require(upsNonEmpty(pending))
    planUpsFromPending(pending) match {
      case Right(p) => p.size == pending.size
      case Left(_) => false
    }
  }.holds

  def runNil(state: State): Boolean = {
    run(state, Nil[Op]()) match {
      case Right(s) => s == state
      case _ => false
    }
  }.holds

  /** Rollback of empty applied is empty (∀ files) — mirrors Verus plan_rollback ensures. */
  def rollbackEmptyApplied(files: List[MigrationSpec]): Boolean = {
    planRollback(files, Nil[Version]()) match {
      case Right(p) => p == Nil[Op]()
      case _ => false
    }
  }.holds

  /** Snoc membership: `v` is in `xs :+ v`. */
  @induct
  def versionInSnoc(xs: List[Version], v: Version): Boolean = {
    versionIn(xs :+ v, v)
  }.holds

  /**
   * Ledger-consistency helper: after a successful ApplyUp, version is in applied.
   * (Abstract State; TypeDB effect axioms are trusted outside this module.)
   */
  def applyUpRecordsVersion(state: State, v: Version, up: Codes): Boolean = {
    require(!bodyIsEmpty(up))
    check(versionInSnoc(state.applied, v))
    step(state, ApplyUp(v, up)) match {
      case Right(s) => versionIn(s.applied, v)
      case _ => false
    }
  }.holds
}
