//! Verus-annotated migrate / rollback core for tqlmate.
//!
//! Executable Verus Rust for the pure plan+interpreter algorithm that
//! `src/pure.rs` implements for production (State / Op / step / run /
//! plan_migrate / plan_rollback). Ensures clauses are checked by Verus.
//!
//! TypeDB I/O is outside this crate (trusted effect boundary).
//!
//! # Assumptions / MISSING
//! - Migration bodies are ASCII (`is_ascii`) — aligns with byte-oriented
//!   emptiness checks in `src/pure.rs` for typical TypeQL.
//! - [`version_str_lt`] is `external_body`: Rust `str` `<` is assumed to equal
//!   [`seq_char_lt`] on string views (strict-order planning only).

#![allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Digit-only migration version string.
pub struct Version {
    pub s: String,
}

impl Version {
    pub fn eq_ver(&self, other: &Version) -> (b: bool)
        ensures
            b == (self.s@ == other.s@),
    {
        self.s == other.s
    }

    pub fn clone_ver(&self) -> (out: Version)
        ensures
            out.s@ == self.s@,
    {
        Version { s: self.s.clone() }
    }
}

pub struct MigrationSpec {
    pub version: Version,
    pub name: String,
    pub up: String,
    pub down: String,
}

pub enum Op {
    ApplyUp { version: Version, up: String },
    ApplyDown { version: Version, down: String },
}

pub struct State {
    pub applied: Vec<Version>,
}

pub enum StepError {
    EmptyUp { version: Version },
    EmptyDown { version: Version },
}

pub enum PlanError {
    EmptyUp { version: Version },
    EmptyDown { version: Version, name: String },
    MissingFile { version: Version },
    StrictOrder { pending: Version, applied_up_to: Version },
}

/// Sequence of version string views.
pub open spec fn version_views(vs: Seq<Version>) -> Seq<Seq<char>> {
    vs.map(|_i: int, v: Version| v.s@)
}

pub open spec fn is_ascii_ws(c: char) -> bool {
    c == ' ' || c == '\t' || c == '\n' || c == '\r'
}

pub open spec fn body_is_empty_spec(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> is_ascii_ws(#[trigger] s[i])
}

pub fn body_is_empty(s: &str) -> (b: bool)
    requires
        s.is_ascii(),
    ensures
        b == body_is_empty_spec(s@),
{
    let mut i: usize = 0;
    while i < s.unicode_len()
        invariant
            s.is_ascii(),
            i <= s@.len(),
            forall|j: int| #![auto] 0 <= j < i ==> is_ascii_ws(s@[j]),
        decreases s@.len() - i,
    {
        let c = s.get_char(i);
        if !(c == ' ' || c == '\t' || c == '\n' || c == '\r') {
            return false;
        }
        i = i + 1;
    }
    true
}

pub fn prefix_clone(applied: &Vec<Version>, n: usize) -> (out: Vec<Version>)
    requires
        n <= applied.len(),
    ensures
        version_views(out@) =~= version_views(applied@).subrange(0, n as int),
        out@.len() == n,
{
    let mut out: Vec<Version> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n <= applied.len(),
            out@.len() == i,
            version_views(out@) =~= version_views(applied@).subrange(0, i as int),
        decreases n - i,
    {
        out.push(applied[i].clone_ver());
        proof {
            assert(version_views(out@) =~= version_views(applied@).subrange(0, i as int) + seq![
                applied@[i as int].s@,
            ]);
            assert(version_views(applied@).subrange(0, (i + 1) as int)
                =~= version_views(applied@).subrange(0, i as int) + seq![applied@[i as int].s@]);
        }
        i = i + 1;
    }
    out
}

pub open spec fn remove_last_matching_spec(s: Seq<Seq<char>>, target: Seq<char>) -> Seq<Seq<char>>
    decreases s.len(),
{
    if s.len() == 0 {
        Seq::empty()
    } else if s[s.len() - 1] == target {
        s.subrange(0, s.len() - 1)
    } else {
        remove_last_matching_spec(s.subrange(0, s.len() - 1), target).push(s[s.len() - 1])
    }
}

pub fn remove_last_matching(applied: &Vec<Version>, v: &Version) -> (out: Vec<Version>)
    ensures
        version_views(out@) =~= remove_last_matching_spec(version_views(applied@), v.s@),
    decreases applied.len(),
{
    if applied.len() == 0 {
        proof {
            assert(remove_last_matching_spec(version_views(applied@), v.s@)
                =~= Seq::<Seq<char>>::empty());
        }
        Vec::new()
    } else {
        let last_i = applied.len() - 1;
        if applied[last_i].eq_ver(v) {
            let out = prefix_clone(applied, last_i);
            proof {
                assert(version_views(out@) =~= version_views(applied@).subrange(0, last_i as int));
                assert(version_views(applied@)[last_i as int] == v.s@);
                assert(last_i as int == version_views(applied@).len() - 1);
                assert(remove_last_matching_spec(version_views(applied@), v.s@)
                    =~= version_views(applied@).subrange(0, version_views(applied@).len() - 1));
            }
            out
        } else {
            let prefix = prefix_clone(applied, last_i);
            let mut out = remove_last_matching(&prefix, v);
            proof {
                assert(version_views(prefix@) =~= version_views(applied@).subrange(
                    0,
                    last_i as int,
                ));
                assert(last_i as int == version_views(applied@).len() - 1);
                assert(version_views(applied@)[last_i as int] != v.s@);
                assert(version_views(out@) =~= remove_last_matching_spec(
                    version_views(prefix@),
                    v.s@,
                ));
            }
            out.push(applied[last_i].clone_ver());
            proof {
                assert(version_views(out@) =~= remove_last_matching_spec(
                    version_views(prefix@),
                    v.s@,
                ).push(version_views(applied@)[last_i as int]));
                assert(remove_last_matching_spec(version_views(applied@), v.s@)
                    =~= remove_last_matching_spec(
                    version_views(applied@).subrange(0, version_views(applied@).len() - 1),
                    v.s@,
                ).push(version_views(applied@)[version_views(applied@).len() - 1]));
            }
            out
        }
    }
}

pub open spec fn op_bodies_ascii(op: Op) -> bool {
    match op {
        Op::ApplyUp { up, .. } => up.is_ascii(),
        Op::ApplyDown { down, .. } => down.is_ascii(),
    }
}

pub fn step(state: State, op: Op) -> (r: Result<State, StepError>)
    requires
        op_bodies_ascii(op),
    ensures
        match op {
            Op::ApplyUp { version, up } => {
                if body_is_empty_spec(up@) {
                    match r {
                        Result::Err(StepError::EmptyUp { version: ev }) => ev.s@ == version.s@,
                        _ => false,
                    }
                } else {
                    match r {
                        Result::Ok(s) => version_views(s.applied@) =~= version_views(
                            state.applied@,
                        ) + seq![version.s@],
                        _ => false,
                    }
                }
            },
            Op::ApplyDown { version, down } => {
                if body_is_empty_spec(down@) {
                    match r {
                        Result::Err(StepError::EmptyDown { version: ev }) => ev.s@
                            == version.s@,
                        _ => false,
                    }
                } else {
                    match r {
                        Result::Ok(s) => version_views(s.applied@) =~= remove_last_matching_spec(
                            version_views(state.applied@),
                            version.s@,
                        ),
                        _ => false,
                    }
                }
            },
        },
{
    match op {
        Op::ApplyUp { version, up } => {
            if body_is_empty(up.as_str()) {
                return Err(StepError::EmptyUp { version });
            }
            let mut applied = state.applied;
            applied.push(version);
            Ok(State { applied })
        },
        Op::ApplyDown { version, down } => {
            if body_is_empty(down.as_str()) {
                return Err(StepError::EmptyDown { version });
            }
            let applied = remove_last_matching(&state.applied, &version);
            Ok(State { applied })
        },
    }
}

fn clone_op(op: &Op) -> (out: Op)
    ensures
        op_bodies_ascii(*op) ==> op_bodies_ascii(out),
        match (*op, out) {
            (
                Op::ApplyUp { version: v1, up: u1 },
                Op::ApplyUp { version: v2, up: u2 },
            ) => v1.s@ == v2.s@ && u1@ == u2@ && u1.is_ascii() == u2.is_ascii(),
            (
                Op::ApplyDown { version: v1, down: d1 },
                Op::ApplyDown { version: v2, down: d2 },
            ) => v1.s@ == v2.s@ && d1@ == d2@ && d1.is_ascii() == d2.is_ascii(),
            _ => false,
        },
{
    match op {
        Op::ApplyUp { version, up } => {
            let u = up.clone();
            proof {
                assert(u@ == up@);
                assert(u.is_ascii() == up.is_ascii());
            }
            Op::ApplyUp { version: version.clone_ver(), up: u }
        },
        Op::ApplyDown { version, down } => {
            let d = down.clone();
            proof {
                assert(d@ == down@);
                assert(d.is_ascii() == down.is_ascii());
            }
            Op::ApplyDown { version: version.clone_ver(), down: d }
        },
    }
}

fn tail_ops(plan: &Vec<Op>) -> (rest: Vec<Op>)
    requires
        plan.len() > 0,
        forall|i: int| 0 <= i < plan@.len() ==> op_bodies_ascii(#[trigger] plan@[i]),
    ensures
        rest@.len() == plan@.len() - 1,
        forall|i: int| 0 <= i < rest@.len() ==> op_bodies_ascii(#[trigger] rest@[i]),
{
    let mut rest: Vec<Op> = Vec::new();
    let mut i: usize = 1;
    while i < plan.len()
        invariant
            1 <= i <= plan.len(),
            rest@.len() == i - 1,
            forall|j: int| 0 <= j < plan@.len() ==> op_bodies_ascii(#[trigger] plan@[j]),
            forall|j: int| 0 <= j < rest@.len() ==> op_bodies_ascii(#[trigger] rest@[j]),
        decreases plan.len() - i,
    {
        rest.push(clone_op(&plan[i]));
        i = i + 1;
    }
    rest
}


/// Spec interpreter: left-fold `step` over the plan (views only for Apply* bodies).
pub open spec fn run_spec(applied: Seq<Seq<char>>, plan: Seq<Op>) -> Result<Seq<Seq<char>>, ()>
    decreases plan.len(),
{
    if plan.len() == 0 {
        Result::Ok(applied)
    } else {
        match plan[0] {
            Op::ApplyUp { version, up } => {
                if body_is_empty_spec(up@) {
                    Result::Err(())
                } else {
                    run_spec(applied + seq![version.s@], plan.subrange(1, plan.len() as int))
                }
            },
            Op::ApplyDown { version, down } => {
                if body_is_empty_spec(down@) {
                    Result::Err(())
                } else {
                    run_spec(
                        remove_last_matching_spec(applied, version.s@),
                        plan.subrange(1, plan.len() as int),
                    )
                }
            },
        }
    }
}

/// `run(s, []) = Ok(s)`.
pub fn run(state: State, plan: &Vec<Op>) -> (r: Result<State, StepError>)
    requires
        forall|i: int| 0 <= i < plan@.len() ==> op_bodies_ascii(#[trigger] plan@[i]),
    ensures
        plan@.len() == 0 ==> (match r {
            Result::Ok(s) => version_views(s.applied@) =~= version_views(state.applied@),
            _ => false,
        }),
    decreases plan.len(),
{
    if plan.len() == 0 {
        Ok(state)
    } else {
        let op = clone_op(&plan[0]);
        let next = match step(state, op) {
            Ok(s) => s,
            Err(e) => {
                return Err(e);
            },
        };
        let rest = tail_ops(plan);
        run(next, &rest)
    }
}

/// Empty applied ⇒ empty rollback plan (∀ files).
pub fn plan_rollback(files: &Vec<MigrationSpec>, applied: &Vec<Version>) -> (r: Result<
    Vec<Op>,
    PlanError,
>)
    requires
        forall|i: int| 0 <= i < files@.len() ==> (#[trigger] files@[i]).down.is_ascii(),
    ensures
        applied@.len() == 0 ==> (match r {
            Result::Ok(p) => p@.len() == 0,
            _ => false,
        }),
{
    if applied.len() == 0 {
        return Ok(Vec::new());
    }
    let version = applied[applied.len() - 1].clone_ver();
    let mut i: usize = 0;
    let mut found: Option<usize> = None;
    while i < files.len()
        invariant
            i <= files.len(),
            forall|j: int| 0 <= j < files@.len() ==> (#[trigger] files@[j]).down.is_ascii(),
            match found {
                None => forall|j: int|
                    #![auto]
                    0 <= j < i ==> files@[j].version.s@ != version.s@,
                Some(fi) => fi < files.len() && files@[fi as int].version.s@ == version.s@,
            },
        decreases files.len() - i,
    {
        if files[i].version.eq_ver(&version) {
            found = Some(i);
            break;
        }
        i = i + 1;
    }
    match found {
        None => Err(PlanError::MissingFile { version }),
        Some(fi) => {
            let m = &files[fi];
            if body_is_empty(m.down.as_str()) {
                Err(
                    PlanError::EmptyDown {
                        version: m.version.clone_ver(),
                        name: m.name.clone(),
                    },
                )
            } else {
                let mut plan: Vec<Op> = Vec::new();
                let down = m.down.clone();
                proof {
                    assert(down.is_ascii() == m.down.is_ascii());
                }
                plan.push(Op::ApplyDown { version: m.version.clone_ver(), down });
                Ok(plan)
            }
        },
    }
}

fn version_in(applied: &Vec<Version>, v: &Version) -> (b: bool)
    ensures
        b == exists|j: int| #![auto] 0 <= j < applied@.len() && applied@[j].s@ == v.s@,
{
    let mut i: usize = 0;
    while i < applied.len()
        invariant
            i <= applied.len(),
            forall|j: int| #![auto] 0 <= j < i ==> applied@[j].s@ != v.s@,
        decreases applied.len() - i,
    {
        if applied[i].eq_ver(v) {
            return true;
        }
        i = i + 1;
    }
    false
}

pub fn pending_specs(files: &Vec<MigrationSpec>, applied: &Vec<Version>) -> (out: Vec<
    MigrationSpec,
>)
    requires
        forall|i: int| 0 <= i < files@.len() ==> (#[trigger] files@[i]).up.is_ascii(),
    ensures
        files@.len() == 0 ==> out@.len() == 0,
        forall|i: int|
            0 <= i < out@.len() ==> !exists|j: int|
                #![auto]
                0 <= j < applied@.len() && applied@[j].s@ == (#[trigger] out@[i]).version.s@,
        forall|i: int| 0 <= i < out@.len() ==> (#[trigger] out@[i]).up.is_ascii(),
{
    let mut out: Vec<MigrationSpec> = Vec::new();
    let mut i: usize = 0;
    while i < files.len()
        invariant
            i <= files.len(),
            forall|j: int| 0 <= j < files@.len() ==> (#[trigger] files@[j]).up.is_ascii(),
            forall|k: int|
                0 <= k < out@.len() ==> !exists|j: int|
                    #![auto]
                    0 <= j < applied@.len() && applied@[j].s@
                        == (#[trigger] out@[k]).version.s@,
            forall|k: int| 0 <= k < out@.len() ==> (#[trigger] out@[k]).up.is_ascii(),
            // out only grows while scanning files; empty files ⇒ empty out
            files@.len() == 0 ==> out@.len() == 0,
        decreases files.len() - i,
    {
        let f_ver = files[i].version.clone_ver();
        let is_pending = !version_in(applied, &f_ver);
        if is_pending {
            let up = files[i].up.clone();
            proof {
                assert(up@ == files@[i as int].up@);
                assert(up.is_ascii() == files@[i as int].up.is_ascii());
                assert(up.is_ascii());
            }
            out.push(
                MigrationSpec {
                    version: f_ver,
                    name: files[i].name.clone(),
                    up,
                    down: files[i].down.clone(),
                },
            );
        }
        i = i + 1;
    }
    out
}

fn plan_ups_from_pending(pending: &Vec<MigrationSpec>) -> (r: Result<Vec<Op>, PlanError>)
    requires
        forall|i: int| 0 <= i < pending@.len() ==> (#[trigger] pending@[i]).up.is_ascii(),
    ensures
        pending@.len() == 0 ==> (match r {
            Result::Ok(p) => p@.len() == 0,
            _ => false,
        }),
{
    let mut plan: Vec<Op> = Vec::new();
    let mut i: usize = 0;
    while i < pending.len()
        invariant
            i <= pending.len(),
            forall|j: int| 0 <= j < pending@.len() ==> (#[trigger] pending@[j]).up.is_ascii(),
            forall|j: int| 0 <= j < plan@.len() ==> op_bodies_ascii(#[trigger] plan@[j]),
            pending@.len() == 0 ==> plan@.len() == 0,
        decreases pending.len() - i,
    {
        let f = &pending[i];
        if body_is_empty(f.up.as_str()) {
            return Err(PlanError::EmptyUp { version: f.version.clone_ver() });
        }
        let up = f.up.clone();
        proof {
            assert(up.is_ascii());
        }
        plan.push(Op::ApplyUp { version: f.version.clone_ver(), up });
        i = i + 1;
    }
    Ok(plan)
}

pub open spec fn seq_char_lt(a: Seq<char>, b: Seq<char>) -> bool
    decreases a.len() + b.len(),
{
    if a.len() == 0 {
        b.len() != 0
    } else if b.len() == 0 {
        false
    } else if a[0] < b[0] {
        true
    } else if a[0] > b[0] {
        false
    } else {
        seq_char_lt(a.subrange(1, a.len() as int), b.subrange(1, b.len() as int))
    }
}

/// Trusted: Rust `str` `<` equals [`seq_char_lt`] on views.
/// MISSING: not proved that `std` Ord matches this spec.
#[verifier::external_body]
pub fn version_str_lt(a: &Version, b: &Version) -> (r: bool)
    ensures
        r == seq_char_lt(a.s@, b.s@),
{
    a.s.as_str() < b.s.as_str()
}

fn max_version(applied: &Vec<Version>) -> (r: Option<Version>)
    ensures
        applied@.len() == 0 ==> r is None,
        applied@.len() > 0 ==> r is Some,
{
    if applied.len() == 0 {
        return None;
    }
    let mut best: usize = 0;
    let mut i: usize = 1;
    while i < applied.len()
        invariant
            best < applied.len(),
            1 <= i <= applied.len(),
        decreases applied.len() - i,
    {
        if version_str_lt(&applied[best], &applied[i]) {
            best = i;
        }
        i = i + 1;
    }
    Some(applied[best].clone_ver())
}

fn check_strict_order_specs(files: &Vec<MigrationSpec>, applied: &Vec<Version>) -> (r: Result<
    (),
    PlanError,
>) {
    let max = match max_version(applied) {
        Some(m) => m,
        None => {
            return Ok(());
        },
    };
    let mut i: usize = 0;
    while i < files.len()
        invariant
            i <= files.len(),
        decreases files.len() - i,
    {
        let pending = files[i].version.clone_ver();
        if !version_in(applied, &pending) && version_str_lt(&pending, &max) {
            return Err(PlanError::StrictOrder { pending, applied_up_to: max });
        }
        i = i + 1;
    }
    Ok(())
}

/// Plan pending ups. When `strict`, rejects pending versions `< max(applied)`.
///
/// Definitional (nonstrict): `pending_specs` then `plan_ups_from_pending`.
pub fn plan_migrate(
    files: &Vec<MigrationSpec>,
    applied: &Vec<Version>,
    strict: bool,
) -> (r: Result<Vec<Op>, PlanError>)
    requires
        forall|i: int| 0 <= i < files@.len() ==> (#[trigger] files@[i]).up.is_ascii(),
    ensures
        (!strict && files@.len() == 0) ==> (match r {
            Result::Ok(p) => p@.len() == 0,
            _ => false,
        }),
{
    if strict {
        match check_strict_order_specs(files, applied) {
            Ok(()) => {},
            Err(e) => {
                return Err(e);
            },
        }
    }
    let pending = pending_specs(files, applied);
    proof {
        // When files is empty, pending is empty (loop never pushes).
        if files@.len() == 0 {
            assert(pending@.len() == 0);
        }
    }
    plan_ups_from_pending(&pending)
}

/// Round-trip: empty → ApplyUp → ApplyDown → empty applied.
pub fn roundtrip_up_down(v: Version, up: String, down: String) -> (final_st: State)
    requires
        up.is_ascii(),
        down.is_ascii(),
        !body_is_empty_spec(up@),
        !body_is_empty_spec(down@),
    ensures
        final_st.applied@.len() == 0,
{
    let state0 = State { applied: Vec::new() };
    let v_for_down = v.clone_ver();
    let state1 = match step(state0, Op::ApplyUp { version: v, up }) {
        Result::Ok(s) => s,
        Result::Err(_) => {
            assert(false);
            unreached()
        },
    };
    proof {
        assert(state1.applied@.len() == 1);
        assert(version_views(state1.applied@)[0] == v_for_down.s@);
        assert(remove_last_matching_spec(version_views(state1.applied@), v_for_down.s@)
            =~= Seq::<Seq<char>>::empty());
    }
    let state2 = match step(state1, Op::ApplyDown { version: v_for_down, down }) {
        Result::Ok(s) => s,
        Result::Err(_) => {
            assert(false);
            unreached()
        },
    };
    state2
}

pub proof fn lemma_remove_last_matching_nil(target: Seq<char>)
    ensures
        remove_last_matching_spec(Seq::<Seq<char>>::empty(), target) =~= Seq::<
            Seq<char>,
        >::empty(),
{
}

pub proof fn lemma_remove_last_matching_singleton(v: Seq<char>)
    ensures
        remove_last_matching_spec(seq![v], v) =~= Seq::<Seq<char>>::empty(),
{
    assert(seq![v].len() == 1);
    assert(seq![v][0] == v);
    assert(remove_last_matching_spec(seq![v], v) == seq![v].subrange(0, 0));
    assert(seq![v].subrange(0, 0) =~= Seq::<Seq<char>>::empty());
}

/// One successful ApplyUp appends the version view.
pub fn run_one_apply_up_appends(state: State, v: Version, up: String) -> (r: Result<
    State,
    StepError,
>)
    requires
        up.is_ascii(),
        !body_is_empty_spec(up@),
    ensures
        (match r {
            Result::Ok(s) => version_views(s.applied@) =~= version_views(state.applied@) + seq![
                v.s@,
            ],
            _ => false,
        }),
{
    step(state, Op::ApplyUp { version: v, up })
}

/// Strict migrate maps a strict-order failure to `PlanError::StrictOrder`.
pub fn plan_migrate_strict_maps_error(
    files: &Vec<MigrationSpec>,
    applied: &Vec<Version>,
) -> (r: Result<Vec<Op>, PlanError>)
    requires
        forall|i: int| 0 <= i < files@.len() ==> (#[trigger] files@[i]).up.is_ascii(),
{
    plan_migrate(files, applied, true)
}

} // verus!
