theory LTS

imports Main

begin

section {* Labeled transition systems and their executions *}

subsection {* Labeled transition systems *}

text {* 
  The semantics of a B component is a discrete, eventful, state-transition system. We 
  formalize labeled transition systems (LTS) and their behaviors, independently of B.
  An LTS is given by a set of initial states and a set of transitions, which are
  triples (source and destination state, and a transition label). The following
  definitions of transitions and transition systems are parameterized by types
  @{text "'st"} and @{text "'ev"} of states and events.
*}

record ('st, 'ev) Tr =
  src :: 'st     -- "source state"
  dst :: 'st     -- "destination state"
  lbl :: 'ev     -- "labeling event"

record ('st, 'ev) LTS =
  init :: "'st set" -- "set of initial states"
  trans :: "('st, 'ev) Tr set" -- "set of transitions"

text {*
   We first introduce auxiliary definitions for some useful
   concepts. The function @{text "outgoing"}, given a LTS and a
   state, returns the set of outgoing transitions in that state.  
*}

definition
  outgoing :: "('st, 'ev) LTS \<Rightarrow> 'st \<Rightarrow> ('st, 'ev) Tr set"
where
  "outgoing l \<equiv> \<lambda>s. { t | t . t \<in> trans l \<and> src t = s}"

text {*
  The function @{text "accepted_events"}, given an LTS and a state,
  returns the set of events that label the outgoing transitions in
  that state. It corresponds to the operations and the corresponding
  parameter valuations that are applicable in that state.  
*}

definition
  accepted_events :: "('st, 'ev) LTS \<Rightarrow> 'st \<Rightarrow> 'ev set"
where
  "accepted_events l s \<equiv> lbl ` (outgoing l s)"

text {* 
  The inductively defined set @{term "states m"} corresponds to the set of
  reachable states of a given LTS @{text m}. 
*}

inductive_set states :: "('st, 'ev) LTS \<Rightarrow> 'st set" 
  for l :: "('st, 'ev) LTS" where
  base[elim!]: "s \<in> init l \<Longrightarrow> s \<in> states l"
| step[elim!]: "\<lbrakk>s \<in> states l; t \<in> outgoing l s\<rbrakk> \<Longrightarrow> dst t \<in> states l"

inductive_cases base : "s \<in> states l"
inductive_cases step : "dst t \<in> states l"

text {* 
  A few lemmas related to reachable states are then enunciated and proved. 
  First, all the initial states are reachable states:
*}

lemma reachable_init: "init l \<subseteq> states l"
  by auto

text {* Next, the successors states of the reachable states are themselves reachable states.
We first define a function @{text "successors"} that returns the set of successors of a
given set @{text "S"} of states in a given LTS @{text "l"}: *}

definition successors :: "('st, 'ev) LTS \<Rightarrow> 'st set \<Rightarrow> 'st set" where
  "successors l S \<equiv> dst ` (UNION S (outgoing l))"

text {* Next, we show that the successors of the reachable states are also reachable. *}

lemma reachable_stable: "successors l (states l) \<subseteq> states l"
  unfolding successors_def by auto

text {* 
  The following lemma is at the basis of proofs of invariants, and more
  generally, safety properties. Any set @{text S} that contains all initial
  states and is closed under successors contains all reachable states.
*}

lemma reachable_induct_set:
  assumes s: "s \<in> states l"
  and "init l \<subseteq> S"
  and "successors l S \<subseteq> S"
  shows "s \<in> S"
  using assms by (induct s) (auto simp: successors_def)

text {*
  The following lemma is similar but stated in terms of a predicate.
  It contains the principle for proving invariants.
*}
lemmas reachable_induct_predicate = states.induct
text {* @{thm reachable_induct_predicate} *}

text {*
  The \emph{alphabet} of an LTS is defined as the set of labels
  appearing at some reachable state.
*}

definition alphabet where
  "alphabet l \<equiv> UNION (states l) (accepted_events l)"


subsection {* Behavior *}

text {* 
  Two views of (finitary) behavior are formalized. The first view is
  the internal behavior: a \emph{run} is a sequence of transitions such
  that for any two consecutive transitions, the source state of the
  second one is the destination state of the first one.

  The second, external view of behavior, projects transitions to their
  labels: only the name of the event is recorded whereas states are
  abstracted from.
*}

subsubsection {* Internal behaviour *}

type_synonym ('st, 'ev) Run = "('st, 'ev) Tr list"

text {* 
  The inductive set @{text "runs l"} denotes the set of finite executions
  of the LTS @{text "l"}, viewed as lists of transitions. There are two base 
  cases, corresponding to the empty execution and to executions with a 
  single transition whose source state is an initial state.
*}

inductive_set runs :: "('st, 'ev) LTS \<Rightarrow> ('st, 'ev) Run set"  
  for l :: "('st, 'ev) LTS" where
  base: "[] \<in> runs l"
| start: "\<lbrakk> s \<in> init l; t \<in> outgoing l s \<rbrakk> \<Longrightarrow> [t] \<in> runs l"
| step: "\<lbrakk> ts \<in> runs l; ts \<noteq> []; t \<in> outgoing l (dst (last ts)) \<rbrakk> \<Longrightarrow> ts @ [t] \<in> runs l"

inductive_cases empty_run : "[] \<in> runs l"
inductive_cases one_step_run : "[t] \<in> runs l"
inductive_cases multi_step_run : "ts @ [t] \<in> runs l"

text {* 
  The following lemma states that for any non-empty run @{text ts} of an LTS @{text l},
  the source state of the first transition is an initial state of @{text l}.
*}

lemma run_starts_initial: "ts \<in> runs l \<Longrightarrow> ts \<noteq> [] \<Longrightarrow> src (hd ts) \<in> init l"
  by (induct rule: runs.induct, auto simp: outgoing_def)

text {*
  The set of runs is closed under prefixes.
*}
lemma prefix_is_run:
  assumes "ts \<in> runs l"
  shows "take n ts \<in> runs l"
using assms proof (induct rule: runs.induct)
  show "take n [] \<in> runs l" by (auto intro: runs.base)
next
  fix s t
  assume s: "s \<in> init l" and t: "t \<in> outgoing l s"
  show "take n [t] \<in> runs l"
  proof (cases n)
    assume "n = 0"
    thus ?thesis by (auto intro: runs.base)
  next
    fix m
    assume "n = Suc m"
    hence "take n [t] = [t]" by simp
    with s t show ?thesis by (auto intro: runs.start)
  qed
next
  fix ts t
  assume ts: "ts \<in> runs l" "ts \<noteq> []"
     and t: "t \<in> outgoing l (dst (last ts))"
     and ih: "take n ts \<in> runs l"
  show "take n (ts @ [t]) \<in> runs l"
  proof (cases "n \<le> length ts")
    case True
    hence "take n (ts @ [t]) = take n ts" by auto
    with ih show ?thesis by simp
  next
    case False
    hence "take n (ts @ [t]) = ts @ [t]" by auto
    with ts t show ?thesis by (auto elim: runs.step)
  qed
qed


subsubsection {* External behavior. *}

text {* 
  The external, or observable, behavior of a LTS is obtained by
  projecting the internal behavior to the events labeling its 
  transitions. We call this a \emph{trace} of the LTS.
*}

type_synonym 'ev Trace = "'ev list"

definition traces :: "('st, 'ev) LTS \<Rightarrow> 'ev Trace set" where
  "traces l \<equiv> (map lbl) ` (runs l)"

end

