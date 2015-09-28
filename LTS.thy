theory LTS

imports Main

begin

section {* Labeled transition systems and their executions *}

subsection {* Labeled transition systems *}

text {* 
  The semantics of a B component is a discrete, eventful, state-transition systems. We 
  start by defining labeled transition systems and their behaviors, independently of B.
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
  The inductively defined set @{term "states m"} corresponds to the set of
  reachable states of a given LTS @{text m}. 
*}

inductive_set states :: "('st, 'ev) LTS \<Rightarrow> 'st set" 
  for l :: "('st, 'ev) LTS" where
  base[elim!]: "s \<in> init l \<Longrightarrow> s \<in> states l"
| step[elim!]: "\<lbrakk> t \<in> trans l; src t \<in> states l \<rbrakk> \<Longrightarrow> dst t \<in> states l"

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
  "successors l S \<equiv> { dst t | t . t \<in> trans l \<and> src t \<in> S }"

text {* Next, we show that the successors of the reachable states are also reachable. *}

lemma reachable_stable: "successors l (states l) \<subseteq> states l"
  unfolding successors_def by auto
  
text {* 
  The following lemma is at the basis of proofs of invariants, and more
  generally, safety properties. Any set @{text S} that contains all initial
  states and is closed under successors contains all reachable states.
*}

lemma reachable_induct_set:
  assumes base: "init l \<subseteq> S"
  and step: "successors l S \<subseteq> S"
  and s: "s \<in> states l"
  shows "s \<in> S"
  using s base step by (induct s) (auto simp: successors_def)

text {*
  The following lemma is similar but stated in terms of a predicate.
  It contains the principle for proving invariants.
*}
lemmas reachable_induct_predicate = states.induct
text {* @{thm reachable_induct_predicate} *}

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
| start: "\<lbrakk> t \<in> trans l; src t \<in> init l \<rbrakk> \<Longrightarrow> [t] \<in> runs l"
| step: "\<lbrakk> t \<in> trans l; ts \<in> runs l; ts \<noteq> []; src t = dst (last ts) \<rbrakk> \<Longrightarrow> ts @ [t] \<in> runs l"

inductive_cases empty_run : "[] \<in> runs l"
inductive_cases one_step_run : "[t] \<in> runs l"
inductive_cases multi_step_run : "ts @ [t] \<in> runs l"

text {* 
  The following lemma states that for any non-empty run @{text ts} of an LTS @{text l},
  the source state of the first transition is an initial state of @{text l}.
*}

lemma "ts \<in> runs l \<Longrightarrow> ts \<noteq> [] \<Longrightarrow> src (hd ts) \<in> init l"
  by (induct rule: runs.induct, auto)


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

