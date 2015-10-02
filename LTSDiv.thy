theory LTSDiv

imports Main

begin

section {* Labeled transition systems with divergences and their executions *}

subsection {* Labeled transition systems with divergences*}

text {* 
  A labeled-transition system with divergences is a LTS augmented with a set of
  divergences. A divergence is a pair formed by a state and an event and formalizes
  situations where the LTS is not able to handle a given event.
*}

record ('st, 'ev) Tr =
  src :: 'st     -- "source state"
  dst :: 'st     -- "destination state"
  lbl :: 'ev     -- "labeling event"

record ('st, 'ev) LTSDiv =
  init :: "'st set" -- "set of initial states"
  trans :: "('st, 'ev) Tr set" -- "set of transitions"
  divergences :: "('st * 'ev) set" -- "set of divergences"

text {* 
  The set of transitions @{term "div_trans l"} corresponds to transitions
  that provoke a divergence.
*}

definition div_trans :: "('st, 'ev) LTSDiv \<Rightarrow> ('st, 'ev) Tr set" where
  "div_trans l \<equiv> { t | t . t \<in> trans l \<and> (src t, lbl t) \<in> divergences l }"

text {* 
  The set @{term "div_state l s"} are the events that cause divergence
  in state @{term "s"} of @{term "l"}.
*}

definition div_state :: "('st, 'ev) LTSDiv \<Rightarrow> 'st \<Rightarrow> 'ev set" where
  "div_state l st \<equiv> { e | e . (st, e) \<notin> divergences l }"

text {* 
  The function @{term "div_states"} lifts the previous definition to sets
  of states.
*}

(* dd : is there a more concise way to express this? *)

definition div_states :: "('st, 'ev) LTSDiv \<Rightarrow> 'st set \<Rightarrow> 'ev set" where
  "div_states l s \<equiv> { e | e st . st \<in> s \<and> e \<in> div_state l st }"

text {* 
  The inductively defined set @{term "states l"} corresponds to the set of
  reachable states of a given LTS with divergences @{text l}. A transition
  only happens for events that do not cause divergence.
*}

inductive_set states :: "('st, 'ev) LTSDiv \<Rightarrow> 'st set" 
  for l :: "('st, 'ev) LTSDiv" where
  base[elim!]: "s \<in> init l \<Longrightarrow> s \<in> states l"
| step[elim!]: "\<lbrakk> t \<in> trans l; t \<notin> div_trans l; src t \<in> states l \<rbrakk> \<Longrightarrow> dst t \<in> states l"

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
given set @{text "S"} of states in a given LTS with divergences @{text "l"}: *}

definition successors :: "('st, 'ev) LTSDiv \<Rightarrow> 'st set \<Rightarrow> 'st set" where
  "successors l S \<equiv> { dst t | t . t \<in> trans l \<and> t \<notin> div_trans l \<and> src t \<in> S }"

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

inductive_set runs :: "('st, 'ev) LTSDiv \<Rightarrow> ('st, 'ev) Run set"  
  for l :: "('st, 'ev) LTSDiv" where
  base: "[] \<in> runs l"
| start: "\<lbrakk> t \<notin> div_trans l; src t \<in> init l \<rbrakk> \<Longrightarrow> [t] \<in> runs l"
| step: "\<lbrakk> t \<notin> div_trans l; ts \<in> runs l; ts \<noteq> []; src t = dst (last ts) \<rbrakk>
         \<Longrightarrow> ts @ [t] \<in> runs l"

inductive_cases empty_run : "[] \<in> runs l"
inductive_cases one_step_run : "[t] \<in> runs l"
inductive_cases multi_step_run : "ts @ [t] \<in> runs l"

text {* 
  The following lemma states that for any non-empty run @{text ts} of an LTS @{text l},
  the source state of the first transition is an initial state of @{text l}.
*}

lemma "ts \<in> runs l \<Longrightarrow> ts \<noteq> [] \<Longrightarrow> src (hd ts) \<in> init l"
  by (induct rule: runs.induct, auto)

text {*
  The function @{text div_run} provides the set of events that cause a divergence
  of a LTS @{text "l"} after it has executed run @{text "r"}.
*}

definition div_run :: "('st, 'ev) LTSDiv \<Rightarrow> ('st, 'ev) Run \<Rightarrow> 'ev set" where 
"div_run l r \<equiv> 
   if r = [] then div_states l (init l)
   else div_state l (dst (last r))"

subsubsection {* External behavior. *}

text {* 
  The external, or observable, behavior of a LTS is an expression of the
  events to which the LTS responds. It is a set of \emph{trace-divergences}
  observations. Each such observation is a trace of events leading the LTS
  to some internal state, and a set of events that provoke divergences in
  that state.
*}

text {*
  The type corresponding to such observations is named @{text TraceDiv} and is
  defined as follows:
*}
type_synonym 'ev TraceDiv = "'ev list * 'ev set"

text {*
  Next, the function @{text trace_div_run} maps observations of internal behavior to 
  observations of external behavior.
*}

definition trace_div_run :: "('st, 'ev) LTSDiv \<Rightarrow> ('st, 'ev) Run \<Rightarrow> 'ev TraceDiv" where 
"trace_div_run l r \<equiv> 
   if r = [] then ([], div_states l (init l))
   else (map lbl r, div_state l (dst (last r)))"

text {*
  Equipped with this function, we define the observable trace-divergence semantics
  of the LTS as function @{text trace_div}.
*}
definition trace_div :: "('st, 'ev) LTSDiv \<Rightarrow> 'ev TraceDiv set" where
  "trace_div l \<equiv> trace_div_run l ` (runs l)"

end

