theory LTS

imports Main

begin

section {* Execution models *}

subsection {* Labeled transition systems *}

text {* The semantics of a B component is a discrete, eventful, state-transition systems. We 
first define what is meant exactly by such systems. Any system is, at a given time in a state. 
Conversely, a system has a set of possible states. A system evolves from state to state,
and such changes called transitions. The following record definition of 
@{text "('st, 'ev) Tr}"} models transitions, where the parametric sorts @{text "'st"} 
and @{text "'ev"} represent states and events, respectively. *}

record ('st, 'ev) Tr =
  src :: 'st -- "source state"
  dst :: 'st -- "destination state"
  lbl :: 'ev -- "labeling event"

text {* Building on this formalization of transitions, the record @{text "('st, 'ev) LTS"} 
formalizes labeled transition systems (LTS):  *}

record ('st, 'ev) LTS =
  init :: "'st set" -- "set of initial states"
  trans :: "('st, 'ev) Tr set" -- "set of transitions"

text {* The inductively defined set @{term "states"} yields the reachable states of a 
given LTS. *}

inductive_set states :: "('st, 'ev) LTS \<Rightarrow> 'st set" for m :: "('st, 'ev) LTS" where
  base[elim!]: "s \<in> init m \<Longrightarrow> s \<in> states m"
| step[elim!]: "\<lbrakk> t \<in> trans m; src t \<in> states m \<rbrakk> \<Longrightarrow> dst t \<in> states m"
  
text {* A few lemmas related to reachable states are then enunciated and proved. 
First, all the initial states are reachable states:*}

lemma reachable_init: "init m \<subseteq> states m" 
  by auto

text {* Next, the successors states of the reachable states are themselves reachable states.
We first define a function @{text "successors"} that returns the set of successors of a
given set @{text "S"} of states in a given LTS @{text "L"}: *}

definition successors :: "('st, 'ev) LTS \<Rightarrow> 'st set \<Rightarrow> 'st set" where
  "successors m S \<equiv> { dst t | t . t \<in> trans m \<and> src t \<in> S }"

text {* Next, we show that the successors of the reachable states are also reachable. *}

lemma reachable_stable: "successors m (states m) \<subseteq> states m"
  unfolding successors_def by auto
  
text {* The following lemma is related to the identification of sufficient conditions to establish 
safety properties. Consider a property that is satisfied by some set of states $S$. If the initial 
states are in $S$, and if the successors of $S$ are in $S$ then all the reachable states are in 
$S$. *}

lemma reachable_induct_set:
  assumes s: "s \<in> states m" and base: "init m \<subseteq> S" and step: "successors m S \<subseteq> S"
  shows "s \<in> S"
using s proof (induct s)
  fix i
  assume "i \<in> init m"
  with base show "i \<in> S" ..
next
  fix t
  assume "t \<in> trans m" and "src t \<in> S"
  with step show "dst t \<in> S" unfolding successors_def by auto
qed

text {* Next we enunciate and prove a similar lemma for predicates. In a LTS @{text "m"}, 
if every initial state
statisfies some predicate @{text "P"} and, for each transition, whenever the source state
satisfies @{text "P"}, the destination state also satisfies @{text "P"}, then all the
reachable states satisfy @{text "P"} (and this is an invariant of the LTS). *}
lemma reachable_induct_predicate:
  assumes s: "s \<in> states m"
      and base: "\<forall>s \<in> init m. P s"
      and step: "\<forall>t \<in> trans m. P (src t) \<longrightarrow> P (dst t)"
  shows "P s"
proof -
  from s have "s \<in> { s . P s}" (is "s \<in> ?S")
  proof (rule reachable_induct_set)
    from base show "init m \<subseteq> ?S" by auto
  next
    from step show "successors m ?S \<subseteq> ?S" by (auto simp: successors_def)
  qed
  thus ?thesis ..
qed

subsection {* Behavior *}

subsubsection {* Internal behavior *}

text {* Two views of behavior are formalized. The first view is the internal behavior, and
corresponds to the set of possible executions. An execution is a sequence of transitions, such
that two consecutive transitions have coincident state. We introduce the abbreviation @{text "Run"}
to name the type for executions: *}

type_synonym ('st, 'ev) Run = "('st, 'ev) Tr list"

text {* The inductive set @{text "runs"}
denotes all possible executions of a given LTS @{text "L"}. There are two base cases, 
corresponding to the empty execution and to executions with a single transition: *}

inductive_set runs :: "('st, 'ev) LTS \<Rightarrow> ('st, 'ev) Run set"  
          for m :: "('st, 'ev) LTS" where
  base: "[] \<in> runs m"
| start: "\<lbrakk> t \<in> trans m; src t \<in> init m \<rbrakk> \<Longrightarrow> [t] \<in> runs m"
| step: "\<lbrakk> t \<in> trans m; ts \<in> runs m; ts \<noteq> []; src t = dst (last ts) \<rbrakk> \<Longrightarrow> ts @ [t] \<in> runs m"

inductive_cases empty_run : "[] \<in> runs m"
inductive_cases one_step_run : "[t] \<in> runs m"
inductive_cases multi_step_run : "ts @ [t] \<in> runs m"

text {* The following lemma states that for any run $ts$ of a LTS $m$, such that $ts$ is not the 
empty run, then the source state of the first transition is an initial state of $m$. *}

lemma "ts \<in> runs m \<Longrightarrow> ts \<noteq> [] \<Longrightarrow> src (hd ts) \<in> init m"
by (induct rule: runs.induct) auto

subsubsection {* External behavior *}

text {* The external, or observable, behavior of a LTS is restricted to the events labeling its 
transitions. We give the name @{text "Trace"} to the type of event lists: *}

type_synonym 'ev Trace = "'ev list"

text {* We define the \emph{trace} of a run to be the sequence of events along that run: *}

definition trace_of_run :: "('st, 'ev) Run \<Rightarrow> 'ev Trace" where
  "trace_of_run ts = map lbl ts"

text {* We then define the \emph{traces} of an LTS from the corresponding runs: *}

definition traces :: "('st, 'ev) LTS \<Rightarrow> 'ev Trace set" where
  "traces m \<equiv> trace_of_run ` (runs m)"

end

